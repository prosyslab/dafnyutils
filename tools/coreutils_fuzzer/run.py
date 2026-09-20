from __future__ import annotations

import os
import re
import shlex
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, List

import click

DEFAULT_UTILS = ["cat", "touch"]
DEFAULT_REF_TEMPLATE = "_build/coreutils/src/{util}"
DEFAULT_DUT_TEMPLATE = "_build/bench/{util}_bench.dll"
DEFAULT_FUZZ_PROCESS_TIMEOUT_SECONDS = "10"
DEFAULT_CONTAINER_IMAGE = "dafnyutils-coreutils-fuzzer:latest"
FUZZER_OUTCOME_MARKER_PREFIX = "FUZZER_OUTCOME="
FUZZER_BUILD_FAILURE = "fuzzer_build_failure"
FUZZER_TARGET_SPAWN_FAILURE = "fuzzer_target_spawn_failure"
_BUILT_MANIFESTS: set[Path] = set()


@dataclass(frozen=True)
class CommonCommandConfig:
    root_dir: Path
    target_root_dir: Path
    manifest_path: Path
    resolved_utils: list[str]
    iterations: str
    seed: str
    max_args: str
    max_fs_entries: str
    workdir_mode: str
    ref_kind: str
    ref_template: str
    case_set: str | None
    metrics_out: str | None
    container_image: str


def env_or_default(name: str, default: str) -> str:
    return os.environ.get(name) or default


def parse_positive_seconds(value: str, *, source: str) -> int:
    try:
        seconds = int(value)
    except ValueError as exc:
        raise click.UsageError(f"{source} must be a positive integer") from exc
    if seconds < 1:
        raise click.UsageError(f"{source} must be a positive integer")
    return seconds


def resolve_root_dir() -> Path:
    override = os.environ.get("EVAL_REPO_ROOT")
    if override:
        return Path(override).resolve()
    return Path(__file__).resolve().parents[2]


def resolve_target_root_dir(root_dir: Path) -> Path:
    override = os.environ.get("EVAL_TARGET_ROOT")
    return normalize_path(root_dir, override) if override else root_dir


def normalize_path(root_dir: Path, value: str) -> Path:
    path = Path(value)
    if not path.is_absolute():
        path = root_dir / path
    return path


def split_utils(value: str) -> List[str]:
    return [item for item in re.split(r"[,\s]+", value.strip()) if item]


def resolve_fuzz_seed_values(seeds_opt: str | None, fallback_seed: str) -> List[str]:
    raw = seeds_opt if seeds_opt is not None else os.environ.get("FUZZ_SEEDS")
    if raw is None or raw == "":
        return [fallback_seed]
    seeds = split_utils(raw)
    if not seeds:
        raise click.UsageError("fuzz seeds must include at least one integer seed")
    for seed_value in seeds:
        try:
            parsed = int(seed_value)
        except ValueError as exc:
            raise click.UsageError("fuzz seeds must be integer values") from exc
        if parsed < 0:
            raise click.UsageError("fuzz seeds must be non-negative integer values")
    return seeds


def unique_in_order(items: Iterable[str]) -> List[str]:
    seen = set()
    result = []
    for item in items:
        if not item or item in seen:
            continue
        seen.add(item)
        result.append(item)
    return result


def canonical_coreutils_task_ids(root_dir: Path) -> set[str]:
    task_ids: set[str] = set()
    for definition_path in (root_dir / "bench" / "utils").glob("*/benchmark.yaml"):
        directory_id = definition_path.parent.name
        try:
            lines = definition_path.read_text(encoding="utf-8").splitlines()
        except OSError as exc:
            raise click.ClickException(
                f"failed to read benchmark definition {definition_path}: {exc}"
            ) from exc
        task_id_lines = [line for line in lines if line.startswith("task_id:")]
        if len(task_id_lines) != 1:
            raise click.ClickException(
                f"benchmark definition {definition_path} must contain exactly one task_id"
            )
        task_id = task_id_lines[0].split(":", 1)[1].split("#", 1)[0].strip().strip("'\"")
        if task_id != directory_id:
            raise click.ClickException(
                f"benchmark definition {definition_path} has non-canonical task_id {task_id!r}"
            )
        kind_lines = [line for line in lines if line.startswith("kind:")]
        if len(kind_lines) != 1:
            raise click.ClickException(
                f"benchmark definition {definition_path} must contain exactly one kind"
            )
        kind = kind_lines[0].split(":", 1)[1].split("#", 1)[0].strip().strip("'\"")
        if kind != "coreutils":
            raise click.ClickException(
                f"benchmark definition {definition_path} has non-coreutils kind {kind!r}"
            )
        task_ids.add(task_id)
    return task_ids


def collect_all_built_utils(root_dir: Path, definition_root_dir: Path | None = None) -> List[str]:
    build_dir = root_dir / "_build" / "bench"
    if not build_dir.is_dir():
        return []
    known_utils = canonical_coreutils_task_ids(definition_root_dir or root_dir)
    utils = {
        path.name.removesuffix("_bench.dll")
        for path in build_dir.glob("*_bench.dll")
        if path.is_file()
        and path.name.endswith("_bench.dll")
        and path.name.removesuffix("_bench.dll") in known_utils
    }
    return sorted(utils)


def resolve_bin_path(root_dir: Path, util: str, template: str) -> Path:
    return normalize_path(root_dir, template.replace("{util}", util))


def require_target_artifact(path: Path, *, label: str, kind: str) -> None:
    valid = path.is_file() and (kind != "native" or os.access(path, os.X_OK))
    if valid:
        return
    _exit_with_fuzzer_failure(
        command=["target-preflight", label, str(path)],
        returncode=127,
        output=f"missing or unusable {label} target `{path}`",
        outcome=FUZZER_TARGET_SPAWN_FAILURE,
    )


def resolve_utils(
    root_dir: Path,
    custom_utils: Iterable[str],
    utils_opt: str | None,
    all_built: bool,
    *,
    build_root_dir: Path | None = None,
) -> List[str]:
    if custom_utils:
        selected = list(custom_utils)
    elif all_built:
        selected = collect_all_built_utils(build_root_dir or root_dir, root_dir)
    elif utils_opt:
        selected = split_utils(utils_opt)
    elif os.environ.get("FUZZ_UTILS"):
        selected = split_utils(os.environ["FUZZ_UTILS"])
    else:
        selected = DEFAULT_UTILS

    resolved = unique_in_order(selected)
    if not resolved:
        raise click.UsageError(
            "no utilities selected\nhint: pass utility names, set FUZZ_UTILS, or use --all-built"
        )
    known_utils = canonical_coreutils_task_ids(root_dir)
    unknown = [util for util in resolved if util not in known_utils]
    if unknown:
        raise click.UsageError(
            "unknown coreutils benchmark task id(s): "
            + ", ".join(unknown)
            + "\nhint: use canonical task IDs from bench/utils/*/benchmark.yaml"
        )
    return resolved


def _cargo_env() -> dict[str, str]:
    return os.environ.copy()


def _run_cargo_command(command: list[str], env: dict[str, str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )


def _exit_with_fuzzer_failure(
    *, command: list[str], returncode: int, output: str, outcome: str
) -> None:
    click.echo(f"{FUZZER_OUTCOME_MARKER_PREFIX}{outcome}", err=True)
    click.echo(f"fuzzer command: {shlex.join(command)}", err=True)
    click.echo(f"fuzzer return code: {returncode}", err=True)
    if output:
        click.echo(output, err=True, nl=not output.endswith("\n"))
    sys.exit(returncode)


def _ensure_cargo_built(manifest_path: Path, env: dict[str, str]) -> None:
    resolved_manifest = manifest_path.resolve()
    if resolved_manifest in _BUILT_MANIFESTS:
        return
    command = ["cargo", "build", "--manifest-path", str(manifest_path)]
    result = _run_cargo_command(command, env)
    if result.returncode != 0:
        _exit_with_fuzzer_failure(
            command=command,
            returncode=result.returncode,
            output=result.stdout or "",
            outcome=FUZZER_BUILD_FAILURE,
        )
    _BUILT_MANIFESTS.add(resolved_manifest)


def run_cargo(
    manifest_path: Path, args: List[str], captured_output: list[str] | None = None
) -> list[str]:
    return run_fuzzer_binary(manifest_path, args, captured_output)


def run_fuzzer_binary(
    manifest_path: Path, args: List[str], captured_output: list[str] | None = None
) -> list[str]:
    env = _cargo_env()
    _ensure_cargo_built(manifest_path, env)
    target_dir = Path(env.get("CARGO_TARGET_DIR", manifest_path.parent / "target"))
    executable = (
        target_dir / "debug" / ("coreutils_fuzzer.exe" if os.name == "nt" else "coreutils_fuzzer")
    )
    command = [str(executable), *args]
    result = _run_cargo_command(command, env)
    output = result.stdout or ""
    if captured_output is not None:
        captured_output.append(output)
    click.echo(output, nl=False)
    if result.returncode != 0:
        _exit_with_fuzzer_failure(
            command=command,
            returncode=result.returncode,
            output="" if output.endswith("\n") else output,
            outcome=(
                FUZZER_BUILD_FAILURE
                if FUZZER_OUTCOME_MARKER_PREFIX not in output
                else _fuzzer_outcome_from_output(output)
            ),
        )
    return command


def _fuzzer_outcome_from_output(output: str) -> str:
    for line in output.splitlines():
        if line.startswith(FUZZER_OUTCOME_MARKER_PREFIX):
            return line.removeprefix(FUZZER_OUTCOME_MARKER_PREFIX)
    return FUZZER_BUILD_FAILURE


def utility_selection_options(command: Callable) -> Callable:
    decorators = [
        click.option("--all-built", is_flag=True, help="Use all built utilities from _build."),
        click.option(
            "--utils",
            help="Utility list (comma/space separated). Ignored when positional args exist.",
        ),
        click.argument("utils_pos", nargs=-1, metavar="[UTIL]..."),
    ]
    for decorator in reversed(decorators):
        command = decorator(command)
    return command


def common_campaign_options(command: Callable) -> Callable:
    decorators = [
        click.option(
            "--iterations",
            type=int,
            default=None,
            help="Iterations per utility (default: 200)",
        ),
        click.option("--seed", type=int, default=None, help="RNG seed (default: 1)"),
        click.option(
            "--max-args",
            type=int,
            default=None,
            help="Max args per case (default: 10)",
        ),
        click.option(
            "--max-fs-entries", type=int, default=None, help="Max fs entries (default: 12)"
        ),
        click.option("--workdir-mode", default=None, help="per-iteration | shared"),
        click.option("--ref-kind", default=None, help="native | dotnet-dll (default: native)"),
        click.option(
            "--case-set",
            type=click.Path(path_type=Path, dir_okay=False),
            default=None,
            help="Versioned explicit case set. Use {util} when selecting several utilities.",
        ),
        click.option(
            "--metrics-out",
            type=click.Path(path_type=Path, dir_okay=False),
            default=None,
            help="Write versioned JSON metrics. Multi-run paths receive utility/seed suffixes.",
        ),
        click.option(
            "--container-image",
            default=DEFAULT_CONTAINER_IMAGE,
            show_default=True,
            help="Image for the owned disposable fuzz container.",
        ),
    ]
    for decorator in reversed(decorators):
        command = decorator(command)
    return command


def resolve_common_command_config(
    *,
    all_built: bool,
    utils: str | None,
    utils_pos: tuple[str, ...],
    iterations: int | None,
    seed: int | None,
    max_args: int | None,
    max_fs_entries: int | None,
    workdir_mode: str | None,
    ref_kind: str | None,
    case_set: Path | None,
    metrics_out: Path | None,
    container_image: str,
) -> CommonCommandConfig:
    if iterations is not None and iterations < 1:
        raise click.UsageError("iterations must be a positive integer")
    if iterations is None and int(env_or_default("ITERATIONS", "200")) < 1:
        raise click.UsageError("iterations must be a positive integer")
    root_dir = resolve_root_dir()
    target_root_dir = resolve_target_root_dir(root_dir)
    manifest_path = root_dir / "tools" / "coreutils_fuzzer" / "Cargo.toml"
    resolved_utils = resolve_utils(
        root_dir,
        utils_pos,
        utils,
        all_built,
        build_root_dir=target_root_dir,
    )
    if not container_image.strip():
        raise click.UsageError("container image must not be empty")
    return CommonCommandConfig(
        root_dir=root_dir,
        target_root_dir=target_root_dir,
        manifest_path=manifest_path,
        resolved_utils=resolved_utils,
        iterations=(
            str(iterations) if iterations is not None else env_or_default("ITERATIONS", "200")
        ),
        seed=str(seed) if seed is not None else env_or_default("SEED", "1"),
        max_args=str(max_args) if max_args is not None else env_or_default("MAX_ARGS", "10"),
        max_fs_entries=(
            str(max_fs_entries)
            if max_fs_entries is not None
            else env_or_default("MAX_FS_ENTRIES", "12")
        ),
        workdir_mode=workdir_mode or env_or_default("WORKDIR_MODE", "per-iteration"),
        ref_kind=ref_kind or env_or_default("REF_KIND", "native"),
        ref_template=env_or_default("REF_BIN_TEMPLATE", DEFAULT_REF_TEMPLATE),
        case_set=str(case_set) if case_set is not None else None,
        metrics_out=str(metrics_out) if metrics_out is not None else None,
        container_image=container_image,
    )


def resolve_case_set_path(root_dir: Path, template: str | None, util: str) -> Path | None:
    if template is None:
        return None
    path = normalize_path(root_dir, template.replace("{util}", util))
    if not path.is_file():
        raise click.UsageError(f"case set does not exist or is not a file: {path}")
    return path


def resolve_metrics_output_path(
    root_dir: Path,
    template: str | None,
    util: str,
    seed: str,
    *,
    multiple_utils: bool,
    multiple_seeds: bool,
) -> Path | None:
    if template is None:
        return None
    rendered = template.replace("{util}", util).replace("{seed}", seed)
    path = normalize_path(root_dir, rendered)
    suffix_parts = []
    if multiple_utils and "{util}" not in template:
        suffix_parts.append(util)
    if multiple_seeds and "{seed}" not in template:
        suffix_parts.append(f"seed{seed}")
    if not suffix_parts:
        return path
    suffix = path.suffix or ".json"
    stem = path.name[: -len(path.suffix)] if path.suffix else path.name
    return path.with_name(f"{stem}-{'-'.join(suffix_parts)}{suffix}")


@click.group(context_settings={"help_option_names": ["-h", "--help"]})
def cli() -> None:
    """Run parity fuzzing and related benchmark checks."""


@cli.command("fuzz")
@utility_selection_options
@common_campaign_options
@click.option(
    "--seeds",
    default=None,
    help="Comma/space separated RNG seeds. Overrides --seed and FUZZ_SEEDS when set.",
)
@click.option("--dut-kind", default=None, help="native | dotnet-dll (default: dotnet-dll)")
@click.option(
    "--shrink-attempts",
    type=int,
    default=None,
    help="Mismatch shrink attempts (default: 250, 0 disables shrinking)",
)
@click.option(
    "--process-timeout-seconds",
    type=int,
    default=None,
    help="Per reference/DUT subprocess timeout (default: 10; env FUZZ_PROCESS_TIMEOUT_SECONDS)",
)
@click.option(
    "--ignore-stderr",
    is_flag=True,
    help="Ignore stderr differences while still checking exit code, stdout, and filesystem.",
)
def fuzz(
    all_built: bool,
    utils: str | None,
    utils_pos: tuple[str, ...],
    iterations: int | None,
    seed: int | None,
    max_args: int | None,
    max_fs_entries: int | None,
    workdir_mode: str | None,
    ref_kind: str | None,
    case_set: Path | None,
    metrics_out: Path | None,
    container_image: str,
    seeds: str | None,
    dut_kind: str | None,
    shrink_attempts: int | None,
    process_timeout_seconds: int | None,
    ignore_stderr: bool,
) -> None:
    config = resolve_common_command_config(
        all_built=all_built,
        utils=utils,
        utils_pos=utils_pos,
        iterations=iterations,
        seed=seed,
        max_args=max_args,
        max_fs_entries=max_fs_entries,
        workdir_mode=workdir_mode,
        ref_kind=ref_kind,
        case_set=case_set,
        metrics_out=metrics_out,
        container_image=container_image,
    )
    dut_kind_val = dut_kind or env_or_default("DUT_KIND", "dotnet-dll")
    dut_template = env_or_default("DUT_BIN_TEMPLATE", DEFAULT_DUT_TEMPLATE)
    shrink_attempts_val = (
        str(shrink_attempts)
        if shrink_attempts is not None
        else env_or_default("SHRINK_ATTEMPTS", "250")
    )
    process_timeout_seconds_val = (
        str(process_timeout_seconds)
        if process_timeout_seconds is not None
        else env_or_default("FUZZ_PROCESS_TIMEOUT_SECONDS", DEFAULT_FUZZ_PROCESS_TIMEOUT_SECONDS)
    )
    parse_positive_seconds(
        process_timeout_seconds_val,
        source="fuzz process timeout",
    )
    seed_values = resolve_fuzz_seed_values(seeds, config.seed)

    click.echo(f"selected utilities: {' '.join(config.resolved_utils)}")
    multiple_utils = len(config.resolved_utils) > 1
    multiple_seeds = len(seed_values) > 1
    for util in config.resolved_utils:
        click.echo(f"==> utility: {util}")
        ref_bin = resolve_bin_path(config.root_dir, util, config.ref_template)
        dut_bin = resolve_bin_path(config.target_root_dir, util, dut_template)
        require_target_artifact(ref_bin, label="reference", kind=config.ref_kind)
        require_target_artifact(dut_bin, label="DUT", kind=dut_kind_val)
        for seed_value in seed_values:
            if len(seed_values) > 1:
                click.echo(f"    seed: {seed_value}")
            fuzzer_args = [
                "fuzz",
                "--util",
                util,
                "--ref-kind",
                config.ref_kind,
                "--dut-kind",
                dut_kind_val,
                "--iterations",
                config.iterations,
                "--seed",
                seed_value,
                "--max-args",
                config.max_args,
                "--max-fs-entries",
                config.max_fs_entries,
                "--workdir-mode",
                config.workdir_mode,
                "--ref-bin",
                str(ref_bin),
                "--dut-bin",
                str(dut_bin),
                "--shrink-attempts",
                shrink_attempts_val,
                "--process-timeout-seconds",
                process_timeout_seconds_val,
                "--container-image",
                config.container_image,
            ]
            if ignore_stderr:
                fuzzer_args.append("--ignore-stderr")
            case_set_path = resolve_case_set_path(config.root_dir, config.case_set, util)
            if case_set_path is not None:
                fuzzer_args.extend(["--case-set", str(case_set_path)])
            metrics_path = resolve_metrics_output_path(
                config.root_dir,
                config.metrics_out,
                util,
                seed_value,
                multiple_utils=multiple_utils,
                multiple_seeds=multiple_seeds,
            )
            if metrics_path is not None:
                fuzzer_args.extend(["--metrics-out", str(metrics_path)])
            run_cargo(config.manifest_path, fuzzer_args)


@cli.command("capabilities")
@click.option(
    "--format",
    "output_format",
    type=click.Choice(["text", "json"]),
    default="text",
    show_default=True,
)
def capabilities(output_format: str) -> None:
    """List registered parity-fuzz capabilities."""
    root_dir = resolve_root_dir()
    run_fuzzer_binary(
        root_dir / "tools" / "coreutils_fuzzer" / "Cargo.toml",
        ["capabilities", "--format", output_format],
    )


@cli.command("replay")
@click.argument(
    "repro_bundle",
    type=click.Path(path_type=Path, exists=True, file_okay=False, dir_okay=True),
)
@click.option("--ref-bin", type=click.Path(path_type=Path), default=None)
@click.option("--dut-bin", type=click.Path(path_type=Path), default=None)
@click.option("--ref-kind", type=click.Choice(["native", "dotnet-dll"]), default=None)
@click.option("--dut-kind", type=click.Choice(["native", "dotnet-dll"]), default=None)
@click.option("--process-timeout-seconds", type=int, default=None)
@click.option("--container-image", default=None)
def replay(
    repro_bundle: Path,
    ref_bin: Path | None,
    dut_bin: Path | None,
    ref_kind: str | None,
    dut_kind: str | None,
    process_timeout_seconds: int | None,
    container_image: str | None,
) -> None:
    """Replay an exact saved mismatch case through the normal comparator."""
    if process_timeout_seconds is not None and process_timeout_seconds < 1:
        raise click.UsageError("replay process timeout must be a positive integer")
    root_dir = resolve_root_dir()
    args = [
        "replay",
        "--repro",
        str(repro_bundle.resolve()),
    ]
    for option, value in (
        ("--ref-bin", ref_bin),
        ("--dut-bin", dut_bin),
        ("--ref-kind", ref_kind),
        ("--dut-kind", dut_kind),
        ("--process-timeout-seconds", process_timeout_seconds),
        ("--container-image", container_image),
    ):
        if value is not None:
            args.extend([option, str(value)])
    run_cargo(root_dir / "tools" / "coreutils_fuzzer" / "Cargo.toml", args)


@cli.command("regression")
@click.argument(
    "suite",
    type=click.Path(path_type=Path, exists=True, file_okay=True, dir_okay=False),
)
@click.option("--ref-bin", type=click.Path(path_type=Path), default=None)
@click.option("--dut-bin", type=click.Path(path_type=Path), default=None)
@click.option("--ref-kind", type=click.Choice(["native", "dotnet-dll"]), default="native")
@click.option("--dut-kind", type=click.Choice(["native", "dotnet-dll"]), default="dotnet-dll")
@click.option("--process-timeout-seconds", type=int, default=None)
@click.option("--ignore-stderr", is_flag=True)
@click.option("--metrics-out", type=click.Path(path_type=Path, dir_okay=False), default=None)
@click.option("--container-image", default=DEFAULT_CONTAINER_IMAGE, show_default=True)
def regression(
    suite: Path,
    ref_bin: Path | None,
    dut_bin: Path | None,
    ref_kind: str,
    dut_kind: str,
    process_timeout_seconds: int | None,
    ignore_stderr: bool,
    metrics_out: Path | None,
    container_image: str,
) -> None:
    """Run versioned fixed-behavior expectations without changing replay semantics."""
    if process_timeout_seconds is not None and process_timeout_seconds < 1:
        raise click.UsageError("regression process timeout must be a positive integer")
    root_dir = resolve_root_dir()
    args = [
        "regression",
        "--suite",
        str(suite.resolve()),
        "--ref-kind",
        ref_kind,
        "--dut-kind",
        dut_kind,
        "--container-image",
        container_image,
    ]
    for option, value in (
        ("--ref-bin", ref_bin),
        ("--dut-bin", dut_bin),
        ("--process-timeout-seconds", process_timeout_seconds),
        ("--metrics-out", metrics_out),
    ):
        if value is not None:
            args.extend([option, str(value)])
    if ignore_stderr:
        args.append("--ignore-stderr")
    run_fuzzer_binary(root_dir / "tools" / "coreutils_fuzzer" / "Cargo.toml", args)


def dispatch(argv: list[str] | None = None, *, standalone_mode: bool = True) -> object:
    args = list(sys.argv[1:] if argv is None else argv)
    return cli.main(
        args=args,
        prog_name=Path(__file__).name,
        standalone_mode=standalone_mode,
    )


if __name__ == "__main__":
    dispatch()
