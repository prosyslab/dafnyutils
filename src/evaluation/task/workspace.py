"""Construct public task files and checkers, then materialize editable workspaces."""

from __future__ import annotations

import shlex
from dataclasses import dataclass
from pathlib import Path
from string import Template

from analysis.models import DefinitionInfo
from benchmarks.contracts import analyze_task_entry_contract
from benchmarks.paths import REPO_ROOT
from benchmarks.profiles import (
    ResolvedBenchmark,
    is_algorithm_utility,
    utility_paths,
)
from benchmarks.task import TaskProfile, TaskResourceKind
from entry_contract import EntryContractAnalysis
from evaluation.outputs import write_workspace_baseline
from evaluation.runtime import DAFNY_VERIFY_DOTNET_HEAP_LIMIT
from evaluation.task.preparation import PreparedTask, TaskInputLayout
from evaluation.task.specification_source import (
    PLACEHOLDER_FILE_CONTENT,
    filtered_specification_source,
    module_placeholder,
)
from runtime.filesystem import copy_entry, copy_tree_within_root, path_within_root, remove_entry

EVALUATOR_ONLY_UTILITY_FILENAMES = ("Tests.dfy", "Tests.py", "Makefile")


class _ShellTemplate(Template):
    """Use @ placeholders so Bash variable expansion stays literal."""

    delimiter = "@"


def _shell_template(name: str, values: dict[str, str]) -> str:
    source = Path(__file__).with_name("scripts") / name
    return _ShellTemplate(source.read_text(encoding="utf-8")).substitute(values)


def _run_core_scaffold(source: Path, info: DefinitionInfo) -> str:
    if info.body_start is None:
        raise RuntimeError(f"configured implementation entry has no body: {info.full_name}")
    payload = source.read_bytes()
    scaffold = b"{\n      // entry-contract: implement RunCore\n      assert false;\n    }"
    return (payload[: info.body_start] + scaffold + payload[info.end :]).decode()


@dataclass(frozen=True)
class TaskWorkspaceSpec:
    utility: str
    utility_dir: Path
    copied_paths: tuple[Path, ...]
    task_seed_files: tuple[tuple[Path, Path], ...]
    generated_files: tuple[tuple[Path, str], ...]
    hidden_paths: tuple[Path, ...]
    placeholder_paths: tuple[Path, ...]
    editable_paths: tuple[Path, ...]
    sync_paths: tuple[Path, ...]
    required_output_paths: tuple[Path, ...]
    read_only_paths: tuple[Path, ...] = ()


def _generated_files(
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
    contract_analysis: EntryContractAnalysis,
    public_task_id: str | None = None,
) -> tuple[tuple[Path, str], ...]:
    paths = utility_paths(utility_cfg, utility_name)
    utility_dir = Path(paths["utility_dir"])
    project_config = Path(paths["project_config"])
    manifest = contract_analysis.manifest
    execution_path = Path(manifest.execution_entry.source_path)
    support_dir = Path("eval_support") / public_task_id if public_task_id else Path("eval_support")
    build_args = [
        "build",
        "--output",
        f"_build/bench/{utility_name}_bench.dll",
        project_config.as_posix(),
    ]
    if not is_algorithm_utility(utility_name):
        build_args.append("bench/core/IOExtern.cs")
    script_values = {
        "BUILD_ENVIRONMENT": _shell_template(
            "build_environment.sh", {"DOTNET_HEAP_LIMIT": DAFNY_VERIFY_DOTNET_HEAP_LIMIT}
        ),
        "SCRIPT_PARENT": "../.." if public_task_id is not None else "..",
        "UTILITY_ROOT": shlex.quote(utility_dir.as_posix()),
        "MANIFEST_PATH": shlex.quote((support_dir / "entry_contract.json").as_posix()),
        "RUNTIME_BUILD_ARGS": shlex.join(build_args),
        "FULL_BUILD_ARGS": shlex.join(f"--build-arg={arg}" for arg in build_args),
    }
    symbols_by_source: dict[Path, set[str]] = {}
    for definition in manifest.spec_definitions:
        path = Path(definition.source_path)
        if path.is_relative_to(utility_dir):
            symbols_by_source.setdefault(path, set()).add(definition.symbol)
    seeded_sources = {
        path: filtered_specification_source(
            REPO_ROOT / path,
            contract_analysis.source_document,
            symbols,
        )
        for path, symbols in symbols_by_source.items()
    }
    for path in manifest.support_source_sha256:
        support_path = Path(path)
        seeded_sources[support_path] = (REPO_ROOT / support_path).read_text(encoding="utf-8")
    for source in contract_analysis.utility_sources:
        relative = source.relative_to(REPO_ROOT)
        if relative == execution_path or relative in seeded_sources:
            continue
        seeded_sources[relative] = module_placeholder(source, contract_analysis.source_document)
    return (
        (
            support_dir / "entry_contract.json",
            manifest.model_dump_json(indent=2) + "\n",
        ),
        (
            project_config,
            (REPO_ROOT / project_config).read_text(encoding="utf-8"),
        ),
        *tuple(sorted(seeded_sources.items())),
        (
            execution_path,
            _run_core_scaffold(
                contract_analysis.execution_source,
                contract_analysis.execution,
            ),
        ),
        *(
            (support_dir / name, _shell_template(name, script_values))
            for name in ("build.sh", "check_proof_layout.sh", "verify.sh")
        ),
    )


def task_workspace_spec(
    *,
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
    task: TaskProfile | None = None,
    prepared_task: PreparedTask | None = None,
    public_task_id: str | None = None,
) -> TaskWorkspaceSpec:
    profile = utility_cfg.task_profile
    utility_dir = Path(utility_paths(utility_cfg, utility_name)["utility_dir"])
    copied_paths = tuple(Path(path) for path in profile.support_files)
    if task is None:
        required_output_paths = editable_paths = tuple(
            Path(path) for path in profile.editable_outputs
        )
    else:
        required_output_paths = tuple(
            Path(output.path) for output in task.workspace.required_outputs
        )
        editable_paths = tuple(Path(path) for path in task.workspace.editable_paths)
    sync_paths = editable_paths or required_output_paths
    if prepared_task is not None:
        if prepared_task.profile.task_id != utility_name:
            raise ValueError("prepared task id does not match workspace utility")
        if task is not None and task != prepared_task.profile:
            raise ValueError("workspace task does not match prepared task")
        prepared_task.validate_source_identity(repository_root=REPO_ROOT)
        analysis = prepared_task.entry_analysis
    else:
        analysis = analyze_task_entry_contract(utility_cfg, utility_name)
    writable_files = set(required_output_paths)
    if task is not None:
        writable_files.add(Path(task.dafny.execution_entry.source_path))
    read_only_sources = {
        Path(definition.source_path) for definition in analysis.manifest.spec_definitions
    }
    read_only_sources.update(copied_paths)
    if task is not None:
        read_only_sources.update(
            Path(resource.path)
            for resource in task.resources
            if resource.kind is TaskResourceKind.FORMAL_SPECIFICATION
        )
    hidden_files = (
        ("Makefile",) if is_algorithm_utility(utility_name) else EVALUATOR_ONLY_UTILITY_FILENAMES
    )
    return TaskWorkspaceSpec(
        utility=utility_name,
        utility_dir=utility_dir,
        copied_paths=copied_paths,
        task_seed_files=(),
        generated_files=_generated_files(utility_cfg, utility_name, analysis, public_task_id),
        hidden_paths=tuple(utility_dir / name for name in hidden_files),
        placeholder_paths=tuple(Path(path) for path in profile.placeholder_outputs),
        editable_paths=editable_paths,
        sync_paths=sync_paths,
        required_output_paths=required_output_paths or sync_paths,
        read_only_paths=tuple(sorted(read_only_sources - writable_files)),
    )


@dataclass(frozen=True)
class WorkspaceRoots:
    sandbox_root: Path
    workspace_root: Path
    task_root: Path
    run_root: Path
    oracle_target_root: Path
    candidate_output_root: Path


def _path_at_or_below(path: Path, roots: set[Path]) -> bool:
    return any(path == root or root in path.parents for root in roots)


def workspace_roots(run_dir: Path) -> WorkspaceRoots:
    sandbox_root = run_dir / "sandbox"
    workspace_root = sandbox_root / "workspace"
    return WorkspaceRoots(
        sandbox_root=sandbox_root,
        workspace_root=workspace_root,
        task_root=sandbox_root / "task",
        run_root=sandbox_root / "run",
        oracle_target_root=workspace_root,
        candidate_output_root=sandbox_root / "run" / "candidate_outputs",
    )


def _copy_allowlisted_repo_subset(destination: Path, copied_paths: tuple[Path, ...]) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    for rel_path in copied_paths:
        source = (REPO_ROOT / rel_path).resolve()
        if not path_within_root(source, REPO_ROOT):
            raise RuntimeError(f"workspace seed path escapes repository root: {rel_path}")
        target = destination / rel_path
        if not source.exists():
            raise FileNotFoundError(f"workspace seed path missing: {rel_path}")
        if source.is_dir() and not source.is_symlink():
            copy_tree_within_root(source, target)
        else:
            copy_entry(source, target)


def _remove_workspace_path(workspace_root: Path, rel_path: Path) -> None:
    target = workspace_root / rel_path
    if not path_within_root(target, workspace_root):
        raise RuntimeError(f"workspace path escapes workspace root: {rel_path}")
    remove_entry(target)


def _copy_task_seed_files(
    *,
    workspace_root: Path,
    task_dir: Path,
    task_seed_files: tuple[tuple[Path, Path], ...],
) -> None:
    for workspace_path, task_path in task_seed_files:
        source = (task_dir / task_path).resolve()
        target = workspace_root / workspace_path
        if not path_within_root(source, task_dir):
            raise RuntimeError(f"task seed path escapes task input root: {task_path}")
        if not path_within_root(target, workspace_root):
            raise RuntimeError(f"task seed target escapes workspace root: {workspace_path}")
        if not source.is_file():
            raise FileNotFoundError(f"task seed file missing: {task_path}")
        copy_entry(source, target)


def _copy_task_input_directory(*, source: Path, target: Path) -> None:
    remove_entry(target)
    copy_tree_within_root(source, target)


def _write_generated_files(
    *,
    workspace_root: Path,
    generated_files: tuple[tuple[Path, str], ...],
) -> None:
    for rel_path, content in generated_files:
        target = workspace_root / rel_path
        if not path_within_root(target, workspace_root):
            raise RuntimeError(f"generated file escapes workspace root: {rel_path}")
        target.parent.mkdir(parents=True, exist_ok=True)
        remove_entry(target)
        target.write_text(content, encoding="utf-8")
        if target.suffix == ".sh":
            target.chmod(0o755)
        elif target.name == "dfyconfig.toml":
            target.chmod(0o444)


def _apply_hidden_and_placeholder_paths(
    *,
    workspace_root: Path,
    hidden_paths: tuple[Path, ...],
    placeholder_paths: tuple[Path, ...],
) -> None:
    for rel_path in hidden_paths:
        _remove_workspace_path(workspace_root, rel_path)
    for rel_path in placeholder_paths:
        placeholder = workspace_root / rel_path
        if not path_within_root(placeholder, workspace_root):
            raise RuntimeError(f"placeholder path escapes workspace root: {rel_path}")
        placeholder.parent.mkdir(parents=True, exist_ok=True)
        placeholder.write_text(PLACEHOLDER_FILE_CONTENT, encoding="utf-8")


def materialize_workspace_layout(
    *,
    run_dir: Path,
    task_input_layout: TaskInputLayout,
    task_spec: TaskWorkspaceSpec,
) -> WorkspaceRoots:
    roots = workspace_roots(run_dir)
    _materialize_workspace_roots(
        roots=roots,
        task_input_layout=task_input_layout,
        task_spec=task_spec,
        reset_sandbox=True,
    )
    return roots


def _materialize_workspace_roots(
    *,
    roots: WorkspaceRoots,
    task_input_layout: TaskInputLayout,
    task_spec: TaskWorkspaceSpec,
    reset_sandbox: bool,
) -> None:
    seeded_workspace_paths = {workspace_path for workspace_path, _ in task_spec.task_seed_files}
    if reset_sandbox:
        remove_entry(roots.sandbox_root)
    else:
        remove_entry(roots.workspace_root)
    roots.sandbox_root.mkdir(parents=True, exist_ok=True)
    _copy_allowlisted_repo_subset(roots.workspace_root, task_spec.copied_paths)
    _copy_task_seed_files(
        workspace_root=roots.workspace_root,
        task_dir=task_input_layout.task_dir,
        task_seed_files=task_spec.task_seed_files,
    )
    _apply_hidden_and_placeholder_paths(
        workspace_root=roots.workspace_root,
        hidden_paths=task_spec.hidden_paths,
        placeholder_paths=tuple(
            path for path in task_spec.placeholder_paths if path not in seeded_workspace_paths
        ),
    )
    _write_generated_files(
        workspace_root=roots.workspace_root,
        generated_files=task_spec.generated_files,
    )
    roots.run_root.mkdir(parents=True, exist_ok=True)
    _copy_task_input_directory(
        source=task_input_layout.task_dir,
        target=roots.task_root,
    )
    roots.candidate_output_root.mkdir(parents=True, exist_ok=True)
    write_workspace_baseline(roots, task_spec)


def refresh_workspace_support_files(
    *,
    workspace_root: Path,
    task_input_layout: TaskInputLayout,
    task_spec: TaskWorkspaceSpec,
) -> None:
    candidate_paths = set(task_spec.sync_paths)

    for rel_path in task_spec.copied_paths:
        if _path_at_or_below(rel_path, candidate_paths):
            continue
        source = (REPO_ROOT / rel_path).resolve()
        target = workspace_root / rel_path
        if not path_within_root(source, REPO_ROOT):
            raise RuntimeError(f"workspace support path escapes repository root: {rel_path}")
        if not source.exists():
            raise FileNotFoundError(f"workspace support path missing: {rel_path}")
        if source.is_dir():
            raise IsADirectoryError(f"workspace support path must be a file: {rel_path}")
        remove_entry(target)
        copy_entry(source, target)

    for workspace_path, task_path in task_spec.task_seed_files:
        if _path_at_or_below(workspace_path, candidate_paths):
            continue
        source = (task_input_layout.task_dir / task_path).resolve()
        target = workspace_root / workspace_path
        if not path_within_root(source, task_input_layout.task_dir):
            raise RuntimeError(f"task support path escapes task input root: {task_path}")
        if not source.is_file():
            raise FileNotFoundError(f"task support file missing: {task_path}")
        remove_entry(target)
        copy_entry(source, target)

    _write_generated_files(
        workspace_root=workspace_root,
        generated_files=tuple(
            item
            for item in task_spec.generated_files
            if not _path_at_or_below(item[0], candidate_paths)
        ),
    )
