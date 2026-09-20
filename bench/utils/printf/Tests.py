"""Check printf parity for the verified literal, escape, and string-format subset."""

import fcntl
import tempfile
from pathlib import Path

import pytest

from tools.bench.bench_test_support import (
    assert_requested_message_behavior,
    assert_result_matches_reference,
    bench_dll_path,
    build_bench_utility,
    build_coreutils_utility,
    coreutils_binary_path,
    evaluation_target_root,
    latest_bench_utility_source_mtime,
    parity_env,
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])

BENCH_PRINTF_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "printf_bench.dll")
COREUTILS_PRINTF = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "printf")
PRINTF_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "printf" / "PrintfCore.dfy",
    ROOT / "bench" / "utils" / "printf" / "PrintfProof.dfy",
    ROOT / "bench" / "utils" / "printf" / "Printf.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_printf_once(request: pytest.FixtureRequest) -> None:
    # Source verification needs no candidate or GNU executable build.
    if request.session.items and all(
        item.get_closest_marker("dafny_verify") for item in request.session.items
    ):
        return
    lock_path = ROOT / "_build" / "bench" / ".build_bench_lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("w", encoding="utf-8") as lock_file:
        fcntl.flock(lock_file, fcntl.LOCK_EX)
        if (
            not BENCH_PRINTF_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "printf") > BENCH_PRINTF_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "printf")
        if not COREUTILS_PRINTF.exists():
            build_coreutils_utility(ROOT, "printf")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_printf(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_PRINTF_DLL, args, cwd, env=parity_env())


def run_system_printf(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_PRINTF, "printf", args, cwd, env=parity_env())


def verify_printf_module(target: Path) -> None:
    run_dafny_verify(target)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    assert_result_matches_reference(ref_result, bench_result)


@pytest.mark.parametrize(
    "args",
    [
        ["hello"],
        ["line\\nnext\\tindent\\\\slash"],
        ["octal:\\0101\\0042"],
    ],
)
def test_literal_and_escape_formats_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/printf/printf.sh
    # upstream: coreutils/tests/printf/printf-cov.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printf(args, cwd)
        bench = run_bench_printf(args, cwd)
        assert_same_result(ref, bench)


def test_literal_format_ignores_extra_arguments_with_warning() -> None:
    # upstream: coreutils/tests/printf/printf.sh
    # upstream: coreutils/tests/printf/printf-cov.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printf(["hello", "ignored"], cwd)
        bench = run_bench_printf(["hello", "ignored"], cwd)
        assert_result_matches_reference(ref, bench, stderr_mode="presence")


@pytest.mark.parametrize(
    "args",
    [
        ["%s:%s\\n", "left", "right"],
        ["<%s><%s>", "one"],
        ["%s,", "a", "b", "c"],
        ["%%:%s", "value"],
    ],
)
def test_string_directives_and_repetition_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/printf/printf.sh
    # upstream: coreutils/tests/printf/printf-cov.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printf(args, cwd)
        bench = run_bench_printf(args, cwd)
        assert_same_result(ref, bench)


def test_missing_format_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/printf/printf.sh
    # upstream: coreutils/tests/printf/printf-cov.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printf([], cwd)
        bench = run_bench_printf([], cwd)
        assert_same_result(ref, bench)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_printf(args, cwd)
            bench = run_bench_printf(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize(
    "args",
    [["--help", "--version"], ["--version", "--version"]],
)
def test_requested_message_excess_argument_warning_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printf(args, cwd)
        bench = run_bench_printf(args, cwd)
        assert_result_matches_reference(ref, bench, stdout_mode="presence", stderr_mode="presence")


def test_deferred_printf_regressions_placeholder() -> None:
    # Not ported yet: the benchmarked printf intentionally covers only the
    # literal, escape, and `%s` subset, so numeric, indexed, multibyte, shell-
    # quoted, and stat-format surfaces remain outside the modeled behavior.
    # upstream: coreutils/tests/printf/printf-hex.sh
    # upstream: coreutils/tests/printf/printf-indexed.sh
    # upstream: coreutils/tests/printf/printf-mb.sh
    # upstream: coreutils/tests/printf/printf-surprise.sh
    # upstream: coreutils/tests/printf/printf-quote.sh
    # upstream: coreutils/tests/stat/stat-printf.pl
    pytest.skip("covers only the verified literal-and-string printf subset")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", PRINTF_VERIFY_TARGETS, ids=lambda path: path.name)
def test_printf_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_printf_module(target)
