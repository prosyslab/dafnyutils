"""Check csplit numeric split parity and verify its Dafny proof surface."""

from __future__ import annotations

import fcntl
import re
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
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])

BENCH_CSPLIT_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "csplit_bench.dll")
COREUTILS_CSPLIT = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "csplit")
CSPLIT_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "csplit" / "CsplitSchema.dfy",
    ROOT / "bench" / "utils" / "csplit" / "CsplitCore.dfy",
    ROOT / "bench" / "utils" / "csplit" / "CsplitSpec.dfy",
    ROOT / "bench" / "utils" / "csplit" / "CsplitProof.dfy",
    ROOT / "bench" / "utils" / "csplit" / "Csplit.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_csplit_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_CSPLIT_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "csplit") > BENCH_CSPLIT_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "csplit")
        if not COREUTILS_CSPLIT.exists():
            build_coreutils_utility(ROOT, "csplit")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_csplit(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_CSPLIT_DLL, args, cwd, input_data=input_data)


def run_system_csplit(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_CSPLIT, "csplit", args, cwd, input_data=input_data)


def write_inputs(cwd: Path, files: dict[str, bytes]) -> None:
    for name, data in files.items():
        path = cwd / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)


def generated_regular_files(cwd: Path) -> dict[str, bytes]:
    return {path.name: path.read_bytes() for path in sorted(cwd.glob("xx*")) if path.is_file()}


def normalize_csplit_stderr(stderr: bytes) -> bytes:
    text = stderr.decode("latin1")
    text = re.sub(
        r"Try '.*csplit --help' for more information\.\n",
        "Try 'csplit --help' for more information.\n",
        text,
    )
    return text.encode("latin1")


def assert_csplit_parity(
    args: list[str],
    *,
    files: dict[str, bytes] | None = None,
    input_data: bytes = b"",
    ignore_stderr_when_exit_nonzero: bool = True,
) -> None:
    with tempfile.TemporaryDirectory() as ref_dir, tempfile.TemporaryDirectory() as bench_dir:
        ref_cwd = Path(ref_dir)
        bench_cwd = Path(bench_dir)
        write_inputs(ref_cwd, files or {})
        write_inputs(bench_cwd, files or {})

        ref = run_system_csplit(args, ref_cwd, input_data=input_data)
        bench = run_bench_csplit(args, bench_cwd, input_data=input_data)

        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=ignore_stderr_when_exit_nonzero,
            stderr_normalizer=normalize_csplit_stderr,
        )
        assert generated_regular_files(bench_cwd) == generated_regular_files(ref_cwd)


def test_numeric_line_patterns_write_default_files() -> None:
    # upstream: coreutils/tests/csplit/csplit.sh
    assert_csplit_parity(
        ["input.txt", "2", "3"],
        files={"input.txt": b"a\nb\nc\n"},
    )


def test_stdin_numeric_pattern_writes_default_files() -> None:
    # upstream: coreutils/tests/csplit/csplit.sh
    assert_csplit_parity(["-", "2"], input_data=b"a\nb\n")


def test_stdin_out_of_range_pattern_reports_written_empty_piece() -> None:
    # Source: fuzzer regression for numeric stdin split past end-of-input.
    # upstream: coreutils/tests/csplit/csplit.sh
    assert_csplit_parity(["-", "3"], input_data=b"")


def test_repeated_line_number_warning_and_empty_piece_match_coreutils() -> None:
    # upstream: coreutils/tests/csplit/csplit.sh
    assert_csplit_parity(
        ["input.txt", "1", "1"],
        files={"input.txt": b"a\nb\n"},
        ignore_stderr_when_exit_nonzero=False,
    )


# Fuzzer regression: duplicate diagnostics emitted before a later zero must be preserved.
def test_duplicate_warning_precedes_later_zero_error() -> None:
    # upstream: none - repository-local GNU parity regression
    assert_csplit_parity(
        ["input.txt", "2", "2", "0"],
        files={"input.txt": b"a\nb\nc\n"},
        ignore_stderr_when_exit_nonzero=False,
    )


# Fuzzer regression: duplicate diagnostics emitted before a later decrease must be preserved.
def test_duplicate_warning_precedes_later_backward_error() -> None:
    # upstream: none - repository-local GNU parity regression
    assert_csplit_parity(
        ["input.txt", "2", "2", "1"],
        files={"input.txt": b"a\nb\nc\n"},
        ignore_stderr_when_exit_nonzero=False,
    )


def test_existing_output_directory_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/csplit/csplit.sh
    with tempfile.TemporaryDirectory() as ref_dir, tempfile.TemporaryDirectory() as bench_dir:
        ref_cwd = Path(ref_dir)
        bench_cwd = Path(bench_dir)
        write_inputs(ref_cwd, {"input.txt": b"a\nb\n"})
        write_inputs(bench_cwd, {"input.txt": b"a\nb\n"})
        (ref_cwd / "xx00").mkdir()
        (bench_cwd / "xx00").mkdir()

        ref = run_system_csplit(["input.txt", "2"], ref_cwd)
        bench = run_bench_csplit(["input.txt", "2"], bench_cwd)

        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
            stderr_normalizer=normalize_csplit_stderr,
        )


def test_later_write_failure_removes_created_outputs_match_coreutils() -> None:
    # upstream: coreutils/tests/csplit/csplit.sh
    with tempfile.TemporaryDirectory() as ref_dir, tempfile.TemporaryDirectory() as bench_dir:
        ref_cwd = Path(ref_dir)
        bench_cwd = Path(bench_dir)
        write_inputs(ref_cwd, {"input.txt": b"a\nb\nc\n"})
        write_inputs(bench_cwd, {"input.txt": b"a\nb\nc\n"})
        (ref_cwd / "xx01").mkdir()
        (bench_cwd / "xx01").mkdir()

        ref = run_system_csplit(["input.txt", "2", "3"], ref_cwd)
        bench = run_bench_csplit(["input.txt", "2", "3"], bench_cwd)

        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
            stderr_normalizer=normalize_csplit_stderr,
        )
        assert not (bench_cwd / "xx00").exists()
        assert (bench_cwd / "xx01").is_dir()


@pytest.mark.parametrize("args", [["input.txt", "0"], ["input.txt", "2", "1"]])
def test_numeric_pattern_diagnostics_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/csplit/csplit.sh
    assert_csplit_parity(
        args,
        files={"input.txt": b"a\nb\n"},
        ignore_stderr_when_exit_nonzero=False,
    )


def test_missing_input_file_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/csplit/csplit.sh
    assert_csplit_parity(["missing.txt", "1"], ignore_stderr_when_exit_nonzero=False)


# Fuzzer regression: GNU opens a named input before rejecting decreasing numeric patterns.
def test_missing_input_precedes_backward_numeric_pattern() -> None:
    # upstream: none - repository-local GNU parity regression
    assert_csplit_parity(["3", "4", "1"], ignore_stderr_when_exit_nonzero=False)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_csplit(args, cwd)
            bench = run_bench_csplit(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize("args", [["--prefix", "yy", "input.txt", "1"], ["input.txt", "/a/"]])
def test_deferred_surface_reports_benchmark_diagnostic(args: list[str]) -> None:
    # upstream: none - Checks this benchmark slice's unsupported-pattern diagnostic rather than GNU
    # upstream-reason: parity.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_inputs(cwd, {"input.txt": b"a\n"})
        stdout, stderr, exit_code = run_bench_csplit(args, cwd)

    assert exit_code == 1
    assert stdout == b""
    assert b"not supported by this benchmark slice" in stderr


def test_deferred_csplit_regressions_placeholder() -> None:
    # Not ported yet: regex contexts, repeat counts, custom suffix formats,
    # and GNU's remove-created-files-on-error behavior are outside this slice.
    # Not ported yet: --suppress-matched and regex paragraph splitting are
    # deferred until regex contexts are modeled.
    # Not ported yet: streaming/memory-limit, many-piece stress, and long-line
    # buffer regression coverage are beyond the current numeric split slice.
    # Not ported yet: /dev/full cleanup semantics depend on device-backed
    # write failures and GNU's remove-on-error policy.
    # upstream: coreutils/tests/csplit/csplit.sh
    # upstream: coreutils/tests/csplit/csplit-suppress-matched.pl
    # upstream: coreutils/tests/csplit/csplit-heap.sh
    # upstream: coreutils/tests/csplit/csplit-1000.sh
    # upstream: coreutils/tests/csplit/csplit-io-err.sh
    pytest.skip("requires deferred csplit pattern, cleanup, or stress behavior")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", CSPLIT_VERIFY_TARGETS, ids=lambda path: path.name)
def test_csplit_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
