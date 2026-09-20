"""Check comm sorted-file parity against GNU coreutils and verify proof surface."""

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
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])

BENCH_COMM_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "comm_bench.dll")
COREUTILS_COMM = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "comm")
COMM_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "comm" / "CommSchema.dfy",
    ROOT / "bench" / "utils" / "comm" / "CommCore.dfy",
    ROOT / "bench" / "utils" / "comm" / "CommSpec.dfy",
    ROOT / "bench" / "utils" / "comm" / "CommProof.dfy",
    ROOT / "bench" / "utils" / "comm" / "Comm.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_comm_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_COMM_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "comm") > BENCH_COMM_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "comm")
        if not COREUTILS_COMM.exists():
            build_coreutils_utility(ROOT, "comm")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_comm(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_COMM_DLL, args, cwd, input_data=input_data)


def run_system_comm(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_COMM, "comm", args, cwd, input_data=input_data)


def assert_comm_parity(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
    check_stderr: bool = True,
) -> None:
    ref = run_system_comm(args, cwd, input_data=input_data)
    bench = run_bench_comm(args, cwd, input_data=input_data)
    assert_result_matches_reference(
        ref,
        bench,
        ignore_stderr_when_exit_nonzero=not check_stderr,
    )


def write_comm_inputs(cwd: Path) -> None:
    _ = (cwd / "a").write_bytes(b"1\n3\n3\n3")
    _ = (cwd / "b").write_bytes(b"2\n2\n3\n3\n3")


def write_comm_nul_inputs(cwd: Path) -> None:
    _ = (cwd / "za").write_bytes(b"1\0003\0003\0003")
    _ = (cwd / "zb").write_bytes(b"2\0002\0003\0003\0003")


def test_default_three_columns_match_coreutils() -> None:
    # upstream: coreutils/tests/misc/comm.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_comm_inputs(cwd)

        assert_comm_parity(["a", "b"], cwd)


@pytest.mark.parametrize(
    "args",
    [
        ["-1", "a", "b"],
        ["-2", "a", "b"],
        ["-3", "a", "b"],
        ["-1", "-2", "a", "b"],
        ["-1", "-3", "a", "b"],
        ["-2", "-3", "a", "b"],
        ["-1", "-2", "-3", "a", "b"],
        ["-12", "a", "b"],
        ["-23", "a", "b"],
    ],
)
def test_suppressed_columns_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/comm.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_comm_inputs(cwd)

        assert_comm_parity(args, cwd)


# Output delimiters preserve ASCII, empty, and UTF-8 text bytes in every column.
@pytest.mark.parametrize(
    "args",
    [
        ["--output-delimiter=,", "a", "b"],
        ["--output-delimiter=é", "a", "b"],
        ["--output-delimiter=++", "a", "b"],
        ["--output-delimiter=", "a", "b"],
    ],
)
def test_output_delimiters_match_coreutils(args: list[str]) -> None:
    # Alternate output delimiters position later columns with the requested delimiter bytes.
    # upstream: coreutils/tests/misc/comm.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_comm_inputs(cwd)

        assert_comm_parity(args, cwd)


def test_duplicate_matching_output_delimiters_match_coreutils() -> None:
    # Repeating the same output delimiter value is accepted by GNU comm.
    # upstream: coreutils/tests/misc/comm.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_comm_inputs(cwd)

        assert_comm_parity(["--output-delimiter=,", "--output-delimiter=,", "a", "b"], cwd)


def test_duplicate_conflicting_output_delimiters_match_coreutils() -> None:
    # Conflicting output delimiter values are rejected before files are compared.
    # upstream: coreutils/tests/misc/comm.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_comm_inputs(cwd)

        assert_comm_parity(
            ["--output-delimiter=,", "--output-delimiter=+", "a", "b"],
            cwd,
            check_stderr=True,
        )


@pytest.mark.parametrize(
    "args",
    [
        ["--total", "a", "b"],
        ["--total", "-123", "a", "b"],
        ["--total", "--output-delimiter=", "a", "b"],
    ],
)
def test_total_rows_match_coreutils(args: list[str]) -> None:
    # Total mode reports per-column counts even when regular comparison rows are suppressed.
    # upstream: coreutils/tests/misc/comm.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_comm_inputs(cwd)

        assert_comm_parity(args, cwd)


@pytest.mark.parametrize(
    "args",
    [
        ["-z", "za", "zb"],
        ["-z", "-1", "za", "zb"],
        ["-z", "-23", "za", "zb"],
        ["-z", "--output-delimiter=", "za", "zb"],
        ["--total", "-z", "za", "zb"],
        ["--total", "-z123", "--output-delimiter=,", "za", "zb"],
    ],
)
def test_zero_terminated_modes_match_coreutils(args: list[str]) -> None:
    # Zero-terminated mode uses NUL records and NUL output terminators.
    # upstream: coreutils/tests/misc/comm.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_comm_nul_inputs(cwd)

        assert_comm_parity(args, cwd)


@pytest.mark.parametrize(
    ("args", "input_data"),
    [
        (["-", "b"], b"1\n3\n3\n3"),
        (["a", "-"], b"2\n2\n3\n3\n3"),
    ],
)
def test_single_stdin_operand_matches_coreutils(args: list[str], input_data: bytes) -> None:
    # A single `-` operand is read from stdin and compared with the named sorted input.
    # upstream: none - Adds comm stdin-operand parity beyond upstream runtime coverage.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_comm_inputs(cwd)

        assert_comm_parity(args, cwd, input_data=input_data)


def test_empty_and_final_unterminated_lines_match_coreutils() -> None:
    # upstream: coreutils/tests/misc/comm.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "left").write_bytes(b"\na\nb")
        _ = (cwd / "right").write_bytes(b"\nb\nc")

        assert_comm_parity(["left", "right"], cwd)


@pytest.mark.parametrize(
    "args",
    [
        [],
        ["a"],
        ["a", "b", "extra"],
    ],
)
def test_operand_count_diagnostics_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/comm.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_comm_inputs(cwd)

        assert_comm_parity(args, cwd, check_stderr=True)


@pytest.mark.parametrize(
    "args",
    [
        ["missing", "b"],
        ["a", "missing"],
        ["a b", "b"],
    ],
)
def test_file_diagnostics_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/comm.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_comm_inputs(cwd)

        assert_comm_parity(args, cwd, check_stderr=True)


def test_directory_operand_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/read-errors.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        directory = cwd / "dir"
        directory.mkdir()
        _ = (cwd / "b").write_bytes(b"1\n")

        assert_comm_parity(["dir", "b"], cwd, check_stderr=True)


def test_invalid_short_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_comm_parity(["-9", "a", "b"], cwd, check_stderr=True)


def test_repeated_stdin_operand_reports_benchmark_diagnostic() -> None:
    # Repeated stdin remains outside the model because GNU observes a second descriptor read error.
    # upstream: none - Documents this benchmark slice rejecting repeated stdin operands instead.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_comm_inputs(cwd)

        stdout, stderr, exit_code = run_bench_comm(["-", "-"], cwd, input_data=b"a\n")

    assert stdout == b""
    assert stderr == (
        b"comm: repeated standard input operands are not supported by this benchmark slice\n"
        b"Try 'comm --help' for more information.\n"
    )
    assert exit_code == 1


def test_unsorted_inputs_report_benchmark_diagnostic() -> None:
    # upstream: none - Documents this benchmark slice rejecting unsorted inputs instead of modeling
    # upstream-reason: GNU's partial-output order diagnostics.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "left").write_bytes(b"b\na\n")
        _ = (cwd / "right").write_bytes(b"a\nb\n")

        stdout, stderr, exit_code = run_bench_comm(["left", "right"], cwd)

    assert stdout == b""
    assert stderr == b"comm: input is not sorted in the benchmark-supported byte order\n"
    assert exit_code == 1


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_comm(args, cwd)
            bench = run_bench_comm(args, cwd)
            assert_requested_message_behavior(ref, bench)


def test_deferred_comm_regressions_inventory() -> None:
    # Not ported yet: GNU's precise partial-output sortedness diagnostics plus
    # `--check-order` and `--nocheck-order` are deferred.
    # Not ported yet: repeated stdin operands cannot reproduce GNU's second-read
    # file-descriptor diagnostic in the current World model.
    # upstream: coreutils/tests/misc/comm.pl
    pytest.skip("requires deferred comm options or sortedness diagnostics")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", COMM_VERIFY_TARGETS)
def test_comm_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
