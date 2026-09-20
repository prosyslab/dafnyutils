"""Check tail line and byte selection parity against GNU coreutils and verify proof surface."""

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

BENCH_TAIL_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "tail_bench.dll")
COREUTILS_TAIL = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "tail")
TAIL_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "tail" / "TailSchema.dfy",
    ROOT / "bench" / "utils" / "tail" / "TailCore.dfy",
    ROOT / "bench" / "utils" / "tail" / "TailSpec.dfy",
    ROOT / "bench" / "utils" / "tail" / "TailProof.dfy",
    ROOT / "bench" / "utils" / "tail" / "Tail.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_tail_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_TAIL_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "tail") > BENCH_TAIL_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "tail")
        if not COREUTILS_TAIL.exists():
            build_coreutils_utility(ROOT, "tail")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_tail(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_TAIL_DLL, args, cwd, input_data=input_data)


def run_system_tail(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_TAIL, "tail", args, cwd, input_data=input_data)


def assert_tail_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_tail(args, cwd, input_data=input_data)
    bench = run_bench_tail(args, cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench)


# Default file input emits the last ten lines.
def test_default_last_ten_lines_from_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n11\n")

        assert_tail_parity(["input.txt"], cwd)


# Positive stdin line count emits the last requested lines.
def test_positive_line_count_from_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["-n", "2"], cwd, input_data=b"a\nb\nc\nd\n")


# Explicit negative stdin line count emits the last requested lines.
def test_negative_line_count_from_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["-n", "-2"], cwd, input_data=b"a\nb\nc\nd\n")


# Plus-prefixed stdin line count emits from the requested start line.
def test_from_start_line_count_from_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["-n", "+3"], cwd, input_data=b"a\nb\nc\nd\n")


# Legacy bare negative counts select lines from the end.
def test_legacy_bare_negative_line_count_from_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["-1"], cwd, input_data=b"x\ny\n")


# Legacy bare plus counts select lines from the requested start line.
def test_legacy_bare_plus_line_count_from_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["+2"], cwd, input_data=b"x\ny\n")


# Legacy c-suffixed plus counts select bytes from the requested start byte.
def test_legacy_plus_byte_count_from_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["+2c"], cwd, input_data=b"abcd")


# Legacy c-suffixed negative counts select bytes from the end.
def test_legacy_negative_byte_count_from_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["-1c"], cwd, input_data=b"abcd")


# Legacy l-suffixed counts select lines from the end.
def test_legacy_l_suffix_line_count_from_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["-1l"], cwd, input_data=b"x\ny\n")


# Legacy -l compatibility selects the default last ten lines.
def test_legacy_l_option_default_count_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["-l"], cwd, input_data=b"x\n" + (b"y\n" * 10) + b"z")


# Legacy -b compatibility selects ten 512-byte blocks from the end.
def test_legacy_b_option_block_count_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["-b"], cwd, input_data=(b"x\n" * ((512 * 10 // 2) + 1)))


# Zero-terminated line mode treats NUL as the record delimiter.
def test_zero_terminated_last_records_match_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["-z", "-n", "2"], cwd, input_data=b"a\0b\0c\0")


# Zero-terminated +NUM starts at the requested one-based record.
def test_zero_terminated_from_record_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["--zero-terminated", "-n", "+2"], cwd, input_data=b"a\0b\0c\0")


# Positive stdin byte count emits the last requested bytes.
def test_byte_count_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail-c.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["-c", "3"], cwd, input_data=b"123456")


# Long-looking count arguments use GNU's normalized invalid-count diagnostic.
def test_long_option_count_value_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_tail(["-c", "--lines"], cwd)
        bench = run_bench_tail(["-c", "--lines"], cwd)
        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Short-looking count arguments use GNU's normalized invalid-count diagnostic.
def test_short_option_count_value_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_tail(["--bytes", "-n"], cwd)
        bench = run_bench_tail(["--bytes", "-n"], cwd)
        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Earlier invalid counts are reported before a later missing option value.
def test_invalid_count_before_missing_value_matches_coreutils() -> None:
    # upstream: none - Adds tail diagnostic ordering parity for invalid and missing count values.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_tail(["-q", "-n", "-z", "--lines"], cwd)
        bench = run_bench_tail(["-q", "-n", "-z", "--lines"], cwd)
        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Mixed file and stdin operands print headers around each successful input.
def test_file_and_stdin_operands_with_headers_match_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "first.txt").write_bytes(b"file-a\nfile-b\n")
        _ = (cwd / "second.txt").write_bytes(b"tail-a\ntail-b\n")

        assert_tail_parity(
            ["first.txt", "-", "second.txt"],
            cwd,
            input_data=b"stdin-a\nstdin-b\n",
        )


def write_header_inputs(cwd: Path) -> None:
    _ = (cwd / "first.txt").write_bytes(b"a\nb\n")
    _ = (cwd / "second.txt").write_bytes(b"c\nd\n")


# Multiple file operands print default headers.
def test_default_multifile_headers_match_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_header_inputs(cwd)
        assert_tail_parity(["first.txt", "second.txt"], cwd)


# Quiet mode suppresses multiple-file headers.
def test_quiet_header_mode_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_header_inputs(cwd)
        assert_tail_parity(["--quiet", "first.txt", "second.txt"], cwd)


# Silent mode suppresses multiple-file headers.
def test_silent_header_mode_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_header_inputs(cwd)
        assert_tail_parity(["--silent", "first.txt", "second.txt"], cwd)


# Verbose mode prints a header for a single file.
def test_verbose_header_mode_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_header_inputs(cwd)
        assert_tail_parity(["--verbose", "first.txt"], cwd)


def write_count_input(cwd: Path) -> None:
    _ = (cwd / "input.txt").write_bytes(b"a\nb\nc\nd\n")


# Zero line count emits no lines.
def test_zero_line_count_from_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_count_input(cwd)
        assert_tail_parity(["-n", "0", "input.txt"], cwd)


# Zero line count suppresses empty headers across file and stdin operands.
def test_zero_line_count_multifile_stdin_headers_match_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_count_input(cwd)
        assert_tail_parity(["--lines", "0", "input.txt", "-"], cwd, input_data=b"stdin\n")


# Negative zero line count emits no lines.
def test_negative_zero_line_count_from_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_count_input(cwd)
        assert_tail_parity(["-n", "-0", "input.txt"], cwd)


# Plus zero line count emits from the beginning.
def test_plus_zero_line_count_from_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_count_input(cwd)
        assert_tail_parity(["-n", "+0", "input.txt"], cwd)


# Long line-count option emits the last requested lines.
def test_long_line_count_option_from_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_count_input(cwd)
        assert_tail_parity(["--lines=2", "input.txt"], cwd)


# Positive byte count emits the last requested bytes from a file.
def test_positive_byte_count_from_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_count_input(cwd)
        assert_tail_parity(["-c", "2", "input.txt"], cwd)


# Long byte-count option emits the last requested bytes from a file.
def test_long_byte_count_option_from_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_count_input(cwd)
        assert_tail_parity(["--bytes=2", "input.txt"], cwd)


# Zero byte count does not read or diagnose missing operands.
def test_zero_byte_count_missing_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tail_parity(["--bytes", "0", "missing.txt"], cwd)


# Plus-prefixed byte count emits from the requested start byte.
def test_from_start_byte_count_from_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_count_input(cwd)
        assert_tail_parity(["-c", "+2", "input.txt"], cwd)


# GNU xstrtol regression: tail accepts coreutils multiplier suffixes on counts.
@pytest.mark.parametrize("args", [["-n", "1k"], ["-n", "MiB"], ["-c", "1kB"]])
def test_gnulib_xstrtol_count_suffixes_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/gnulib-tests/test-xstrtol.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_count_input(cwd)
        assert_tail_parity([*args, "input.txt"], cwd)


# GNU count suffixes through exa scale are accepted when the decoded count fits.
def test_gnu_gigabyte_count_suffix_matches_coreutils() -> None:
    # upstream: none - Documents GNU tail usage count suffix behavior.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_count_input(cwd)
        assert_tail_parity(["-c", "1G", "input.txt"], cwd)


# GNU binary count suffixes through exbi scale are accepted when the decoded count fits.
def test_gnu_binary_exabyte_count_suffix_matches_coreutils() -> None:
    # upstream: none - Documents GNU tail usage count suffix behavior.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        write_count_input(cwd)
        assert_tail_parity(["-c", "1EiB", "input.txt"], cwd)


# GNU xstrtol regression: invalid suffixes are count errors.
@pytest.mark.parametrize(
    "args",
    [
        ["-n", "x"],
        ["-n", "9x"],
        ["-n", "1bB"],
        ["-n", "99999999999999999999999999999999999999999999999999999999999999999999h"],
    ],
)
def test_gnulib_xstrtol_invalid_count_suffixes_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/gnulib-tests/test-xstrtol.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_tail(args, cwd)
        bench = run_bench_tail(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


# Directory operands in line mode report read diagnostics.
def test_directory_operand_line_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/read-errors.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "dir").mkdir()
        ref = run_system_tail(["-n", "1", "dir"], cwd)
        bench = run_bench_tail(["-n", "1", "dir"], cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


# Directory operands in byte mode report read diagnostics.
def test_directory_operand_byte_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/read-errors.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "dir").mkdir()
        ref = run_system_tail(["-c", "1", "dir"], cwd)
        bench = run_bench_tail(["-c", "1", "dir"], cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


# Directory operands still receive multifile headers before read diagnostics.
def test_multifile_directory_header_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/read-errors.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"a\nb\n")
        (cwd / "dir").mkdir()
        ref = run_system_tail(["input.txt", "dir"], cwd)
        bench = run_bench_tail(["input.txt", "dir"], cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


# Missing operands do not receive multifile headers when open fails.
def test_multifile_missing_operand_omits_header_matches_coreutils() -> None:
    # upstream: none - Adds tail multifile missing-operand header parity.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"a\nb\n")
        ref = run_system_tail(["input.txt", "missing.txt"], cwd)
        bench = run_bench_tail(["input.txt", "missing.txt"], cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


# Invalid line counts report a count diagnostic.
def test_invalid_line_count_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_tail(["-n", "bad"], cwd)
        bench = run_bench_tail(["-n", "bad"], cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


# Invalid byte counts report a count diagnostic.
def test_invalid_byte_count_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/tail/tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_tail(["--bytes=nope"], cwd)
        bench = run_bench_tail(["--bytes=nope"], cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


# Help requests print usage information and exit successfully.
def test_help_exits_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_tail(["--help"], cwd)
        bench = run_bench_tail(["--help"], cwd)
        assert_requested_message_behavior(ref, bench)


# Version requests print version information and exit successfully.
def test_version_exits_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_tail(["--version"], cwd)
        bench = run_bench_tail(["--version"], cwd)
        assert_requested_message_behavior(ref, bench)


# Deferred upstream regressions are inventoried with their unsupported host effects.
def test_deferred_tail_regressions_inventory() -> None:
    # Not ported: tail.pl f-pipe-1 follow-mode regression.
    # Not ported: `-f` follow mode requires blocking stream observation.
    # Not ported: procfs/sysfs, /dev/zero, and /dev/urandom cases require
    # special device and quasi-seekable host effects outside World.
    # Not ported: this is a seek/buffering stress regression rather than
    # an observable World-level semantic difference for regular files.
    # upstream: coreutils/tests/tail/tail.pl
    # upstream: coreutils/tests/tail/tail-c.sh
    # upstream: coreutils/tests/tail/basic-seek.sh
    pytest.skip("requires deferred tail options or unmodeled host effects")


# The tail schema module verifies independently.
@pytest.mark.dafny_verify
def test_tail_schema_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(TAIL_VERIFY_TARGETS[0])


# The tail core module verifies independently.
@pytest.mark.dafny_verify
def test_tail_core_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(TAIL_VERIFY_TARGETS[1])


# The tail spec module verifies independently.
@pytest.mark.dafny_verify
def test_tail_spec_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(TAIL_VERIFY_TARGETS[2])


# The tail proof module verifies independently.
@pytest.mark.dafny_verify
def test_tail_proof_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(TAIL_VERIFY_TARGETS[3])


# The tail benchmark item module verifies independently.
@pytest.mark.dafny_verify
def test_tail_benchmark_item_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(TAIL_VERIFY_TARGETS[4])
