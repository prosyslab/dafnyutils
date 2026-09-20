"""Check paste parallel/serial line merging parity and verify proof surface."""

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

BENCH_PASTE_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "paste_bench.dll")
COREUTILS_PASTE = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "paste")
PASTE_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "paste" / "PasteSchema.dfy",
    ROOT / "bench" / "utils" / "paste" / "PasteCore.dfy",
    ROOT / "bench" / "utils" / "paste" / "PasteSpec.dfy",
    ROOT / "bench" / "utils" / "paste" / "PasteProof.dfy",
    ROOT / "bench" / "utils" / "paste" / "Paste.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_paste_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_PASTE_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "paste") > BENCH_PASTE_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "paste")
        if not COREUTILS_PASTE.exists():
            build_coreutils_utility(ROOT, "paste")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_paste(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_PASTE_DLL, args, cwd, input_data=input_data)


def run_system_paste(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_PASTE, "paste", args, cwd, input_data=input_data)


def assert_paste_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_paste(args, cwd, input_data=input_data)
    bench = run_bench_paste(args, cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench)


def test_stdin_default_lines_match_coreutils() -> None:
    # upstream: coreutils/tests/paste/paste.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_paste_parity([], Path(tmp_dir), input_data=b"a\nb\n")


def test_parallel_files_use_tabs_and_blank_missing_rows() -> None:
    # upstream: coreutils/tests/paste/paste.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "left.txt").write_bytes(b"a\nb\n")
        _ = (cwd / "right.txt").write_bytes(b"1\n")

        assert_paste_parity(["left.txt", "right.txt"], cwd)


def test_serial_mode_outputs_each_file_independently() -> None:
    # upstream: coreutils/tests/paste/paste.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "left.txt").write_bytes(b"a\nb\n")
        _ = (cwd / "right.txt").write_bytes(b"1\n2\n")

        assert_paste_parity(["-s", "left.txt", "right.txt"], cwd)


def test_serial_missing_file_preserves_successful_output() -> None:
    # upstream: coreutils/tests/paste/paste.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "present.txt").write_bytes(b"ok\nagain\n")

        ref = run_system_paste(["-s", "present.txt", "missing.txt"], cwd)
        bench = run_bench_paste(["-s", "present.txt", "missing.txt"], cwd)

        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


def test_custom_delimiters_and_stdin_operand_match_coreutils() -> None:
    # upstream: coreutils/tests/paste/paste.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "tail.txt").write_bytes(b"1\n2\n")

        assert_paste_parity(["-d", ",:", "-", "tail.txt"], cwd, input_data=b"a\nb\n")


# Zero-terminated parallel mode must preserve final unterminated records.
def test_zero_terminated_parallel_final_records_match_coreutils() -> None:
    # upstream: coreutils/tests/paste/paste.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "left.txt").write_bytes(b"a\0")
        _ = (cwd / "right.txt").write_bytes(b"b")

        assert_paste_parity(["-z", "left.txt", "right.txt"], cwd)


# Zero-terminated serial mode must still honor the custom delimiter list.
def test_zero_terminated_serial_custom_delimiter_matches_coreutils() -> None:
    # upstream: coreutils/tests/paste/paste.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "records.txt").write_bytes(b"1\0a")

        assert_paste_parity(["--zero-terminated", "-s", "-d", " ", "records.txt"], cwd)


# Empty NUL-delimited stdin records must remain records rather than disappearing.
def test_zero_terminated_stdin_empty_records_match_coreutils() -> None:
    # upstream: coreutils/tests/paste/paste.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_paste_parity(["-z"], Path(tmp_dir), input_data=b"a\0\0b")


# Parallel repeated stdin operands must share one stream row-wise.
def test_parallel_repeated_stdin_operands_match_coreutils() -> None:
    # upstream: none - Adds paste repeated-stdin parity beyond upstream runtime coverage.
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_paste_parity(["-", "-"], Path(tmp_dir), input_data=b"a\nb\nc\n")


# Zero-terminated repeated stdin operands must share one NUL-delimited stream row-wise.
def test_zero_terminated_repeated_stdin_operands_match_coreutils() -> None:
    # upstream: none - Adds paste zero-terminated repeated-stdin parity.
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_paste_parity(["-z", "-", "-"], Path(tmp_dir), input_data=b"a\0b\0c")


def test_missing_file_reports_failure_after_successful_operands() -> None:
    # upstream: coreutils/tests/paste/paste.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "present.txt").write_bytes(b"ok\n")

        assert_paste_parity(["present.txt", "missing.txt"], cwd)


# Parallel mode reports only the first unreadable operand and suppresses stdout.
def test_parallel_multiple_missing_files_reports_first_failure() -> None:
    # upstream: none - Adds paste multiple-open-failure ordering parity.
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_paste_parity(["missing-a.txt", "missing-b.txt"], Path(tmp_dir))


# Serial mode continues after unreadable operands and reports each failure.
def test_serial_multiple_missing_files_reports_each_failure() -> None:
    # upstream: none - Adds paste serial open-failure continuation parity.
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_paste_parity(["-s", "missing-a.txt", "missing-b.txt"], Path(tmp_dir))


# Parallel directory read errors must preserve rows formed from readable operands.
def test_parallel_directory_operand_preserves_partial_row() -> None:
    # upstream: coreutils/tests/misc/read-errors.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "left.txt").write_bytes(b"a\n")
        (cwd / "dir").mkdir()

        assert_paste_parity(["left.txt", "dir"], cwd)


# Zero-terminated directory read errors must terminate preserved partial rows with NUL.
def test_zero_terminated_directory_operand_preserves_partial_record() -> None:
    # upstream: coreutils/tests/misc/read-errors.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "left.txt").write_bytes(b"a\0")
        (cwd / "dir").mkdir()

        assert_paste_parity(["-z", "left.txt", "dir"], cwd)


# Parallel open failures must preempt later directory read diagnostics.
def test_parallel_open_failure_preempts_directory_read_error() -> None:
    # upstream: none - Adds paste mixed missing-and-directory ordering parity.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "left.txt").write_bytes(b"a\n")
        (cwd / "dir").mkdir()

        assert_paste_parity(["left.txt", "dir", "missing.txt"], cwd)


# Diagnostic paths containing shell-sensitive assignment characters must be quoted.
def test_missing_assignment_like_path_is_quoted_like_coreutils() -> None:
    # Coreutils quotef diagnostic behavior.
    # upstream: coreutils/gnulib-tests/test-quotearg-simple
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_paste_parity(["a=rw"], Path(tmp_dir))


# Serial directory operands must still emit an empty record before the diagnostic.
def test_serial_directory_operand_emits_empty_record() -> None:
    # upstream: coreutils/tests/misc/read-errors.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "dir").mkdir()
        _ = (cwd / "right.txt").write_bytes(b"b\n")

        assert_paste_parity(["-s", "dir", "right.txt"], cwd)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_paste(args, cwd)
            bench = run_bench_paste(args, cwd)
            assert_requested_message_behavior(ref, bench)


def test_deferred_paste_regressions_inventory() -> None:
    # Not ported yet: locale-sensitive multibyte delimiter behavior is outside
    # the deterministic C-locale byte-oriented slice modeled here.
    # upstream: coreutils/tests/paste/multi-byte.sh
    pytest.skip("requires locale-sensitive multibyte delimiter handling")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", PASTE_VERIFY_TARGETS)
def test_paste_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
