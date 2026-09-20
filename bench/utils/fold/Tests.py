"""Check fold line wrapping parity against GNU coreutils and verify proof surface."""

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

BENCH_FOLD_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "fold_bench.dll")
COREUTILS_FOLD = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "fold")


def build_fold_once_if_needed() -> None:
    lock_path = ROOT / "_build" / "bench" / ".build_bench_lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("w", encoding="utf-8") as lock_file:
        fcntl.flock(lock_file, fcntl.LOCK_EX)
        if (
            not BENCH_FOLD_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "fold") > BENCH_FOLD_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "fold")
        if not COREUTILS_FOLD.exists():
            build_coreutils_utility(ROOT, "fold")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_fold(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_FOLD_DLL, args, cwd, input_data=input_data)


def run_system_fold(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_FOLD, "fold", args, cwd, input_data=input_data)


def assert_fold_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_fold(args, cwd, input_data=input_data)
    bench = run_bench_fold(args, cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench)


# Default width wraps long stdin lines at 80 bytes.
def test_default_width_wraps_long_stdin_line_matches_coreutils() -> None:
    # upstream: coreutils/tests/fold/fold.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        build_fold_once_if_needed()
        assert_fold_parity([], cwd, input_data=b"a" * 85 + b"\n")


# The width option wraps file input at the requested byte count.
def test_width_option_wraps_file_line_matches_coreutils() -> None:
    # upstream: coreutils/tests/fold/fold.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "input.txt").write_bytes(b"abcdef\nghijkl")
        build_fold_once_if_needed()
        assert_fold_parity(["-b", "-w", "4", "input.txt"], cwd)


# Spaces mode wraps at the last blank that fits before the width boundary.
def test_spaces_mode_wraps_at_previous_blank_matches_coreutils() -> None:
    # upstream: coreutils/tests/fold/fold.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        build_fold_once_if_needed()
        assert_fold_parity(["-s", "-w", "8"], cwd, input_data=b"aa bb ccdd\n")


# Default mode treats C-locale control bytes as columns, not raw bytes.
def test_default_column_controls_match_coreutils() -> None:
    # upstream: none - coreutils/src/fold.c adjust_column; no upstream runtime coverage
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        payload = (
            b"\x08\t"
            + bytes(range(11, 32))
            + b" !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcd"
        )
        (cwd / "a.txt").write_bytes(payload)
        build_fold_once_if_needed()
        assert_fold_parity(["a.txt"], cwd)


# The vendored scanner stops at byte 0xff before later bytes are folded.
def test_ff_byte_terminates_scanner_matches_coreutils() -> None:
    # upstream: none - coreutils/src/fold.c mbbuf_get_char; no upstream runtime coverage
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "a.txt").write_bytes(bytes([0xFE, 0xFF, 0x00, 0x01, ord("A")]))
        build_fold_once_if_needed()
        assert_fold_parity(["a.txt"], cwd)


# Default column mode treats NUL as zero-width in the vendored LC_ALL=C build.
def test_default_nul_is_zero_width_matches_coreutils() -> None:
    # upstream: none - coreutils/src/fold.c adjust_column; no upstream runtime coverage
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "a.txt").write_bytes((b"\x00" * 90) + (b"A" * 80))
        build_fold_once_if_needed()
        assert_fold_parity(["a.txt"], cwd)


# Nonnumeric width values use GNU's short invalid-number diagnostic.
def test_nonnumeric_width_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/gnulib-tests/test-xstrtol.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        build_fold_once_if_needed()
        ref = run_system_fold(["--width", "-b"], cwd)
        bench = run_bench_fold(["--width", "-b"], cwd)
        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Earlier invalid widths are reported before a later missing width value.
def test_invalid_width_before_missing_width_value_matches_coreutils() -> None:
    # upstream: none - Adds fold diagnostic ordering parity for invalid and missing width values.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        build_fold_once_if_needed()
        ref = run_system_fold(["-w", "-w", "-b", "-w"], cwd)
        bench = run_bench_fold(["-w", "-w", "-b", "-w"], cwd)
        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Multiple file operands continue after a missing file and preserve input order.
def test_multiple_files_are_processed_in_order_matches_coreutils() -> None:
    # upstream: coreutils/tests/fold/multiple-files.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "file1").write_bytes(b"a\n")
        (cwd / "file2").write_bytes(b"b\n")
        build_fold_once_if_needed()
        ref = run_system_fold(["file1", "missing", "file2"], cwd)
        bench = run_bench_fold(["file1", "missing", "file2"], cwd)
        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Missing paths containing shell-special bytes use GNU's quoted diagnostic.
def test_missing_path_with_space_is_quoted_matches_coreutils() -> None:
    # upstream: coreutils/tests/fold/multiple-files.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        build_fold_once_if_needed()
        ref = run_system_fold(["next monday"], cwd)
        bench = run_bench_fold(["next monday"], cwd)
        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Each named file starts with a fresh wrap column even when the previous file lacks a newline.
def test_file_operand_boundary_resets_wrap_column_matches_coreutils() -> None:
    # upstream: coreutils/tests/fold/multiple-files.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "file1").write_bytes(b"abcde")
        (cwd / "file2").write_bytes(b"fghi")
        build_fold_once_if_needed()
        assert_fold_parity(["-w", "4", "file1", "file2"], cwd)


# Help exits successfully with the shared requested-message contract.
def test_help_exit_successfully_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        build_fold_once_if_needed()
        assert_requested_message_behavior(
            run_system_fold(["--help"], cwd),
            run_bench_fold(["--help"], cwd),
        )


# Version exits successfully with the shared requested-message contract.
def test_version_exit_successfully_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        build_fold_once_if_needed()
        assert_requested_message_behavior(
            run_system_fold(["--version"], cwd),
            run_bench_fold(["--version"], cwd),
        )


# The fold CLI schema module verifies independently.
@pytest.mark.dafny_verify
def test_fold_schema_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "fold" / "FoldSchema.dfy")


# The fold executable core module verifies independently.
@pytest.mark.dafny_verify
def test_fold_core_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "fold" / "FoldCore.dfy")


# The fold world-transition spec module verifies independently.
@pytest.mark.dafny_verify
def test_fold_spec_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "fold" / "FoldSpec.dfy")


# The fold proof bridge module verifies independently.
@pytest.mark.dafny_verify
def test_fold_proof_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "fold" / "FoldProof.dfy")


# The fold benchmark item module verifies independently.
@pytest.mark.dafny_verify
def test_fold_benchmark_item_verifies() -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(ROOT / "bench" / "utils" / "fold" / "Fold.dfy")
