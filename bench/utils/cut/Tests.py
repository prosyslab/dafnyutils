"""Check cut byte/character selection parity and verify proof surface."""

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

BENCH_CUT_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "cut_bench.dll")
COREUTILS_CUT = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "cut")
CUT_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "cut" / "CutSchema.dfy",
    ROOT / "bench" / "utils" / "cut" / "CutCore.dfy",
    ROOT / "bench" / "utils" / "cut" / "CutSpec.dfy",
    ROOT / "bench" / "utils" / "cut" / "CutProof.dfy",
    ROOT / "bench" / "utils" / "cut" / "Cut.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_cut_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_CUT_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "cut") > BENCH_CUT_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "cut")
        if not COREUTILS_CUT.exists():
            build_coreutils_utility(ROOT, "cut")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_cut(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_CUT_DLL, args, cwd, input_data=input_data)


def run_system_cut(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_CUT, "cut", args, cwd, input_data=input_data)


def assert_cut_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_cut(args, cwd, input_data=input_data)
    bench = run_bench_cut(args, cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench)


def assert_cut_diagnostic_parity(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> None:
    ref = run_system_cut(args, cwd, input_data=input_data)
    bench = run_bench_cut(args, cwd, input_data=input_data)
    assert_result_matches_reference(
        ref,
        bench,
        ignore_stderr_when_exit_nonzero=False,
    )


def test_stdin_byte_positions_match_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_parity(["-b", "1,3-4"], cwd, input_data=b"abcd\nxy\n")


# Complement mode prints bytes not selected by the byte range list.
def test_byte_complement_matches_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_parity(["--complement", "-b", "2-3"], cwd, input_data=b"abcd\nxy\n")


def test_stdin_character_range_adds_newline_for_partial_final_line() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_parity(["-c", "4"], cwd, input_data=b"123\n123\n123")


def test_file_operand_character_open_range_matches_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"abcdefg\nhi\n")

        assert_cut_parity(["-c", "2-4,6-", "input.txt"], cwd)


def test_multiple_files_and_stdin_operand_match_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "tail.txt").write_bytes(b"tail\n")

        assert_cut_parity(["-b", "1-2", "-", "tail.txt"], cwd, input_data=b"head\n")


def test_repeated_dash_consumes_stdin_once_match_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_parity(["-b", "1", "-", "-"], cwd, input_data=b"once\n")


# Zero-terminated byte mode terminates a final partial NUL-delimited record.
def test_zero_terminated_byte_records_match_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_parity(["-z", "-b", "1"], cwd, input_data=b"ab\0cd")


# Output delimiters split adjacent byte ranges instead of coalescing them.
def test_output_delimiter_splits_adjacent_byte_ranges_match_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_parity(["-b", "1-2,3-4", "--output-delimiter=:"], cwd, input_data=b"abcd\n")


# Output delimiters do not split ranges connected by overlap.
def test_output_delimiter_merges_overlapping_character_ranges_match_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_parity(
            ["-c", "1-3,2-4,6-", "--output-delimiter=:"],
            cwd,
            input_data=b"abcdefg\n",
        )


# Complement mode inserts output delimiters between complement groups.
def test_output_delimiter_complement_groups_match_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_parity(
            ["--complement", "-b", "2,4", "--output-delimiter=:"],
            cwd,
            input_data=b"abcdef\n",
        )


# An empty output delimiter argument selects GNU's NUL output delimiter.
def test_empty_output_delimiter_uses_nul_between_ranges_match_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_parity(["-b", "1,2", "--output-delimiter="], cwd, input_data=b"ab\n")


# Byte mode accepts -n as a GNU-compatible no-op.
def test_no_split_option_is_accepted_for_byte_mode() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_parity(["-n", "-b", "1,3"], cwd, input_data=b"abc\n")


# Invalid comma-separated list diagnostics keep the suffix that GNU reports.
def test_invalid_range_list_suffix_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_diagnostic_parity(["-c", "u=rw,go=r"], cwd, input_data=b"abc\n")


# Repeated-dash range diagnostics still report the first invalid position.
def test_repeated_dash_invalid_position_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_diagnostic_parity(["-c", "04z8u0-m8-5665"], cwd, input_data=b"abc\n")


def test_missing_file_with_space_operand_quotes_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_diagnostic_parity(["-b", "1", "a b"], cwd)


# Missing-file diagnostics quote shell-sensitive operand characters.
def test_missing_file_with_mode_like_operand_quotes_diagnostic_matches_coreutils() -> None:
    # upstream: none - Adds cut missing-file quoting parity for assignment-like operands.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_diagnostic_parity(["-c", "2-", "u=rw,go=r"], cwd)


def test_directory_operand_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/read-errors.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "dir").mkdir()

        assert_cut_diagnostic_parity(["-b", "1", "dir"], cwd)


@pytest.mark.parametrize(
    "args",
    [
        [],
        ["-b", ""],
        ["-b", "a.txt"],
        ["-b", "0"],
        ["-b", "-"],
        ["-b", "3-1"],
        ["-b", "1", "-c", "2"],
    ],
)
def test_list_diagnostics_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/cut/cut.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_cut_diagnostic_parity(args, cwd, input_data=b"abc\n")


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_cut(args, cwd)
            bench = run_bench_cut(args, cwd)
            assert_requested_message_behavior(ref, bench)


def test_deferred_cut_regressions_placeholder() -> None:
    # Not ported yet: field mode, custom input delimiters, -s suppression, and
    # locale-sensitive multibyte character handling are outside this benchmark slice.
    # Not ported yet: these need a memory-limit harness around streaming input.
    # upstream: coreutils/tests/cut/cut.pl
    # upstream: coreutils/tests/cut/cut-huge-range.sh
    # upstream: coreutils/tests/cut/bounded-memory.sh
    pytest.skip("requires deferred cut modes or memory-limit harness support")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", CUT_VERIFY_TARGETS, ids=lambda path: path.name)
def test_cut_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
