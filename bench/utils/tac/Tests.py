"""Check tac record-reversal parity against GNU coreutils and verify proof surface."""

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

BENCH_TAC_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "tac_bench.dll")
COREUTILS_TAC = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "tac")
TAC_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "tac" / "TacSchema.dfy",
    ROOT / "bench" / "utils" / "tac" / "TacCore.dfy",
    ROOT / "bench" / "utils" / "tac" / "TacSpec.dfy",
    ROOT / "bench" / "utils" / "tac" / "TacProof.dfy",
    ROOT / "bench" / "utils" / "tac" / "Tac.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_tac_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_TAC_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "tac") > BENCH_TAC_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "tac")
        if not COREUTILS_TAC.exists():
            build_coreutils_utility(ROOT, "tac")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_tac(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_TAC_DLL, args, cwd, input_data=input_data)


def run_system_tac(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_TAC, "tac", args, cwd, input_data=input_data)


def assert_tac_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_tac(args, cwd, input_data=input_data)
    bench = run_bench_tac(args, cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench)


@pytest.mark.parametrize(
    "payload",
    [
        b"",
        b"a",
        b"\n",
        b"a\n",
        b"a\nb",
        b"a\nb\n",
        b"1234567\n8\n",
        b"12345\n8\n",
    ],
)
def test_stdin_default_newline_records_match_coreutils(payload: bytes) -> None:
    # upstream: coreutils/tests/tac/tac.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_tac_parity([], Path(tmp_dir), input_data=payload)


def test_single_file_default_newline_records_match_coreutils() -> None:
    # upstream: coreutils/tests/tac/tac.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"alpha\nbeta\ngamma\n")

        assert_tac_parity(["input.txt"], cwd)


def test_multiple_operands_reverse_each_input_separately() -> None:
    # upstream: coreutils/tests/tac/tac.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "first.txt").write_bytes(b"a\nb\n")
        _ = (cwd / "second.txt").write_bytes(b"1\n2\n")

        assert_tac_parity(["first.txt", "second.txt"], cwd)


def test_file_and_stdin_operands_match_coreutils() -> None:
    # upstream: coreutils/tests/tac/tac.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "tail.txt").write_bytes(b"tail-a\ntail-b\n")

        assert_tac_parity(["-", "tail.txt"], cwd, input_data=b"head-a\nhead-b\n")


# A literal custom separator reverses separator-delimited records.
def test_custom_separator_matches_coreutils() -> None:
    # upstream: coreutils/tests/tac/tac.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tac_parity(["-s", "--"], cwd, input_data=b"one--two--three--")


# Before mode attaches separators to the following record before reversal.
def test_before_mode_with_custom_separator_matches_coreutils() -> None:
    # upstream: coreutils/tests/tac/tac.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tac_parity(["-b", "-s", "--"], cwd, input_data=b"one--two--three--")


# After mode uses the rightmost start in an overlapping literal separator cluster.
def test_overlapping_custom_separator_matches_coreutils() -> None:
    # upstream: none - Adds tac literal-overlap separator parity beyond upstream runtime coverage.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tac_parity(["-s", "--"], cwd, input_data=b"a---b")


# After mode scans literal separators from right to left across repeated prefixes.
def test_repeated_prefix_separator_after_mode_matches_coreutils() -> None:
    # upstream: none - Adds tac repeated-prefix separator parity beyond upstream runtime coverage.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tac_parity(["-s", "aba"], cwd, input_data=b"abababa")


# After mode backs up the next scan after a repeated-byte literal separator.
def test_repeated_byte_separator_after_mode_matches_coreutils() -> None:
    # upstream: none - Adds tac repeated-byte separator parity beyond upstream runtime coverage.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tac_parity(["-s", "aa"], cwd, input_data=b"baaaa")


# Before mode uses the rightmost start in an overlapping literal separator cluster.
def test_before_mode_with_overlapping_custom_separator_matches_coreutils() -> None:
    # upstream: none - Adds tac before-mode literal-overlap separator parity.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tac_parity(["-b", "-s", "--"], cwd, input_data=b"a---b")


# Before mode backs up the next scan after a repeated-byte literal separator.
def test_repeated_byte_separator_before_mode_matches_coreutils() -> None:
    # upstream: none - Adds tac before-mode repeated-byte separator parity.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tac_parity(["-b", "-s", "aa"], cwd, input_data=b"baaaa")


# An empty separator is treated as an ASCII NUL literal separator.
def test_empty_separator_matches_coreutils_nul_records() -> None:
    # upstream: coreutils/tests/tac/tac.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_tac_parity(["-s", ""], cwd, input_data=b"a\0b\0c\0")


def test_repeated_dash_consumes_stdin_once_match_coreutils() -> None:
    # upstream: coreutils/tests/tac/tac-2-nonseekable.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_tac_parity(["-", "-"], Path(tmp_dir), input_data=b"x\n")


def test_missing_file_diagnostic_and_continuation_match_coreutils() -> None:
    # upstream: coreutils/tests/tac/tac-continue.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "five.txt").write_bytes(b"1\n2\n3\n4\n5\n")

        ref = run_system_tac(["missing.txt", "five.txt"], cwd)
        bench = run_bench_tac(["missing.txt", "five.txt"], cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


def test_missing_file_with_space_operand_quotes_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/tac/tac.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["a b"]
        ref = run_system_tac(args, cwd)
        bench = run_bench_tac(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_tac(args, cwd)
            bench = run_bench_tac(args, cwd)
            assert_requested_message_behavior(ref, bench)


def test_deferred_tac_regressions_inventory() -> None:
    # opt-r, opt-r2, opt-r3, opt-r4, opt-r5.
    # Not ported: `-r` regular-expression separators are outside this slice.
    # Not ported: tac.pl opt-br and opt-br2 regressions.
    # Not ported: `-b` with `-r` is deferred with regular-expression separators.
    # Not ported: tac.pl pipe-bad-tmpdir regression.
    # Not ported: non-seekable buffering to `$TMPDIR` and temporary-storage
    # failures are not represented in `World`.
    # Not ported: this is a C allocator stress regression; the benchmark covers
    # the same default no-newline semantics with smaller fixtures.
    # Not ported: requires root-only mount setup and ENOSPC during temp buffering.
    # Not ported: procfs/sysfs quasi-seekable inputs are outside the filesystem
    # model used by subprocess parity tests.
    # Not ported: the runner always supplies stdin through subprocess pipes.
    # Not ported: tac-locale.sh locale-sensitive non-ASCII separators.
    # Not ported: locale-sensitive non-ASCII separators depend on locale handling.
    # upstream: coreutils/tests/tac/tac.pl
    # upstream: coreutils/tests/tac/tac-2-nonseekable.sh
    # upstream: coreutils/tests/tac/tac-continue.sh
    # upstream: coreutils/tests/tac/tac-locale.sh
    pytest.skip("inventory only: documents GNU tac cases outside this benchmark slice")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", TAC_VERIFY_TARGETS)
def test_tac_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
