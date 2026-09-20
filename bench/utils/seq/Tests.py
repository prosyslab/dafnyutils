"""Check seq parity for fixed-point decimal scenarios and its Dafny proof surface."""

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

BENCH_SEQ_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "seq_bench.dll")
COREUTILS_SEQ = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "seq")
SEQ_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "seq" / "SeqCore.dfy",
    ROOT / "bench" / "utils" / "seq" / "SeqProof.dfy",
    ROOT / "bench" / "utils" / "seq" / "Seq.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_seq_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_SEQ_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "seq") > BENCH_SEQ_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "seq")
        if not COREUTILS_SEQ.exists():
            build_coreutils_utility(ROOT, "seq")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_seq(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_SEQ_DLL, args, cwd, env=parity_env())


def run_system_seq(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_SEQ, "seq", args, cwd, env=parity_env())


def verify_seq_module(target: Path) -> None:
    run_dafny_verify(target)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    assert_result_matches_reference(ref_result, bench_result)


@pytest.mark.parametrize(
    "args",
    [
        ["3"],
        ["1", "2", "5"],
        ["0"],
        ["--", "1", "-1", "-2"],
        ["--", "-0", "2"],
    ],
)
def test_integer_sequences_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/seq/seq.pl
    # upstream: coreutils/tests/seq/seq-extra-number.sh
    # upstream: coreutils/tests/seq/seq-precision.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_seq(args, cwd)
        bench = run_bench_seq(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        [".8", ".01", ".81"],
        ["1", ".5", "2"],
        ["01.50", ".25", "02.00"],
        ["--", "-0", "0.5", "1"],
    ],
)
def test_fixed_point_decimal_sequences_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/seq/seq.pl
    # upstream: coreutils/tests/seq/seq-extra-number.sh
    # upstream: coreutils/tests/seq/seq-precision.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_seq(args, cwd)
        bench = run_bench_seq(args, cwd)
        assert_same_result(ref, bench)


# GNU xstrtod regression: accepted sign and trailing-dot forms remain seq operands.
@pytest.mark.parametrize(
    "args",
    [
        ["+1"],
        ["1."],
        ["+1", "+1", "+3"],
        ["1.", "1.", "3."],
    ],
)
def test_gnulib_xstrtod_accepted_decimal_forms_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/gnulib-tests/test-xstrtod
    # upstream: coreutils/gnulib-tests/test-xstrtold
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_seq(args, cwd)
        bench = run_bench_seq(args, cwd)
        assert_same_result(ref, bench)


# GNU xstrtod regression: incomplete decimal spellings are rejected as numbers.
@pytest.mark.parametrize("args", [["."], ["+.e-0"]])
def test_gnulib_xstrtod_incomplete_decimal_forms_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/gnulib-tests/test-xstrtod
    # upstream: coreutils/gnulib-tests/test-xstrtold
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_seq(args, cwd)
        bench = run_bench_seq(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize("args", [[".9e2"], ["1e0", "1e0", "3e0"], ["1e-1", "1e-1", "3e-1"]])
def test_scientific_notation_numbers_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/gnulib-tests/test-xstrtod
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_seq(args, cwd)
        bench = run_bench_seq(args, cwd)
        assert_same_result(ref, bench)


# Custom separators preserve their exact UTF-8 bytes in emitted output.
@pytest.mark.parametrize(
    "args",
    [
        ["-s,", "1", "3"],
        ["--separator=é", "1", "3"],
        ["--separator=::", "1", "3"],
        ["-s", "-", "1", "3"],
    ],
)
def test_separator_option_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/seq/seq.pl
    # upstream: coreutils/tests/seq/seq-extra-number.sh
    # upstream: coreutils/tests/seq/seq-precision.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_seq(args, cwd)
        bench = run_bench_seq(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        ["-w", "8", "10"],
        ["--equal-width", "1", ".5", "2"],
        ["-w", "--", "-1", "1", "1"],
    ],
)
def test_equal_width_option_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/seq/seq.pl
    # upstream: coreutils/tests/seq/seq-extra-number.sh
    # upstream: coreutils/tests/seq/seq-precision.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_seq(args, cwd)
        bench = run_bench_seq(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        [],
        ["1", "0", "3"],
        ["a"],
        ["--", " 1 "],
        ["1", "2", "3", "4"],
        ["1", "-s,", "3"],
    ],
)
def test_error_scenarios_match_coreutils_status_and_stdout(args: list[str]) -> None:
    # upstream: coreutils/tests/seq/seq.pl
    # upstream: coreutils/tests/seq/seq-extra-number.sh
    # upstream: coreutils/tests/seq/seq-precision.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_seq(args, cwd)
        bench = run_bench_seq(args, cwd)
        assert_same_result(ref, bench)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_seq(args, cwd)
            bench = run_bench_seq(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize(
    "args",
    [["--help", "--version"], ["--version", "--help"]],
)
def test_help_version_precedence_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_seq(args, cwd)
        bench = run_bench_seq(args, cwd)
        assert_requested_message_behavior(ref, bench)


def test_deferred_seq_regressions_placeholder() -> None:
    # Not ported yet: these require broken-pipe handling, /dev/full write
    # redirection, non-C locale availability, or glibc-specific long-double
    # behavior that the current parity harness intentionally avoids.
    # upstream: coreutils/tests/seq/seq-epipe.sh
    # upstream: coreutils/tests/seq/seq-io-errors.sh
    # upstream: coreutils/tests/seq/seq-locale.sh
    # upstream: coreutils/tests/seq/seq-long-double.sh
    pytest.skip("requires pipe, locale, or platform-specific seq fixtures")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", SEQ_VERIFY_TARGETS, ids=lambda path: path.name)
def test_seq_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_seq_module(target)
