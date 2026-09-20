"""Check uniq adjacent-line parity against GNU coreutils and verify proof surface."""

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

BENCH_UNIQ_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "uniq_bench.dll")
COREUTILS_UNIQ = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "uniq")
UNIQ_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "uniq" / "UniqSchema.dfy",
    ROOT / "bench" / "utils" / "uniq" / "UniqCore.dfy",
    ROOT / "bench" / "utils" / "uniq" / "UniqSpec.dfy",
    ROOT / "bench" / "utils" / "uniq" / "UniqProof.dfy",
    ROOT / "bench" / "utils" / "uniq" / "Uniq.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_uniq_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_UNIQ_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "uniq") > BENCH_UNIQ_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "uniq")
        if not COREUTILS_UNIQ.exists():
            build_coreutils_utility(ROOT, "uniq")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_uniq(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_UNIQ_DLL, args, cwd, input_data=input_data)


def run_system_uniq(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_UNIQ, "uniq", args, cwd, input_data=input_data)


def assert_uniq_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_uniq(args, cwd, input_data=input_data)
    bench = run_bench_uniq(args, cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench)


@pytest.mark.parametrize(
    "payload",
    [
        b"",
        b"a\na\n",
        b"a\na",
        b"a\nb",
        b"a\na\nb",
        b"b\na\na\n",
        b"a\nb\nc\n",
    ],
)
def test_default_adjacent_duplicate_suppression_matches_coreutils(payload: bytes) -> None:
    # upstream: coreutils/tests/uniq/uniq.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_uniq_parity([], cwd, input_data=payload)


def test_file_input_matches_coreutils() -> None:
    # upstream: coreutils/tests/uniq/uniq.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"a\na\nb\n")

        assert_uniq_parity(["input.txt"], cwd)


def test_dash_input_and_stdout_output_operand_match_coreutils() -> None:
    # upstream: coreutils/tests/uniq/uniq.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_uniq_parity(["-", "-"], cwd, input_data=b"x\nx\ny\n")


def test_count_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/uniq/uniq.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_uniq_parity(["-c"], cwd, input_data=b"a\na\nb\n")


def test_repeated_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/uniq/uniq.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_uniq_parity(["--repeated"], cwd, input_data=b"a\na\nb\nc\nc\n")


def test_unique_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/uniq/uniq.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_uniq_parity(["-u"], cwd, input_data=b"a\na\nb\nc\nc\nd\n")


def test_repeated_and_unique_together_suppress_output_matches_coreutils() -> None:
    # upstream: coreutils/tests/uniq/uniq.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_uniq_parity(["-d", "-u"], cwd, input_data=b"a\na\nb\n")


def test_ignore_case_matches_coreutils() -> None:
    # upstream: coreutils/tests/uniq/uniq.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_uniq_parity(["--ignore-case"], cwd, input_data=b"A\na\nB\nb\n")


def test_nul_byte_is_not_a_line_delimiter_matches_coreutils() -> None:
    # upstream: coreutils/tests/uniq/uniq.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_uniq_parity([], cwd, input_data=b"a\x00a\na\n")


def test_missing_file_with_space_operand_quotes_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/uniq/uniq.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["a b"]
        ref = run_system_uniq(args, cwd)
        bench = run_bench_uniq(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


# A shell-special missing path must use GNU's quoted diagnostic.
def test_missing_file_with_equals_operand_quotes_diagnostic_matches_coreutils() -> None:
    # upstream: none - Covers byte-exact quoting for a missing equals-containing
    # operand not exercised by GNU uniq tests.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["a="]
        ref = run_system_uniq(args, cwd)
        bench = run_bench_uniq(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


def test_directory_operand_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/read-errors.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        directory = cwd / "dir"
        directory.mkdir()
        args = ["dir"]
        ref = run_system_uniq(args, cwd)
        bench = run_bench_uniq(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


def test_invalid_short_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-x"]
        ref = run_system_uniq(args, cwd)
        bench = run_bench_uniq(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


def test_extra_operand_reports_failure() -> None:
    # upstream: coreutils/tests/uniq/uniq.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"a\n")
        args = ["input.txt", "-", "extra"]
        ref = run_system_uniq(args, cwd)
        bench = run_bench_uniq(args, cwd)
        assert_result_matches_reference(ref, bench, stderr_mode="presence")


def test_traditional_skip_char_operand_reports_benchmark_diagnostic() -> None:
    # upstream: none - Documents this benchmark slice rejecting obsolete GNU +N syntax instead of
    # upstream-reason: treating it as an input file name.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "+1").write_bytes(b"would-be-file\n")

        stdout, stderr, exit_code = run_bench_uniq(["+1"], cwd, input_data=b"abc\n")

    assert stdout == b""
    assert stderr == (
        b"uniq: traditional skip-character operand '+1' is not supported by this benchmark\n"
    )
    assert exit_code == 1


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_uniq(args, cwd)
            bench = run_bench_uniq(args, cwd)
            assert_requested_message_behavior(ref, bench)


def test_deferred_uniq_regressions_placeholder() -> None:
    # Not ported yet: field skipping, character skipping, and check-char width
    # options, including 123-124 coverage, are not implemented in the
    # benchmark schema or semantics.
    # Not ported yet: `-z`/`--zero-terminated` needs NUL-delimited record
    # parsing and output delimiters; this slice models newline-delimited lines.
    # Not ported yet: `-D`, `--all-repeated`, and `--group` delimiter modes,
    # including variants from `triple_test`, are unimplemented GNU extensions.
    # Not ported yet: non-`-` OUTPUT operands need a World/IO write-and-
    # truncate file-content effect, which BenchIO.IO does not currently expose.
    # Not ported yet: locale-sensitive collation and multibyte character
    # width/counting behavior is outside the deterministic C-locale slice.
    # Not ported yet: it targets huge `-f` skip counts, an unimplemented option.
    # Not ported yet: /dev/full, closed-pipe, and injected EIO behavior require
    # write-failure and fault-injection surfaces not modeled by the runner.
    # upstream: coreutils/tests/uniq/uniq.pl
    # upstream: coreutils/tests/uniq/uniq-collate.sh
    # upstream: coreutils/tests/uniq/uniq-perf.sh
    # upstream: coreutils/tests/misc/io-errors.sh
    # upstream: coreutils/tests/misc/option-aliases.sh
    # upstream: coreutils/tests/misc/write-errors.sh
    pytest.skip("requires deferred uniq options or unmodeled host effects")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", UNIQ_VERIFY_TARGETS)
def test_uniq_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
