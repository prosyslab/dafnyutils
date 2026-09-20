"""Check wc count-format parity against GNU coreutils and verify proof surface."""

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

BENCH_WC_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "wc_bench.dll")
COREUTILS_WC = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "wc")
WC_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "wc" / "WcCore.dfy",
    ROOT / "bench" / "utils" / "wc" / "WcProof.dfy",
    ROOT / "bench" / "utils" / "wc" / "Wc.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_wc_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_WC_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "wc") > BENCH_WC_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "wc")
        if not COREUTILS_WC.exists():
            build_coreutils_utility(ROOT, "wc")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_wc(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_WC_DLL, args, cwd, input_data=input_data)


def run_system_wc(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_WC, "wc", args, cwd, input_data=input_data)


def assert_wc_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_wc(args, cwd, input_data=input_data)
    bench = run_bench_wc(args, cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench)


def test_stdin_default_counts_match_coreutils_pipe_format() -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_wc_parity([], cwd, input_data=b"stdin words\n")


def test_single_file_default_counts_match_coreutils() -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"a b\ncd")

        assert_wc_parity(["input.txt"], cwd)


def test_multiple_files_print_total_match_coreutils() -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "first.txt").write_bytes(b"alpha beta\n")
        _ = (cwd / "second.txt").write_bytes(b"x\n\ny z\n")

        assert_wc_parity(["first.txt", "second.txt"], cwd)


@pytest.mark.parametrize(
    "args",
    [
        ["-l", "input.txt"],
        ["-w", "input.txt"],
        ["-c", "input.txt"],
        ["-m", "input.txt"],
        ["-lw", "input.txt"],
        ["--lines", "--words", "--bytes", "input.txt"],
    ],
)
def test_selected_count_options_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"one two\nthree\n")

        assert_wc_parity(args, cwd)


def test_dash_operands_consume_stdin_once_match_coreutils() -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_wc_parity(["-", "-"], cwd, input_data=b"only once\n")


def test_file_and_stdin_operand_total_match_coreutils() -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "tail.txt").write_bytes(b"tail\n")

        assert_wc_parity(["-lwm", "-", "tail.txt"], cwd, input_data=b"head\nline\n")


def test_missing_file_still_reports_total_for_multiple_operands() -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"ok\n")

        assert_wc_parity(["missing.txt", "input.txt"], cwd)


def test_single_count_with_stdin_and_missing_operand_uses_coreutils_width() -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)

        assert_wc_parity(["-w", "-", "missing.txt"], cwd, input_data=b"\x00\x01")


def test_missing_file_with_space_operand_quotes_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["a b"]
        ref = run_system_wc(args, cwd)
        bench = run_bench_wc(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


def test_max_line_length_tabs_match_coreutils() -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"a\tb\n123456789\n")

        assert_wc_parity(["-L", "input.txt"], cwd)


def test_max_line_length_ignores_nonprinting_bytes_match_coreutils() -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.bin").write_bytes(b"?\x00\x00")

        assert_wc_parity(["-L", "input.bin"], cwd)


def test_binary_word_classification_matches_coreutils() -> None:
    # upstream: coreutils/tests/wc/wc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        payload = bytes(list(range(57, 256)) + list(range(0, 154)))[:353]
        _ = (cwd / "input.bin").write_bytes(payload)

        assert_wc_parity(["input.bin"], cwd)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_wc(args, cwd)
            bench = run_bench_wc(args, cwd)
            assert_requested_message_behavior(ref, bench)


def test_deferred_wc_regressions_placeholder() -> None:
    # Not ported yet: these depend on unimplemented `--files0-from` parsing,
    # locale-sensitive word boundaries, concurrent output atomicity, procfs
    # behavior, hardware-specific debug paths, or unsupported `--total=` modes.
    # upstream: coreutils/tests/wc/wc-files0.sh
    # upstream: coreutils/tests/wc/wc-files0-from.pl
    # upstream: coreutils/tests/wc/wc-cpu.sh
    # upstream: coreutils/tests/wc/wc-nbsp.sh
    # upstream: coreutils/tests/wc/wc-parallel.sh
    # upstream: coreutils/tests/wc/wc-proc.sh
    # upstream: coreutils/tests/wc/wc-total.sh
    pytest.skip("requires unimplemented wc options or platform-specific fixtures")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", WC_VERIFY_TARGETS)
def test_wc_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
