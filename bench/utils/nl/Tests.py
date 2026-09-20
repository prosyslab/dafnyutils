"""Check nl line-numbering parity against GNU coreutils and verify proof surface."""

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

BENCH_NL_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "nl_bench.dll")
COREUTILS_NL = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "nl")
NL_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "nl" / "NlSchema.dfy",
    ROOT / "bench" / "utils" / "nl" / "NlCore.dfy",
    ROOT / "bench" / "utils" / "nl" / "NlSpec.dfy",
    ROOT / "bench" / "utils" / "nl" / "NlProof.dfy",
    ROOT / "bench" / "utils" / "nl" / "Nl.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_nl_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_NL_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "nl") > BENCH_NL_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "nl")
        if not COREUTILS_NL.exists():
            build_coreutils_utility(ROOT, "nl")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_nl(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_NL_DLL, args, cwd, input_data=input_data)


def run_system_nl(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_NL, "nl", args, cwd, input_data=input_data)


def assert_nl_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_nl(args, cwd, input_data=input_data)
    bench = run_bench_nl(args, cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


@pytest.mark.parametrize(
    "payload",
    [
        b"",
        b"a\n\nb\n",
        b"a\nb",
    ],
)
def test_stdin_default_number_nonempty_lines_match_coreutils(payload: bytes) -> None:
    # upstream: coreutils/tests/misc/nl.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_nl_parity([], Path(tmp_dir), input_data=payload)


def test_file_and_stdin_operands_continue_numbering_match_coreutils() -> None:
    # upstream: coreutils/tests/misc/nl.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "first.txt").write_bytes(b"first\n")
        _ = (cwd / "second.txt").write_bytes(b"second\n")

        assert_nl_parity(["first.txt", "-", "second.txt"], cwd, input_data=b"middle\n\n")


@pytest.mark.parametrize(
    ("args", "payload"),
    [
        (["-b", "a"], b"a\n\nb\n"),
        (["-b", "n"], b"a\n\nb\n"),
        (["-n", "ln"], b"left\n"),
        (["-n", "rz", "-s", ": "], b"a\n\nb\n"),
    ],
)
def test_numbering_modes_formats_and_separator_match_coreutils(
    args: list[str],
    payload: bytes,
) -> None:
    # upstream: coreutils/tests/misc/nl.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_nl_parity(args, Path(tmp_dir), input_data=payload)


def test_missing_file_diagnostic_and_continuation_match_coreutils() -> None:
    # upstream: coreutils/tests/misc/nl.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "present.txt").write_bytes(b"present\n")

        assert_nl_parity(["missing.txt", "present.txt"], cwd)


# A missing filename containing '=' uses GNU's quoted diagnostic form.
def test_missing_file_with_equals_is_quoted_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/nl.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_nl_parity(["a=rw"], Path(tmp_dir))


def test_logical_page_delimiter_reports_benchmark_diagnostic() -> None:
    # upstream: none - Documents this benchmark slice rejecting GNU logical page delimiters until
    # upstream-reason: logical-page semantics are modeled.
    with tempfile.TemporaryDirectory() as tmp_dir:
        stdout, stderr, exit_code = run_bench_nl(
            [],
            Path(tmp_dir),
            input_data=b"before\n\\:\nafter\n",
        )

        assert exit_code == 1
        assert stdout == b""
        assert b"unsupported logical page delimiter" in stderr


@pytest.mark.parametrize("args", [["-b", "q"], ["-n", "bad"]])
def test_invalid_option_values_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/nl.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_nl_parity(args, Path(tmp_dir))


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_nl(args, cwd)
            bench = run_bench_nl(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", NL_VERIFY_TARGETS)
def test_nl_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
