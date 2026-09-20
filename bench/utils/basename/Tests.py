"""Check basename parity against GNU coreutils and verify its Dafny proof surface."""

import fcntl
import os
import re
import subprocess
import tempfile
from pathlib import Path

import pytest

from evaluation.submission.candidate_execution import run_candidate
from tools.bench.bench_test_support import (
    BENCH_COMMAND_TIMEOUT_SEC,
    GNULIB_DIRNAME_CLI_PATHS,
    assert_requested_message_behavior,
    assert_result_matches_reference,
    bench_dll_path,
    build_bench_utility,
    build_coreutils_utility,
    coreutils_binary_path,
    evaluation_target_root,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])

BENCH_BASENAME_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "basename_bench.dll")
COREUTILS_BASENAME = coreutils_binary_path(
    ROOT,
    ROOT / "_build" / "coreutils" / "src" / "basename",
)
BASENAME_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "basename" / "BasenameCore.dfy",
    ROOT / "bench" / "utils" / "basename" / "BasenameProof.dfy",
    ROOT / "bench" / "utils" / "basename" / "Basename.dfy",
]


def build_bench_basename() -> None:
    build_bench_utility(ROOT, "basename")


def build_coreutils_basename() -> None:
    build_coreutils_utility(ROOT, "basename")


def latest_bench_basename_source_mtime() -> float:
    sources = [
        ROOT / "bench" / "core" / "IO.dfy",
        ROOT / "bench" / "core" / "IOExtern.cs",
    ]
    sources.extend((ROOT / "bench" / "core").glob("*.dfy"))
    sources.extend((ROOT / "bench" / "utils" / "basename").glob("*.dfy"))
    newest = 0.0
    for source in sources:
        try:
            newest = max(newest, source.stat().st_mtime)
        except FileNotFoundError:
            continue
    return newest


@pytest.fixture(scope="session", autouse=True)
def build_basename_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_BASENAME_DLL.exists()
            or latest_bench_basename_source_mtime() > BENCH_BASENAME_DLL.stat().st_mtime
        ):
            build_bench_basename()
        if not COREUTILS_BASENAME.exists():
            build_coreutils_basename()
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def parity_env() -> dict[str, str]:
    env = os.environ.copy()
    env["LC_ALL"] = "C"
    env["LANG"] = "C"
    env["TZ"] = "UTC0"
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CLICOLOR_FORCE"] = "0"
    env["FORCE_COLOR"] = "0"
    return env


def run_bench_basename(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    completed = run_candidate(
        BENCH_BASENAME_DLL,
        args,
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def run_system_basename(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    completed = subprocess.run(
        ["basename", *args],
        executable=str(COREUTILS_BASENAME),
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def verify_basename_module(target: Path) -> None:
    run_dafny_verify(target)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
    *,
    ignore_stderr_when_exit_nonzero: bool = True,
) -> None:
    def normalize_stderr(stderr: bytes) -> bytes:
        text = stderr.decode("latin1")
        text = re.sub(
            r"Try '.*basename --help' for more information\.\n",
            "Try 'basename --help' for more information.\n",
            text,
        )
        return text.encode("latin1")

    assert_result_matches_reference(
        ref_result,
        bench_result,
        ignore_stderr_when_exit_nonzero=ignore_stderr_when_exit_nonzero,
        stderr_normalizer=normalize_stderr,
    )


# Unicode operands must be encoded as UTF-8 without truncating code points to bytes.
@pytest.mark.parametrize(
    ("args", "expected"),
    [
        (["/자료/보고서.txt"], "보고서.txt\n"),
        (["-a", "/자료/보고서", "/café/été"], "보고서\nété\n"),
        (["-s", ".문서", "/자료/보고서.문서"], "보고서\n"),
    ],
)
def test_unicode_operands_preserve_utf8(args: list[str], expected: str, tmp_path: Path) -> None:
    # upstream: none - repository-local GNU parity regression
    ref = run_system_basename(args, tmp_path)
    bench = run_bench_basename(args, tmp_path)
    assert bench == ref == (expected.encode("utf-8"), b"", 0)


def test_missing_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/basename.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_basename([], cwd)
        bench = run_bench_basename([], cwd)
        assert_same_result(ref, bench)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        # Exact help/version text is unnecessary here.
        # We only care that both commands surface the requested output behavior.
        help_ref = run_system_basename(["--help"], cwd)
        help_bench = run_bench_basename(["--help"], cwd)
        assert_requested_message_behavior(help_ref, help_bench)

        version_ref = run_system_basename(["--version"], cwd)
        version_bench = run_bench_basename(["--version"], cwd)
        assert_requested_message_behavior(version_ref, version_bench)


def test_single_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/basename.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["/tmp/sample.txt"]
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_same_result(ref, bench)


def test_suffix_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/basename.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["/tmp/sample.txt", ".txt"]
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        ["d/f/"],
        ["d/f//"],
        ["/"],
        ["//"],
        ["///"],
        ["///a///"],
        [""],
    ],
)
def test_path_trimming_matrix_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/basename.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    "path_arg",
    GNULIB_DIRNAME_CLI_PATHS,
)
def test_gnulib_test_dirname_rows_match_coreutils(path_arg: str) -> None:
    # upstream: coreutils/gnulib-tests/test-dirname
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = [path_arg]
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        ["fs", "fs"],
        ["fs/", "s/"],
        ["//", "/"],
        ["//", "//"],
        ["fs", ""],
        ["a-a", "-a"],
    ],
)
def test_suffix_edge_cases_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/basename.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_same_result(ref, bench)


def test_multiple_suffix_zero_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/basename.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-a", "-s", ".txt", "-z", "dir/file.txt", "other.txt"]
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        ["--zero", "a"],
        ["--multiple", "a", "b"],
        ["--suffix", "a", "ba"],
    ],
)
def test_long_options_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/usage_vs_getopt.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_same_result(ref, bench)


def test_missing_suffix_option_argument_diagnostic_matches_coreutils() -> None:
    # Fuzzing regression: seed 14 iteration 0, minimized to the single --suffix token.
    # upstream: coreutils/tests/misc/basename.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["--suffix"]
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)


def test_extra_operand_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/basename.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["a", "b", "c"]
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_same_result(ref, bench)


def test_invalid_short_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-/"]
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_same_result(ref, bench)


def test_version_write_error_placeholder() -> None:
    # Not ported yet: exact generated help/version text and write failures need
    # stdout redirection or closed stdout support beyond the current runner.
    # upstream: coreutils/tests/help/help-version.sh
    # upstream: coreutils/tests/misc/io-errors.sh
    pytest.skip("requires stdout redirection or closed stdout support in the runner")


def test_help_precedence_ignores_later_parse_error() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        help_args = ["--help"]
        mixed_args = ["--help", "--bogus"]

        help_ref = run_system_basename(help_args, cwd)
        mixed_ref = run_system_basename(mixed_args, cwd)
        assert mixed_ref == help_ref

        help_bench = run_bench_basename(help_args, cwd)
        mixed_bench = run_bench_basename(mixed_args, cwd)
        assert mixed_bench == help_bench


def test_version_precedence_ignores_later_run_options() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        version_args = ["--version"]
        mixed_args = ["--version", "-s", ".txt", "foo.txt"]

        version_ref = run_system_basename(version_args, cwd)
        mixed_ref = run_system_basename(mixed_args, cwd)
        assert mixed_ref == version_ref

        version_bench = run_bench_basename(version_args, cwd)
        mixed_bench = run_bench_basename(mixed_args, cwd)
        assert mixed_bench == version_bench


def test_suffix_argument_consumption_precedes_version_recovery() -> None:
    # Fuzzing regression: minimal seed 54 iteration 22 reproducer.
    # upstream: coreutils/tests/misc/basename.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-s", "--version", "-s"]
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            stderr_mode="presence",
            ignore_stderr_when_exit_nonzero=False,
        )


def test_abbreviated_suffix_argument_consumption_precedes_version_recovery() -> None:
    # upstream: coreutils/tests/misc/basename.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["--suf", "--version", "--bogus"]
        ref = run_system_basename(args, cwd)
        bench = run_bench_basename(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            stderr_mode="presence",
            ignore_stderr_when_exit_nonzero=False,
        )


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", BASENAME_VERIFY_TARGETS, ids=lambda path: path.name)
def test_basename_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_basename_module(target)
