"""Check dirname parity against GNU coreutils and verify its Dafny proof surface."""

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

BENCH_DIRNAME_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "dirname_bench.dll")
COREUTILS_DIRNAME = coreutils_binary_path(
    ROOT,
    ROOT / "_build" / "coreutils" / "src" / "dirname",
)
DIRNAME_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "dirname" / "DirnameCore.dfy",
    ROOT / "bench" / "utils" / "dirname" / "DirnameProof.dfy",
    ROOT / "bench" / "utils" / "dirname" / "Dirname.dfy",
]


def build_bench_dirname() -> None:
    build_bench_utility(ROOT, "dirname")


def build_coreutils_dirname() -> None:
    build_coreutils_utility(ROOT, "dirname")


def latest_bench_dirname_source_mtime() -> float:
    sources = [
        ROOT / "bench" / "core" / "IO.dfy",
        ROOT / "bench" / "core" / "IOExtern.cs",
    ]
    sources.extend((ROOT / "bench" / "core").glob("*.dfy"))
    sources.extend((ROOT / "bench" / "utils" / "dirname").glob("*.dfy"))
    newest = 0.0
    for source in sources:
        try:
            newest = max(newest, source.stat().st_mtime)
        except FileNotFoundError:
            continue
    return newest


@pytest.fixture(scope="session", autouse=True)
def build_dirname_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_DIRNAME_DLL.exists()
            or latest_bench_dirname_source_mtime() > BENCH_DIRNAME_DLL.stat().st_mtime
        ):
            build_bench_dirname()
        if not COREUTILS_DIRNAME.exists():
            build_coreutils_dirname()
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


def run_bench_dirname(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    completed = run_candidate(
        BENCH_DIRNAME_DLL,
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


def run_system_dirname(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    completed = subprocess.run(
        ["dirname", *args],
        executable=str(COREUTILS_DIRNAME),
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


# Unicode directory names must cross the output boundary exactly once as UTF-8.
@pytest.mark.parametrize(
    ("args", "expected"),
    [
        (["/자료/보고서.txt"], "/자료\n"),
        (["/자료/보고서", "/café/été"], "/자료\n/café\n"),
        (["-z", "/자료/보고서"], "/자료\0"),
    ],
)
def test_unicode_operands_preserve_utf8(args: list[str], expected: str, tmp_path: Path) -> None:
    # upstream: none - repository-local GNU parity regression
    ref = run_system_dirname(args, tmp_path)
    bench = run_bench_dirname(args, tmp_path)
    assert bench == ref == (expected.encode("utf-8"), b"", 0)


def verify_dirname_module(target: Path) -> None:
    run_dafny_verify(target)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    def normalize_stderr(stderr: bytes) -> bytes:
        text = stderr.decode("latin1")
        text = re.sub(
            r"Try '.*dirname --help' for more information\.\n",
            "Try 'dirname --help' for more information.\n",
            text,
        )
        return text.encode("latin1")

    assert_result_matches_reference(
        ref_result,
        bench_result,
        stderr_normalizer=normalize_stderr,
    )


def test_missing_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/dirname.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_dirname([], cwd)
        bench = run_bench_dirname([], cwd)
        assert_same_result(ref, bench)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        # Exact help/version text is unnecessary here.
        # We only care that both commands surface the requested output behavior.
        for args in (["--help"], ["--version"]):
            ref = run_system_dirname(args, cwd)
            bench = run_bench_dirname(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize("args", [["--bogus"], ["-x"]], ids=["unknown-long", "unknown-short"])
def test_parse_errors_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_dirname(args, cwd)
        bench = run_bench_dirname(args, cwd)
        assert_same_result(ref, bench)


def test_invalid_short_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-/"]
        ref = run_system_dirname(args, cwd)
        bench = run_bench_dirname(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    "path_arg",
    [
        "d/f",
        "/d/f",
        "d/f/",
        "d/f//",
        "f",
        "/",
        "//",
        "///",
        "//a//",
        "///a///",
        "///a///b",
        "///a//b/",
        "",
    ],
)
def test_path_matrix_matches_coreutils(path_arg: str) -> None:
    # upstream: coreutils/tests/misc/dirname.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = [path_arg]
        ref = run_system_dirname(args, cwd)
        bench = run_bench_dirname(args, cwd)
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
        ref = run_system_dirname(args, cwd)
        bench = run_bench_dirname(args, cwd)
        assert_same_result(ref, bench)


def test_multiple_operands_newline_output_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/dirname.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["a/b", "c/d"]
        ref = run_system_dirname(args, cwd)
        bench = run_bench_dirname(args, cwd)
        assert_same_result(ref, bench)


def test_zero_separated_output_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/dirname.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-z", "/tmp/sample.txt", "plain"]
        ref = run_system_dirname(args, cwd)
        bench = run_bench_dirname(args, cwd)
        assert_same_result(ref, bench)


def test_long_zero_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/usage_vs_getopt.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["--zero", "/tmp/sample.txt", "plain"]
        ref = run_system_dirname(args, cwd)
        bench = run_bench_dirname(args, cwd)
        assert_same_result(ref, bench)


def test_version_write_error_placeholder() -> None:
    # Not ported yet: exact generated help/version text and write failures need
    # stdout redirection or closed stdout support beyond the current runner.
    # upstream: coreutils/tests/help/help-version.sh
    # upstream: coreutils/tests/misc/io-errors.sh
    pytest.skip("requires stdout redirection or closed stdout support in the runner")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", DIRNAME_VERIFY_TARGETS, ids=lambda path: path.name)
def test_dirname_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_dirname_module(target)
