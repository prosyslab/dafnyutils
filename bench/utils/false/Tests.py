"""Check false exit parity against GNU coreutils and verify its Dafny proof surface."""

import fcntl
import os
import subprocess
import tempfile
from pathlib import Path

import pytest

from evaluation.submission.candidate_execution import run_candidate
from tools.bench.bench_test_support import (
    BENCH_COMMAND_TIMEOUT_SEC,
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

BENCH_FALSE_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "false_bench.dll")
COREUTILS_FALSE = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "false")
FALSE_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "false" / "FalseCore.dfy",
    ROOT / "bench" / "utils" / "false" / "FalseProof.dfy",
    ROOT / "bench" / "utils" / "false" / "False.dfy",
]


def build_bench_false() -> None:
    build_bench_utility(ROOT, "false")


def build_coreutils_false() -> None:
    build_coreutils_utility(ROOT, "false")


def latest_bench_false_source_mtime() -> float:
    sources = [
        ROOT / "bench" / "core" / "IO.dfy",
        ROOT / "bench" / "core" / "IOExtern.cs",
    ]
    sources.extend((ROOT / "bench" / "core").glob("*.dfy"))
    sources.extend((ROOT / "bench" / "utils" / "false").glob("*.dfy"))
    newest = 0.0
    for source in sources:
        try:
            newest = max(newest, source.stat().st_mtime)
        except FileNotFoundError:
            continue
    return newest


@pytest.fixture(scope="session", autouse=True)
def build_false_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_FALSE_DLL.exists()
            or latest_bench_false_source_mtime() > BENCH_FALSE_DLL.stat().st_mtime
        ):
            build_bench_false()
        if not COREUTILS_FALSE.exists():
            build_coreutils_false()
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


def run_bench_false(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    completed = run_candidate(
        BENCH_FALSE_DLL,
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


def run_system_false(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    completed = subprocess.run(
        ["false", *args],
        executable=str(COREUTILS_FALSE),
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def verify_false_module(target: Path) -> None:
    run_dafny_verify(target)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    assert_result_matches_reference(ref_result, bench_result)


def test_run_mode_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/false-status.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_false([], cwd)
        bench = run_bench_false([], cwd)
        assert_same_result(ref, bench)


def test_ignored_operands_match_coreutils() -> None:
    # upstream: coreutils/tests/misc/false-status.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["alpha", "beta"]
        ref = run_system_false(args, cwd)
        bench = run_bench_false(args, cwd)
        assert_same_result(ref, bench)


def test_option_like_operand_is_ignored_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-/"]
        ref = run_system_false(args, cwd)
        bench = run_bench_false(args, cwd)
        assert_same_result(ref, bench)


# A trailing option separator remains a second user argument, so special output is suppressed.
@pytest.mark.parametrize("args", [["--help", "--"], ["--version", "--"]])
def test_raw_argument_count_with_trailing_separator_matches_coreutils(
    args: list[str],
) -> None:
    # upstream: coreutils/tests/misc/false-status.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_false(args, cwd)
        bench = run_bench_false(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    "args",
    [["--help"], ["--version"], ["--help", "x"], ["x", "--version"]],
)
def test_help_version_and_mixed_arguments_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/false-status.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_false(args, cwd)
        bench = run_bench_false(args, cwd)
        assert_requested_message_behavior(ref, bench)


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", FALSE_VERIFY_TARGETS)
def test_false_verify_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_false_module(target)
