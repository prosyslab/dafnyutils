"""Check logname parity against GNU coreutils and verify its Dafny proof surface."""

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

BENCH_LOGNAME_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "logname_bench.dll")
COREUTILS_LOGNAME = coreutils_binary_path(
    ROOT,
    ROOT / "_build" / "coreutils" / "src" / "logname",
)
LOGNAME_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "logname" / "LognameCore.dfy",
    ROOT / "bench" / "utils" / "logname" / "LognameProof.dfy",
    ROOT / "bench" / "utils" / "logname" / "Logname.dfy",
]


def build_bench_logname() -> None:
    build_bench_utility(ROOT, "logname")


def build_coreutils_logname() -> None:
    build_coreutils_utility(ROOT, "logname")


def latest_bench_logname_source_mtime() -> float:
    sources = [
        ROOT / "bench" / "core" / "IO.dfy",
        ROOT / "bench" / "core" / "IOExtern.cs",
    ]
    sources.extend((ROOT / "bench" / "core").glob("*.dfy"))
    sources.extend((ROOT / "bench" / "utils" / "logname").glob("*.dfy"))
    newest = 0.0
    for source in sources:
        try:
            newest = max(newest, source.stat().st_mtime)
        except FileNotFoundError:
            continue
    return newest


@pytest.fixture(scope="session", autouse=True)
def build_logname_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_LOGNAME_DLL.exists()
            or latest_bench_logname_source_mtime() > BENCH_LOGNAME_DLL.stat().st_mtime
        ):
            build_bench_logname()
        if not COREUTILS_LOGNAME.exists():
            build_coreutils_logname()
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
    env.pop("LOGNAME", None)
    return env


def run_bench_logname(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    completed = run_candidate(
        BENCH_LOGNAME_DLL,
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


def run_system_logname(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    completed = subprocess.run(
        ["logname", *args],
        executable=str(COREUTILS_LOGNAME),
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def verify_logname_module(target: Path) -> None:
    run_dafny_verify(target)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    def normalize_stderr(stderr: bytes) -> bytes:
        text = stderr.decode("utf-8")
        text = text.replace("‘", "'").replace("’", "'")
        text = re.sub(
            r"Try '.*logname --help' for more information\.\n",
            "Try 'logname --help' for more information.\n",
            text,
        )
        return text.encode("utf-8")

    assert_result_matches_reference(
        ref_result,
        bench_result,
        stderr_normalizer=normalize_stderr,
    )


def test_no_login_name_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version-getopt.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_logname([], cwd)
        bench = run_bench_logname([], cwd)
        assert_same_result(ref, bench)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version-getopt.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        # Exact help/version text is unnecessary here.
        # We only care that both commands surface the requested output behavior.
        for args in (["--help"], ["--version"]):
            ref = run_system_logname(args, cwd)
            bench = run_bench_logname(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        ["--help", "AFTER"],
        ["BEFORE", "--help"],
        ["BEFORE", "--help", "AFTER"],
        ["--version", "AFTER"],
        ["BEFORE", "--version"],
        ["BEFORE", "--version", "AFTER"],
    ],
)
def test_help_version_precedence_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/help/help-version-getopt.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_logname(args, cwd)
        bench = run_bench_logname(args, cwd)
        assert_requested_message_behavior(ref, bench)


def test_extra_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version-getopt.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["extra"]
        ref = run_system_logname(args, cwd)
        bench = run_bench_logname(args, cwd)
        assert_same_result(ref, bench)


def test_bad_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version-getopt.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_logname(["--bogus"], cwd)
        bench = run_bench_logname(["--bogus"], cwd)
        assert_same_result(ref, bench)


def test_invalid_short_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-/"]
        ref = run_system_logname(args, cwd)
        bench = run_bench_logname(args, cwd)
        assert_same_result(ref, bench)


def test_version_write_error_placeholder() -> None:
    # Not ported yet: exact generated help/version text and write failures need
    # stdout redirection or closed stdout support beyond the current runner.
    # upstream: coreutils/tests/help/help-version.sh
    # upstream: coreutils/tests/misc/io-errors.sh
    pytest.skip("requires stdout redirection or closed stdout support in the runner")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", LOGNAME_VERIFY_TARGETS, ids=lambda path: path.name)
def test_logname_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_logname_module(target)
