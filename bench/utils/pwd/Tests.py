"""Check pwd parity against GNU coreutils and verify its Dafny proof surface."""

import fcntl
import re
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

BENCH_PWD_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "pwd_bench.dll")
COREUTILS_PWD = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "pwd")
PWD_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "pwd" / "PwdCore.dfy",
    ROOT / "bench" / "utils" / "pwd" / "PwdProof.dfy",
    ROOT / "bench" / "utils" / "pwd" / "Pwd.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_pwd_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_PWD_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "pwd") > BENCH_PWD_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "pwd")
        if not COREUTILS_PWD.exists():
            build_coreutils_utility(ROOT, "pwd")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_pwd(args: list[str], cwd: Path, *, env: dict[str, str]) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_PWD_DLL, args, cwd, env=env)


def run_system_pwd(args: list[str], cwd: Path, *, env: dict[str, str]) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_PWD, "pwd", args, cwd, env=env)


def verify_pwd_module(target: Path) -> None:
    run_dafny_verify(target)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    def normalize_stderr(stderr: bytes) -> bytes:
        text = stderr.decode("utf-8")
        text = text.replace("‘", "'").replace("’", "'")
        text = re.sub(
            r"Try '.*pwd --help' for more information\.\n",
            "Try 'pwd --help' for more information.\n",
            text,
        )
        return text.encode("utf-8")

    assert_result_matches_reference(
        ref_result,
        bench_result,
        stderr_normalizer=normalize_stderr,
    )


def logical_pwd(cwd: Path) -> str:
    return f"{cwd.as_posix()}/"


def base_env(
    cwd: Path,
    *,
    posixly_correct: bool = False,
    include_pwd: bool = True,
) -> dict[str, str]:
    env = parity_env()
    env.pop("PWD", None)
    if include_pwd:
        env["PWD"] = logical_pwd(cwd)
    if posixly_correct:
        env["POSIXLY_CORRECT"] = "1"
    return env


def test_default_mode_is_physical() -> None:
    # upstream: coreutils/tests/pwd/pwd-option.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        env = base_env(cwd)
        ref = run_system_pwd([], cwd, env=env)
        bench = run_bench_pwd([], cwd, env=env)
        assert_same_result(ref, bench)


def test_posixly_correct_defaults_to_logical() -> None:
    # upstream: coreutils/tests/pwd/pwd-option.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        env = base_env(cwd, posixly_correct=True)
        ref = run_system_pwd([], cwd, env=env)
        bench = run_bench_pwd([], cwd, env=env)
        assert_same_result(ref, bench)


@pytest.mark.parametrize("args", [["-P"], ["--physical"]], ids=["short", "long"])
def test_physical_option_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/pwd/pwd-option.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        env = base_env(cwd)
        ref = run_system_pwd(args, cwd, env=env)
        bench = run_bench_pwd(args, cwd, env=env)
        assert_same_result(ref, bench)


@pytest.mark.parametrize("args", [["-L"], ["--logical"]], ids=["short", "long"])
def test_logical_option_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/pwd/pwd-option.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        env = base_env(cwd)
        ref = run_system_pwd(args, cwd, env=env)
        bench = run_bench_pwd(args, cwd, env=env)
        assert_same_result(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        ["-L", "-P"],
        ["-P", "-L"],
        ["-LP"],
        ["-PL"],
    ],
)
def test_last_option_wins_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/pwd/pwd-option.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        env = base_env(cwd)
        ref = run_system_pwd(args, cwd, env=env)
        bench = run_bench_pwd(args, cwd, env=env)
        assert_same_result(ref, bench)


def test_ignored_operands_match_coreutils() -> None:
    # upstream: coreutils/tests/pwd/pwd-option.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        env = base_env(cwd)
        args = ["extra", "operand"]
        ref = run_system_pwd(args, cwd, env=env)
        bench = run_bench_pwd(args, cwd, env=env)
        assert_same_result(ref, bench)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        env = base_env(cwd)
        for args in (["--help"], ["--version"]):
            ref = run_system_pwd(args, cwd, env=env)
            bench = run_bench_pwd(args, cwd, env=env)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize(
    "args",
    [["--help", "--version"], ["--version", "--help"]],
)
def test_help_version_precedence_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        env = base_env(cwd)
        ref = run_system_pwd(args, cwd, env=env)
        bench = run_bench_pwd(args, cwd, env=env)
        assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize("args", [["--bogus"], ["-/"]], ids=["unknown-long", "unknown-short"])
def test_parse_errors_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        env = base_env(cwd, include_pwd=False)
        ref = run_system_pwd(args, cwd, env=env)
        bench = run_bench_pwd(args, cwd, env=env)
        assert_same_result(ref, bench)


def test_deferred_pwd_long_path_placeholder() -> None:
    # Not ported yet: the upstream case relies on stepwise deep-directory
    # traversal past PATH_MAX, while the current Python runner hands subprocess
    # an already-materialized cwd path and needs a dedicated deep-chdir helper.
    # upstream: coreutils/tests/pwd/pwd-long.sh
    pytest.skip("requires a stepwise deep-directory cwd helper")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", PWD_VERIFY_TARGETS, ids=lambda path: path.name)
def test_pwd_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_pwd_module(target)
