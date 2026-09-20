"""Check echo option and escape parity against GNU coreutils and verify proof surface."""

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

BENCH_ECHO_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "echo_bench.dll")
COREUTILS_ECHO = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "echo")
ECHO_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "echo" / "EchoCore.dfy",
    ROOT / "bench" / "utils" / "echo" / "EchoProof.dfy",
    ROOT / "bench" / "utils" / "echo" / "Echo.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_echo_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_ECHO_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "echo") > BENCH_ECHO_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "echo")
        if not COREUTILS_ECHO.exists():
            build_coreutils_utility(ROOT, "echo")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_echo(
    args: list[str],
    cwd: Path,
    *,
    env: dict[str, str] | None = None,
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_ECHO_DLL, args, cwd, env=env)


def run_system_echo(
    args: list[str],
    cwd: Path,
    *,
    env: dict[str, str] | None = None,
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_ECHO, "echo", args, cwd, env=env)


def assert_echo_parity(args: list[str], *, env: dict[str, str] | None = None) -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_echo(args, cwd, env=env)
        bench = run_bench_echo(args, cwd, env=env)
        assert_result_matches_reference(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        [],
        ["hello", "world"],
        ["-n", "hello", "world"],
        ["-e", "a\\nb"],
        ["-E", "a\\nb"],
        ["-ne", "a\\nb"],
        ["-nE", "a\\nb"],
        ["-eE", "a\\nb"],
        ["-En", "a\\nb"],
        ["--", "foo"],
        ["-n", "-e", "--", "foo\\n"],
        ["-", "value"],
        ["-/"],
    ],
)
def test_basic_option_and_operand_parity(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/echo.sh
    assert_echo_parity(args)


@pytest.mark.parametrize(
    "args",
    [
        ["-n", "-e", "\\x1b\\n\\e\\n\\33\\n\\033\\n\\0033\\n"],
        ["-n", "-e", "\\x\\n"],
        ["-e", "foo\\n\\cbar"],
        ["-n", "-e", "\\a\\b\\e\\f\\n\\r\\t\\v"],
        ["-n", "-e", "\\x4a\\x4b\\x4c\\x4d\\x4e\\x4f\\x4A\\x4B\\x4C\\x4D\\x4E\\x4F"],
        ["-n", "-e", "\\\\"],
    ],
)
def test_echo_sh_escape_regressions_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/echo.sh
    assert_echo_parity(args)


# Unicode literals are UTF-8 while numeric escapes emit exactly one raw byte.
@pytest.mark.parametrize(
    "args",
    [
        ["한글", "é", "😀"],
        ["-e", "한\\né\\😀"],
        ["-ne", "\\0377\\0400\\0777\\400\\777"],
    ],
)
def test_text_and_numeric_escape_byte_boundaries(args: list[str]) -> None:
    # upstream: none - repository-local GNU parity regression
    assert_echo_parity(args)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_echo(args, cwd)
            bench = run_bench_echo(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        ["-n", "-E", "foo\\n"],
        ["-nE", "foo"],
        ["-E", "-n", "foo"],
        ["--version"],
        ["--help"],
    ],
)
def test_posixly_correct_echo_sh_regressions_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/echo.sh
    env = parity_env()
    env["POSIXLY_CORRECT"] = "1"
    assert_echo_parity(args, env=env)


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", ECHO_VERIFY_TARGETS)
def test_echo_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
