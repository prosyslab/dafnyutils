"""Check printenv environment-output parity against GNU coreutils and verify proof surface."""

import fcntl
import os
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
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])

BENCH_PRINTENV_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "printenv_bench.dll")
COREUTILS_PRINTENV = coreutils_binary_path(
    ROOT,
    ROOT / "_build" / "coreutils" / "src" / "printenv",
)
PRINTENV_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "printenv" / "PrintenvCore.dfy",
    ROOT / "bench" / "utils" / "printenv" / "PrintenvProof.dfy",
    ROOT / "bench" / "utils" / "printenv" / "Printenv.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_printenv_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_PRINTENV_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "printenv")
            > BENCH_PRINTENV_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "printenv")
        if not COREUTILS_PRINTENV.exists():
            build_coreutils_utility(ROOT, "printenv")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def printenv_env() -> dict[str, str]:
    env = {
        "ALPHA": "one",
        "BETA": "two words",
        "EMPTY": "",
        "-DASH": "dash-value",
        "LC_ALL": "C",
        "LANG": "C",
        "TERM": "dumb",
        "NO_COLOR": "1",
        "CLICOLOR_FORCE": "0",
        "FORCE_COLOR": "0",
        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        "HOME": os.environ.get("HOME", "/tmp"),
        "DOTNET_ROOT": os.environ.get("DOTNET_ROOT", "/usr/share/dotnet"),
    }
    return env


def run_bench_printenv(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_PRINTENV_DLL, args, cwd, env=printenv_env())


def run_system_printenv(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(
        COREUTILS_PRINTENV,
        "printenv",
        args,
        cwd,
        env=printenv_env(),
    )


def normalize_records(separator: bytes):
    def normalize(data: bytes) -> bytes:
        if not data:
            return b""
        records = data.split(separator)
        if records and records[-1] == b"":
            records = records[:-1]
        return b"\n".join(sorted(records))

    return normalize


def normalize_stderr(stderr: bytes) -> bytes:
    text = stderr.decode("utf-8")
    text = text.replace("‘", "'").replace("’", "'")
    text = re.sub(
        r"Try '.*printenv --help' for more information\.\n",
        "Try 'printenv --help' for more information.\n",
        text,
    )
    return text.encode("utf-8")


def assert_printenv_parity(
    args: list[str],
    *,
    stdout_normalizer=None,
) -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printenv(args, cwd)
        bench = run_bench_printenv(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            stdout_normalizer=stdout_normalizer,
            stderr_normalizer=normalize_stderr,
        )


def test_lists_environment_as_name_value_records() -> None:
    # upstream: coreutils/tests/misc/printenv.sh
    assert_printenv_parity([], stdout_normalizer=normalize_records(b"\n"))


def test_null_option_lists_environment_as_nul_records() -> None:
    # upstream: coreutils/tests/env/env-null.sh
    assert_printenv_parity(["-0"], stdout_normalizer=normalize_records(b"\0"))
    assert_printenv_parity(["--null"], stdout_normalizer=normalize_records(b"\0"))


@pytest.mark.parametrize(
    "args",
    [
        ["ALPHA"],
        ["ALPHA", "EMPTY", "BETA"],
        ["ALPHA", "MISSING", "BETA"],
        ["ALPHA", "--help"],
        ["--", "-DASH"],
        ["-0", "ALPHA", "EMPTY", "MISSING", "BETA"],
        ["--null", "ALPHA", "EMPTY"],
    ],
)
def test_named_variables_are_printed_in_operand_order(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/printenv.sh
    assert_printenv_parity(args)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"], ["--help", "ALPHA"]):
            ref = run_system_printenv(args, cwd)
            bench = run_bench_printenv(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize("args", [["--bogus"], ["-/"], ["-x"]])
def test_invalid_options_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    # upstream: coreutils/tests/misc/usage_vs_getopt.sh
    assert_printenv_parity(args)


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", PRINTENV_VERIFY_TARGETS)
def test_printenv_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
