"""Check factor parity against GNU coreutils and verify its Dafny proof surface."""

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

BENCH_FACTOR_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "factor_bench.dll")
COREUTILS_FACTOR = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "factor")
FACTOR_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "factor" / "FactorCore.dfy",
    ROOT / "bench" / "utils" / "factor" / "FactorProof.dfy",
    ROOT / "bench" / "utils" / "factor" / "Factor.dfy",
]


def build_bench_factor() -> None:
    build_bench_utility(ROOT, "factor")


def build_coreutils_factor() -> None:
    build_coreutils_utility(ROOT, "factor")


def latest_bench_factor_source_mtime() -> float:
    sources = [
        ROOT / "bench" / "core" / "IO.dfy",
        ROOT / "bench" / "core" / "IOExtern.cs",
    ]
    sources.extend((ROOT / "bench" / "core").glob("*.dfy"))
    sources.extend((ROOT / "bench" / "utils" / "factor").glob("*.dfy"))
    newest = 0.0
    for source in sources:
        try:
            newest = max(newest, source.stat().st_mtime)
        except FileNotFoundError:
            continue
    return newest


@pytest.fixture(scope="session", autouse=True)
def build_factor_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_FACTOR_DLL.exists()
            or latest_bench_factor_source_mtime() > BENCH_FACTOR_DLL.stat().st_mtime
        ):
            build_bench_factor()
        if not COREUTILS_FACTOR.exists():
            build_coreutils_factor()
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


def run_bench_factor(
    args: list[str], cwd: Path, *, input_data: bytes = b""
) -> tuple[bytes, bytes, int]:
    completed = run_candidate(
        BENCH_FACTOR_DLL,
        args,
        cwd=cwd,
        check=False,
        input=input_data,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def run_system_factor(
    args: list[str], cwd: Path, *, input_data: bytes = b""
) -> tuple[bytes, bytes, int]:
    completed = subprocess.run(
        ["factor", *args],
        executable=str(COREUTILS_FACTOR),
        cwd=cwd,
        check=False,
        input=input_data,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def verify_factor_module(target: Path) -> None:
    run_dafny_verify(target)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    assert_result_matches_reference(ref_result, bench_result)


@pytest.mark.parametrize(
    "args",
    [["3000", "--exponents"], ["--exponents", "3000"]],
)
def test_exponents_and_permuted_operands_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/factor/factor.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_factor(args, cwd)
        bench = run_bench_factor(args, cwd)
        assert_same_result(ref, bench)


def test_leading_plus_and_spaces_match_coreutils() -> None:
    # upstream: coreutils/tests/factor/factor.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["  +7", "0009"]
        ref = run_system_factor(args, cwd)
        bench = run_bench_factor(args, cwd)
        assert_same_result(ref, bench)


def test_stdin_tokenization_matches_coreutils() -> None:
    # upstream: coreutils/tests/factor/factor.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        stdin_payload = b"9\t+7\n0008 1\n"
        ref = run_system_factor([], cwd, input_data=stdin_payload)
        bench = run_bench_factor([], cwd, input_data=stdin_payload)
        assert_same_result(ref, bench)


def test_invalid_token_continues_matches_coreutils() -> None:
    # upstream: coreutils/tests/factor/factor.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["9", "a", "7"]
        ref = run_system_factor(args, cwd)
        bench = run_bench_factor(args, cwd)
        assert_same_result(ref, bench)


def test_invalid_token_diagnostic_quoting_matches_coreutils() -> None:
    # upstream: coreutils/tests/factor/factor.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = [r"a\b", "a'b"]
        ref = run_system_factor(args, cwd)
        bench = run_bench_factor(args, cwd)
        assert_same_result(ref, bench)


def test_invalid_stdin_byte_diagnostic_quoting_matches_coreutils() -> None:
    # upstream: coreutils/tests/factor/factor.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        stdin_payload = b"@\\@\n@\xe5@\n@\r@\n@\f@\na\x00ignored\n \x00ignored\na\x00b c"
        ref = run_system_factor([], cwd, input_data=stdin_payload)
        bench = run_bench_factor([], cwd, input_data=stdin_payload)
        assert_same_result(ref, bench)


def test_exponent_format_matches_coreutils() -> None:
    # upstream: coreutils/tests/factor/factor.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-h", "3000"]
        ref = run_system_factor(args, cwd)
        bench = run_bench_factor(args, cwd)
        assert_same_result(ref, bench)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_factor(args, cwd)
            bench = run_bench_factor(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize("args", [["--bogus"], ["-x"]], ids=["unknown-long", "unknown-short"])
def test_invalid_option_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_factor(args, cwd)
        bench = run_bench_factor(args, cwd)
        assert_same_result(ref, bench)


def test_deferred_factor_regressions_placeholder() -> None:
    # Not ported yet: these rely on concurrent pipelines and the very expensive
    # generated checksum template flow, neither of which fits the current
    # single-command parity harness.
    # upstream: coreutils/tests/factor/factor-parallel.sh
    # upstream: coreutils/tests/factor/run.sh
    pytest.skip("requires concurrent pipeline fixtures and expensive-range gating")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", FACTOR_VERIFY_TARGETS, ids=lambda path: path.name)
def test_factor_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_factor_module(target)
