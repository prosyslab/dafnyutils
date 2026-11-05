"""Read-only GNU join oracle cases from the pinned public upstream tests.

All inputs are tiny fixed evaluator fixtures. No test creates, writes, removes,
or cleans up a directory; the runner launches only the already-built targets.
"""

import subprocess
from pathlib import Path

import pytest

from benchmark_tools.execution import run_candidate
from benchmark_tools.test_support import (
    assert_result_matches_reference,
    bench_dll_path,
    coreutils_binary_path,
    evaluation_target_root,
    parity_env,
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])
PROJECT = ROOT / "bench/utils/join"


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    """Require the build stage; do not build or publish workspaces in tests."""
    reference = coreutils_binary_path(ROOT, ROOT / "_build/coreutils/src/join")
    candidate = bench_dll_path(ROOT, ROOT / "_build/bench/join_bench.dll")
    assert reference.is_file(), "run make build-coreutils before oracle tests"
    assert candidate.is_file(), "run make -C bench/utils/join build before oracle tests"
    return reference, candidate


def assert_parity(executables, args, *, input_data=b""):
    reference, candidate = executables
    expected = run_coreutils_utility(reference, "join", args, PROJECT, input_data=input_data)
    actual = run_bench_utility(candidate, args, PROJECT, input_data=input_data)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)


# Exercise one named upstream scenario per row using fixed evaluator-only inputs.
@pytest.mark.integration
@pytest.mark.parametrize(
    "name,args",
    [
        ("1a", ["-a1"]),
        ("1b", ["-a2"]),
        ("1c", ["-a1", "-a2"]),
        ("2b", ["-a1", "-e", ".", "-o", "2.1,2.2,2.3"]),
        ("2c", ["-a1", "-e", ".", "-o", "2.1,2.2,2.3"]),
        ("3a", ["-t:"]),
        ("3b", ["-t", ""]),
        ("3c", ["-t", "\\0"]),
        ("4a", ["-v1"]),
        ("4b", ["-v2"]),
        ("4c", ["-v1"]),
        ("4d", ["-v2"]),
        ("5a", ["-a1", "-e", "-", "-o", "1.1,2.2"]),
        ("5b", ["-a1", "-e", "-", "-o", "1.1,2.2"]),
        ("5d", ["-a1", "-e", "-", "-o", "1.1,2.2"]),
        ("5f", ["-a2", "-e", "-", "-o", "2.2,1.1"]),
        ("6a", ["-e", "-"]),
        ("7a", ["-a1", "-e", ".", "-o", "2.7"]),
        ("8b", ["-a1", "-a2", "-e", ".", "-o", "0,1.2"]),
        ("9a", []),
        ("10a", ["-a1", "-a2", "-e", ".", "-o", "auto"]),
        ("10b", ["-a1", "-a2", "-j3", "-e", ".", "-o", "auto"]),
        ("10c", ["-a1", "-1", "1", "-2", "4", "-e.", "-o", "auto"]),
        ("10d", ["-a2", "-1", "1", "-2", "4", "-e.", "-o", "auto"]),
        ("10e", ["-o", "auto"]),
        ("10f", ["-t,", "-o", "auto"]),
        ("v2-order", ["-v2", "-2", "2"]),
        ("trailing-sp", ["-t:", "-1", "1", "-2", "1"]),
        ("sp-vs-blank", []),
        ("bigfield1", ["-1", "184467440737095516160", "-2", "2"]),
        ("invalid-j", ["-j", "x"]),
        ("chkodr-1", ["--check-order"]),
        ("chkodr-2", ["--nocheck-order"]),
        ("chkodr-3", ["--nocheck-order"]),
        ("chkodr-4", []),
        ("chkodr-5", ["--check-order"]),
        ("chkodr-5b", ["--check-order"]),
        ("chkodr-5c", ["--check-order"]),
        ("chkodr-5d", []),
        ("chkodr-5e", []),
        ("chkodr-6", ["--nocheck-order"]),
        ("chkodr-7", ["-12"]),
        ("chkodr-8", []),
        ("header-1", ["--header"]),
        ("header-2", ["--header", "--check-order"]),
        ("header-3", ["--header", "--check-order"]),
        ("header-4", ["--header", "-o", "0,1.3,2.2"]),
        ("header-5", ["--header"]),
        ("header-6", ["--header", "-a1"]),
        ("z1", ["-z"]),
        ("z2", []),
        ("z3", []),
        ("z4", ["-z"]),
        ("z5", ["-z", "-a1", "-a2"]),
        ("z6", ["-z", "-t", ""]),
        ("duplicate-product", []),
        ("ignore-case", ["-i"]),
        ("nul-disorder", ["--check-order"]),
    ],
)
def test_upstream_scenario(executables, name, args):
    # upstream: coreutils/tests/join/join.pl, named vectors; the final three
    # extend Cartesian duplicates, case folding, and binary order diagnostics.
    assert_parity(executables, [*args, f"fixtures/{name}.left", f"fixtures/{name}.right"])


# Preserve stdin equivalence for either operand using one fixed byte stream.
@pytest.mark.integration
@pytest.mark.parametrize("side", [1, 2])
def test_stdin_operand(executables, side):
    # upstream: coreutils/tests/join/join.pl, triple_test variants of 9a.
    path = "fixtures/9a.right"
    args = ["-", path] if side == 1 else [path, "-"]
    assert_parity(executables, args, input_data=b"a 1\nb 2\n")


# GNU validates options at their position before later help or parse failures.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        [],
        ["one"],
        ["one", "two", "three"],
        ["-", "-"],
        ["--bad"],
        ["-Q"],
        ["-a"],
        ["-zQ"],
        ["-j", "0"],
        ["-j", "-1"],
        ["-j", "-9223372036854775808"],
        ["-a", "3"],
        ["-1", "1", "-1", "2"],
        ["-e", "x", "-e", "y"],
        ["-t", "::"],
        ["-t", "é"],
        ["-t:", "-t,"],
        ["-o", "3.1"],
        ["-o", "0.1"],
        ["-o", "1.0"],
        ["-o", "1.1,,2.1"],
        ["--h"],
        ["--header=x"],
        ["--help"],
        ["--version"],
        ["--help", "-Q"],
        ["--version", "--help"],
        ["-j", "x", "--help"],
        ["-a", "3", "--bad"],
        ["-2", "9223372036854775808", "-e", "x:y", "-", "-"],
        ["-2", "9223372036854775808", "-a1", "-", "-"],
        ["-o", "1.9223372036854775808", "-j1", "-", "-"],
        ["--"],
        ["---"],
        ["--="],
        ["--=x"],
        ["--help=x"],
        ["--version=x"],
        ["--he=x"],
        ["--ignore-case=x"],
        ["--check-order=x"],
        ["--zero-terminated=x"],
        ["-izQ"],
        ["-zia"],
        ["-é"],
        ["-a1=2"],
        ["-j", "0x1"],
    ],
)
def test_argument_or_informational_result(executables, args):
    # upstream: coreutils/tests/join/join.pl invalid-j and join.c main/usage.
    assert_parity(executables, args)


# Opening both files precedes the first data read, including directory failures.
@pytest.mark.integration
@pytest.mark.parametrize("args", [["missing", "-"], [".", "missing"], [".", "-"]])
def test_input_failure(executables, args):
    # upstream: coreutils/tests/misc/read-errors.sh and join.c fopen/get_line.
    assert_parity(executables, args, input_data=b"a\n")


# GNU's legacy -j1 and continued -o forms depend on operand positions.
@pytest.mark.integration
@pytest.mark.parametrize(
    "prefix",
    [
        ["-j1"],
        ["-j2"],
        ["-j1", "2"],
        ["-j2", "2"],
        ["-o", "0", "1.2", "2.2"],
        ["-o", "0", "-a1", "1.2"],
    ],
)
def test_legacy_operand_forms(executables, prefix):
    # upstream: coreutils/src/join.c add_file_name backward compatibility.
    assert_parity(executables, [*prefix, "fixtures/9a.left", "fixtures/9a.right"])


# A single rejected /dev/full write preserves GNU's error and exit status.
@pytest.mark.integration
def test_write_failure(executables):
    # upstream: coreutils/tests/misc/close-stdout.sh and join.c prjoin.
    reference, candidate = executables
    args = ["fixtures/9a.left", "fixtures/9a.right"]
    with Path("/dev/full").open("wb") as full:
        expected = subprocess.run(
            ["join", *args],
            executable=str(reference),
            cwd=PROJECT,
            stdout=full,
            stderr=subprocess.PIPE,
            env=parity_env(),
            check=False,
        )
        actual = run_candidate(
            candidate,
            args,
            cwd=PROJECT,
            stdout=full,
            stderr=subprocess.PIPE,
            env=parity_env(),
            check=False,
        )
    assert actual.returncode == expected.returncode
    assert actual.stderr == expected.stderr


# Verify every task-local proof module independently of the runtime oracle cases.
@pytest.mark.integration
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename",
    [
        "Spec/JoinDataSpec.dfy",
        "Proof/JoinDataProof.dfy",
        "Impl/JoinDataCore.dfy",
        "Impl/JoinPlanCore.dfy",
        "Spec/JoinSpec.dfy",
        "Impl/JoinCore.dfy",
        "Proof/JoinProof.dfy",
        "Impl/Join.dfy",
    ],
)
def test_verify_module(filename):
    run_dafny_verify(
        PROJECT / filename,
        extra_flags=(
            "--isolate-assertions",
            "--boogie=/randomSeed:42",
            "--verification-time-limit:30",
        ),
    )
