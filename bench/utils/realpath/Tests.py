"""Strict GNU parity checks for realpath traversal and lexical modes."""

import subprocess
from pathlib import Path

import pytest

from tools.execution import run_candidate
from tools.test_support import (
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
UTILITY = "realpath"
PROJECT = ROOT / "bench" / "utils" / UTILITY
KNOWN_FILE = "bench/utils/realpath/benchmark.yaml"


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    """Reuse the already-built pinned GNU and candidate artifacts."""
    reference = coreutils_binary_path(ROOT, ROOT / "_build/coreutils/src" / UTILITY)
    assert reference.is_file(), "build the pinned GNU reference with make build-coreutils"
    candidate = bench_dll_path(ROOT, ROOT / "_build/bench" / f"{UTILITY}_bench.dll")
    assert candidate.is_file(), "build the candidate with make build TASK=realpath"
    return reference, candidate


def assert_parity(executables: tuple[Path, Path], args: list[str]) -> None:
    """Use the existing read-only repository and compare both streams and status."""
    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, args, ROOT)
    actual = run_bench_utility(candidate, args, ROOT)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)


# Normalize lexical paths without requiring any components to exist.
@pytest.mark.integration
@pytest.mark.parametrize(
    "path", ["a//b/../c/./", "../../../../absent", "/", "//", "///a/../../b", ""]
)
def test_missing_permitted_lexical_paths(executables: tuple[Path, Path], path: str) -> None:
    # upstream: coreutils/tests/misc/realpath.sh
    # Port missing-permitted empty input and lexical root/string handling.
    assert_parity(executables, ["-ms", path])


# Compare whole components when generating a relative path.
@pytest.mark.integration
@pytest.mark.parametrize(
    "base,target", [("prefix", "prefixed/1"), ("prefixed", "prefix/1"), ("prefixed", "prefixed/1")]
)
def test_relative_component_boundaries(
    executables: tuple[Path, Path], base: str, target: str
) -> None:
    # upstream: coreutils/tests/misc/realpath.sh
    # Port the three relative string handling assertions.
    assert_parity(executables, ["-ms", f"--relative-to={base}", target])


# Keep absolute results outside the relative base and handle the root exactly.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        ["-sm", "--relative-to=/usr", "/"],
        ["-sm", "--relative-to=/", "/usr"],
        ["-sm", "--relative-base=/usr", "/tmp", "/usr"],
        ["-sm", "--relative-base=/", "--relative-to=/", "/", "/usr"],
        ["-sm", "--relative-base=/usr/local", "--relative-to=/usr", "/usr", "/usr/local"],
    ],
)
def test_relative_base_policy(executables: tuple[Path, Path], args: list[str]) -> None:
    # upstream: coreutils/tests/misc/realpath.sh
    # Port the relative-base, leading '..', and trailing-slash regressions.
    assert_parity(executables, args)


# Reject nondirectory prefixes even when dot components later cancel their spelling.
@pytest.mark.integration
@pytest.mark.parametrize("suffix", ["/./../missing", "/.//", "/./."])
def test_nondirectory_dot_suffix(executables: tuple[Path, Path], suffix: str) -> None:
    # upstream: none - Exercises canonicalize.c suffix_requires_dir_check over a fixed file.
    assert_parity(executables, ["-s", KNOWN_FILE + suffix])


# Existing-only relative directories reject files while -E restores all-but-last policy.
@pytest.mark.integration
@pytest.mark.parametrize("policy", ["-e", "-eE"])
def test_relative_directory_existence_policy(executables: tuple[Path, Path], policy: str) -> None:
    # upstream: coreutils/tests/misc/realpath.sh
    # Port -e relative-to regular-file rejection and the subsequent -E override.
    assert_parity(executables, ["-s", policy, f"--relative-to={KNOWN_FILE}", "."])


# Preserve NUL terminators and operand order across lexical normalization.
@pytest.mark.integration
def test_nul_multiple_operands(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/misc/realpath.sh
    # Adapt the basic -qz check to multiple strip-mode operands.
    assert_parity(executables, ["-smz", ".", "alpha/../beta", "/"])


# Quiet mode still returns failure and continues with following successful paths.
@pytest.mark.integration
def test_quiet_empty_operand_then_success(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/misc/realpath.sh
    # Combine its empty-operand failure and quiet output policy into one ordered scenario.
    assert_parity(executables, ["-smq", "", "."])


# Relative-directory preparation failures remain diagnostic even in quiet mode.
@pytest.mark.integration
def test_quiet_relative_base_failure(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/misc/realpath.sh
    # Port empty relative-base rejection, preserving GNU's unconditional diagnostic.
    assert_parity(executables, ["-smq", "--relative-base=", "."])


# GNU handles trailing slash differently from a terminal dot for a missing last component.
@pytest.mark.integration
@pytest.mark.parametrize("operand", ["missing-realpath-operand/", "missing-realpath-operand/."])
def test_all_but_last_trailing_component(executables: tuple[Path, Path], operand: str) -> None:
    # upstream: none - Source-backed CAN_ALL_BUT_LAST trailing suffix distinction.
    assert_parity(executables, ["-sE", operand])


# Determine effective strip mode after overrides, required values and option termination.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        ["-LmPs", "missing/child"],
        ["--logical", "--no-symlinks", "-m", "a/../b"],
        ["-m", "--strip", "--", "-P"],
        ["-s", "--relative-to", "-P", "-m", "."],
        ["-m", "--relative-t=.", "--stri", "a/../b"],
    ],
)
def test_effective_strip_argument_roles(executables: tuple[Path, Path], args: list[str]) -> None:
    # upstream: none - Source-defined getopt order and relative-option argument roles.
    assert_parity(executables, args)


# Follow symlinks in the default mode before interpreting the parent component.
@pytest.mark.integration
def test_default_physical_parent(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/misc/realpath.sh - symlink resolution.
    assert_parity(executables, ["/bin/.."])


# Resolve lexical parents before expanding symlinks in logical mode.
@pytest.mark.integration
def test_logical_parent(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/misc/realpath.sh - logical symlink resolution.
    assert_parity(executables, ["-L", "/bin/.."])


# Preserve the selected physical or logical mode after later option overrides.
@pytest.mark.integration
@pytest.mark.parametrize("selection", ["-sP", "-PsL", "--physical", "--logical"])
def test_traversal_mode_overrides(executables: tuple[Path, Path], selection: str) -> None:
    # upstream: none - Source-defined last link-selection option takes effect.
    assert_parity(executables, [selection, "/bin/.."])


# Reject a regular file used as a directory during physical traversal.
@pytest.mark.integration
def test_physical_nondirectory_prefix(executables: tuple[Path, Path]) -> None:
    # upstream: none - Native readlink and directory checks preserve ENOTDIR.
    assert_parity(executables, ["-P", KNOWN_FILE + "/child"])


# Permit missing physical components when requested by the existence policy.
@pytest.mark.integration
def test_physical_missing_components(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/misc/realpath.sh - missing-permitted relative paths.
    assert_parity(executables, ["-mP", "missing-realpath-parent/../child"])


# Resolve relative-directory operands with the same physical mode as the target.
@pytest.mark.integration
def test_physical_relative_directory(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/misc/realpath.sh - relative-to directory preparation.
    assert_parity(executables, ["-eP", "--relative-to=/bin", "/usr"])


# Informational exits and malformed option forms preserve exact GNU diagnostics.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        ["-s"],
        ["--help"],
        ["--version"],
        ["--help", "--bad"],
        ["--bad", "--help"],
        ["--version", "--help"],
        ["--zero=value"],
        ["--zer=value"],
        ["--relative-to"],
        ["--c"],
        ["--canonicalize-"],
        ["--r=x"],
        ["--=x"],
        ["-smJ"],
        ["-é"],
    ],
)
def test_cli_information_and_diagnostics(executables: tuple[Path, Path], args: list[str]) -> None:
    # upstream: coreutils/tests/misc/realpath.sh
    # Extend its operand-required assertion with source-defined option-parser outcomes.
    assert_parity(executables, args)


# Report stdout failure exactly when /dev/full rejects the final output.
@pytest.mark.integration
def test_stdout_failure(executables: tuple[Path, Path]) -> None:
    # upstream: none - Required stream-failure coverage using the Linux /dev/full boundary.
    reference, candidate = executables
    with Path("/dev/full").open("wb") as sink:
        expected = subprocess.run(
            [UTILITY, "-sm", "."],
            executable=str(reference),
            cwd=ROOT,
            env=parity_env(),
            stdout=sink,
            stderr=subprocess.PIPE,
            check=False,
            timeout=60,
        )
        actual = run_candidate(candidate, ["-sm", "."], cwd=ROOT, env=parity_env(), stdout=sink)
    assert (expected.returncode, expected.stderr) == (actual.returncode, actual.stderr)


# Verify each utility proof target without depending on executable fixture construction.
@pytest.mark.integration
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename",
    [
        "Proof/RealpathPathProof.dfy",
        "Impl/RealpathCore.dfy",
        "Proof/RealpathProof.dfy",
        "Impl/Realpath.dfy",
    ],
)
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks the complete Dafny utility proof surface.
    run_dafny_verify(PROJECT / filename)
