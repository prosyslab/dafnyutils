"""GNU parity cases for tsort, including coreutils/tests/misc/tsort.pl scenarios."""

import os
import subprocess
import tempfile
from collections.abc import Iterator
from pathlib import Path

import pytest

from benchmark_tools.environment import EVAL_COREUTILS_BIN_ENV
from benchmark_tools.execution import run_candidate
from benchmark_tools.test_support import (
    BENCH_COMMAND_TIMEOUT_SEC,
    assert_result_matches_reference,
    bench_dll_path,
    build_bench_utility,
    build_coreutils_utility,
    coreutils_binary_path,
    evaluation_target_root,
    parity_env,
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])
UTILITY = "tsort"
PROJECT = ROOT / "bench" / "utils" / UTILITY


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    """Build the two targets only for runtime cases; local Make targets use -n0."""
    build_bench_utility(ROOT, UTILITY)
    if not os.environ.get(EVAL_COREUTILS_BIN_ENV):
        build_coreutils_utility(ROOT, UTILITY)
    return (
        coreutils_binary_path(ROOT, ROOT / "_build/coreutils/src" / UTILITY),
        bench_dll_path(ROOT, ROOT / "_build/bench" / f"{UTILITY}_bench.dll"),
    )


def assert_parity(
    executables: tuple[Path, Path],
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> None:
    """Compare a read-only scenario, including stderr on error exits."""
    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, args, cwd, input_data=input_data)
    actual = run_bench_utility(candidate, args, cwd, input_data=input_data)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)


# Preserve GNU's exact ordering for chains, branches and disconnected components.
@pytest.mark.parametrize(
    "input_data",
    [
        pytest.param(b"a b c c d e\ng g\nf g e f\nh h\n", id="posix-1"),
        pytest.param(b"b a\nd c\nz h x h r h\n", id="posix-2"),
        pytest.param(b"a b b c c d d e e f f g\n", id="linear-1"),
        pytest.param(b"a b b c c d d e e f f g\nc x x y y z\n", id="tree-1"),
        pytest.param(b"a b b c c d d e e f f g\nc x x y y z\nf r r s s t\n", id="tree-2"),
    ],
)
def test_upstream_stdin_matches_coreutils(
    executables: tuple[Path, Path], input_data: bytes
) -> None:
    # upstream: coreutils/tests/misc/tsort.pl
    # upstream-reason: ports posix-1, posix-2, linear-1, tree-1 and tree-2.
    assert_parity(executables, [], PROJECT, input_data=input_data)


# Match cycle diagnostics and recovery, odd-token errors and extra-operand rejection.
@pytest.mark.parametrize(
    ("args", "input_files"),
    [
        pytest.param(["f"], {"f": b"t b\nt s\ns t\n"}, id="cycle-1"),
        pytest.param(["f"], {"f": b"t x\nt s\ns t\n"}, id="cycle-2"),
        pytest.param(["-w", "f"], {"f": b"a a\na b\na c\nc a\nb a"}, id="cycle-3"),
        pytest.param(["odd.1"], {"odd.1": b"a\n"}, id="odd"),
        pytest.param(["f", "g"], {"f": b"", "g": b""}, id="only-one"),
    ],
)
def test_upstream_file_matches_coreutils(
    executables: tuple[Path, Path], args: list[str], input_files: dict[str, bytes]
) -> None:
    # upstream: coreutils/tests/misc/tsort.pl
    # upstream-reason: ports cycle-1/2/3, odd and only-one, preserving their input bytes.
    with tempfile.TemporaryDirectory(prefix="tsort-upstream-") as directory:
        cwd = Path(directory)
        for filename, data in input_files.items():
            (cwd / filename).write_bytes(data)
        assert_parity(executables, args, cwd)


# Check token boundaries, duplicate edges, byte ordering and FIFO release order.
@pytest.mark.parametrize(
    "input_data",
    [
        pytest.param(b"", id="empty"),
        pytest.param(b" \t\n \n", id="whitespace-only"),
        pytest.param(b"a a", id="self-pair"),
        pytest.param(b"z z a a z z", id="isolated-vertices"),
        pytest.param(b"a b a b b c", id="duplicate-edge"),
        pytest.param(b"a b a z", id="reverse-adjacency"),
        pytest.param(b"a b c d", id="fifo-not-priority-queue"),
        pytest.param(b" \ta\tb\n\tb c \n", id="mixed-delimiters"),
        pytest.param(b"a\rb c", id="carriage-return-in-name"),
        pytest.param(b"a\vb c", id="vertical-tab-in-name"),
        pytest.param(b"a\fb c", id="form-feed-in-name"),
        pytest.param(b"a\x00suffix b a c", id="nul-terminated-name"),
        pytest.param(b"\xff \xff \x80 \x80 a a", id="unsigned-byte-order"),
        pytest.param(b"a", id="odd-without-newline"),
        pytest.param(b"a b c", id="odd-after-complete-pair"),
        pytest.param(b"a b b a c d", id="cycle-and-independent-chain"),
        pytest.param(b"a b a b b a", id="cycle-with-duplicate-edge"),
    ],
)
def test_input_boundary_matches_coreutils(
    executables: tuple[Path, Path], input_data: bytes
) -> None:
    # upstream: none - Adds tsort-specific byte, graph and queue boundary cases.
    # upstream-reason: parity.
    assert_parity(executables, [], PROJECT, input_data=input_data)


@pytest.fixture(scope="module")
def cli_workdir() -> Iterator[Path]:
    """Share one small input file across the read-only CLI cases."""
    with tempfile.TemporaryDirectory(prefix="tsort-cli-") as directory:
        cwd = Path(directory)
        (cwd / "f").write_bytes(b"t b\nt s\ns t\n")
        yield cwd


# Match option parsing, standard-input selection and file error diagnostics.
@pytest.mark.parametrize(
    "args",
    [
        pytest.param(["--help"], id="help"),
        pytest.param(["--version"], id="version"),
        pytest.param(["--he"], id="abbreviated-help"),
        pytest.param(["--ver"], id="abbreviated-version"),
        pytest.param(["--bad"], id="unknown-long-option"),
        pytest.param(["--=x"], id="ambiguous-empty-long-option"),
        pytest.param(["-x"], id="unknown-short-option"),
        pytest.param(["-é"], id="non-ascii-short-option"),
        pytest.param(["--help=value"], id="unexpected-help-value"),
        pytest.param(["--version=value"], id="unexpected-version-value"),
        pytest.param(["--help", "--version"], id="help-before-version"),
        pytest.param(["--version", "--help"], id="version-before-help"),
        pytest.param(["--help", "--bad"], id="help-before-error"),
        pytest.param(["--bad", "--help"], id="error-before-help"),
        pytest.param(["-w"], id="legacy-no-op"),
        pytest.param(["-wx"], id="invalid-option-after-no-op"),
        pytest.param(["-"], id="explicit-stdin"),
        pytest.param(["--", "-"], id="stdin-after-delimiter"),
        pytest.param(["f"], id="file-input"),
        pytest.param(["f", "--help"], id="option-after-operand"),
        pytest.param(["missing-input"], id="missing-file"),
        pytest.param([""], id="empty-filename"),
        pytest.param(["."], id="directory-read-error"),
        pytest.param(["--", "--help"], id="option-like-filename"),
    ],
)
def test_cli_matches_coreutils(
    executables: tuple[Path, Path], cli_workdir: Path, args: list[str]
) -> None:
    # upstream: none - Adds CLI precedence, input selection and file error parity.
    # upstream-reason: parity.
    assert_parity(executables, args, cli_workdir, input_data=b"a b a c\n")


# Extra-operand diagnostics quote special characters using GNU's argument quoting.
@pytest.mark.parametrize("operand", ["a'b", 'a"b', "a\nb", "a\tb", "a\\b", "a b"])
def test_quoted_extra_operand_matches_coreutils(
    executables: tuple[Path, Path], operand: str
) -> None:
    # upstream: none - Adds GNU argument-quoting parity.
    # upstream-reason: parity.
    assert_parity(executables, ["-", operand], PROJECT)


# Missing-file diagnostics quote pathnames containing shell-sensitive or non-ASCII bytes.
@pytest.mark.parametrize("filename", ["a'b", 'a"b', "a\nb", "a\tb", "a\\b", "a b", "é"])
def test_quoted_missing_file_matches_coreutils(
    executables: tuple[Path, Path], filename: str
) -> None:
    # upstream: none - Adds GNU file-error path quoting parity as in link's missing-source cases.
    # upstream-reason: parity.
    assert_parity(executables, ["missing-" + filename], PROJECT)


# A failed stdout write must report GNU's diagnostic and failure status.
def test_full_stdout_matches_coreutils(executables: tuple[Path, Path]) -> None:
    # upstream: none - Covers the required failed-write boundary with /dev/full.
    # upstream-reason: parity.
    reference, candidate = executables
    with Path("/dev/full").open("wb", buffering=0) as output:
        expected = subprocess.run(
            [UTILITY],
            executable=reference,
            cwd=PROJECT,
            input=b"a b\n",
            stdout=output,
            stderr=subprocess.PIPE,
            env=parity_env(),
            timeout=BENCH_COMMAND_TIMEOUT_SEC,
            check=False,
        )
        actual = run_candidate(
            candidate,
            [],
            cwd=PROJECT,
            input=b"a b\n",
            stdout=output,
            stderr=subprocess.PIPE,
            env=parity_env(),
            timeout=BENCH_COMMAND_TIMEOUT_SEC,
        )
    assert expected.returncode == 1
    assert (actual.stderr, actual.returncode) == (expected.stderr, expected.returncode)


@pytest.fixture
def unreadable_input() -> Iterator[Path]:
    """Create and clean up one inaccessible file without touching the source tree."""
    with tempfile.TemporaryDirectory(prefix="tsort-denied-") as directory:
        path = Path(directory) / "denied"
        path.write_bytes(b"a b\n")
        path.chmod(0o000)
        yield path


# An existing unreadable input must produce GNU's access-denied result.
def test_access_denied_matches_coreutils(
    executables: tuple[Path, Path], unreadable_input: Path
) -> None:
    # upstream: none - Covers the required access-denied file-open boundary.
    # upstream-reason: parity.
    assert not os.access(unreadable_input, os.R_OK), "run as the benchmark's non-root user"
    reference, candidate = executables
    args = [str(unreadable_input)]
    expected = run_coreutils_utility(reference, UTILITY, args, PROJECT)
    actual = run_bench_utility(candidate, args, PROJECT)
    assert expected[2] == 1
    assert b"Permission denied" in expected[1]
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)


# Check the utility proof modules and the entry contract separately from runtime parity.
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename",
    [
        "Impl/TsortCore.dfy",
        "Impl/TsortGraphBuildCore.dfy",
        "Proof/TsortGraphBuildProof.dfy",
        "Impl/TsortState.dfy",
        "Impl/TsortCycleCore.dfy",
        "Impl/TsortStepCore.dfy",
        "Impl/TsortSortCore.dfy",
        "Proof/TsortProof.dfy",
        "Impl/Tsort.dfy",
    ],
)
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks the Dafny proof surface, not GNU runtime behavior.
    # upstream-reason: verification.
    run_dafny_verify(PROJECT / filename)
