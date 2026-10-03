"""GNU parity cases for link."""

from pathlib import Path

import pytest

from tools.bench_test_support import (
    assert_result_matches_reference,
    bench_dll_path,
    build_bench_utility,
    build_coreutils_utility,
    coreutils_binary_path,
    evaluation_target_root,
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])
UTILITY = "link"
PROJECT = ROOT / "bench" / "utils" / UTILITY


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    """Build the two targets only for runtime cases; local Make targets use -n0."""
    build_bench_utility(ROOT, UTILITY)
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


# Missing both operands reports a failure and usage guidance.
def test_missing_operands_match_coreutils(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: none - Adds missing-operand parity.
    # upstream-reason: parity.
    assert_parity(executables, [], tmp_path)


# Supplying only the source identifies that source in the missing-target diagnostic.
def test_missing_target_operand_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    # upstream: none - Adds one-operand diagnostic parity.
    # upstream-reason: parity.
    assert_parity(executables, ["source"], tmp_path)


# Extra operands are rejected without creating the requested hard link.
def test_extra_operand_matches_coreutils(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: none - Adds extra-operand parity.
    # upstream-reason: parity.
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    for directory in (ref_dir, bench_dir):
        directory.mkdir()
        (directory / "source").write_bytes(b"payload\n")

    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, ["source", "target", "extra"], ref_dir)
    actual = run_bench_utility(candidate, ["source", "target", "extra"], bench_dir)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    for directory in (ref_dir, bench_dir):
        assert not (directory / "target").exists()
        assert (directory / "source").read_bytes() == b"payload\n"


# Extra-operand diagnostics quote special characters without creating a link.
@pytest.mark.parametrize("operand", ["a'b", 'a"b', "a\nb", "a\tb", "a\\b", "a b"])
def test_quoted_extra_operand_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path, operand: str
) -> None:
    # upstream: none - Adds GNU argument-quoting parity.
    # upstream-reason: parity.
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    for directory in (ref_dir, bench_dir):
        directory.mkdir()
        (directory / "source").write_bytes(b"payload")

    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, ["source", "target", operand], ref_dir)
    actual = run_bench_utility(candidate, ["source", "target", operand], bench_dir)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    for directory in (ref_dir, bench_dir):
        assert not (directory / "target").exists()


# Successful execution creates a second name for the source inode.
def test_regular_file_hard_link_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    for directory in (ref_dir, bench_dir):
        directory.mkdir()
        (directory / "source").write_bytes(b"payload\n")

    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, ["source", "target"], ref_dir)
    actual = run_bench_utility(candidate, ["source", "target"], bench_dir)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert expected[2] == actual[2] == 0
    for directory in (ref_dir, bench_dir):
        source_stat = (directory / "source").stat()
        target_stat = (directory / "target").stat()
        assert source_stat.st_ino == target_stat.st_ino
        assert source_stat.st_nlink == target_stat.st_nlink == 2
        assert (directory / "target").read_bytes() == b"payload\n"


# A nonexistent source reports a creation error and leaves the target absent.
def test_missing_source_matches_coreutils(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: none - Adds missing-source parity.
    # upstream-reason: parity.
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    ref_dir.mkdir()
    bench_dir.mkdir()
    reference, candidate = executables

    expected = run_coreutils_utility(reference, UTILITY, ["missing", "target"], ref_dir)
    actual = run_bench_utility(candidate, ["missing", "target"], bench_dir)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert expected[2] == actual[2] == 1
    assert not (ref_dir / "target").exists()
    assert not (bench_dir / "target").exists()


# An existing target reports a creation error and preserves both files.
def test_existing_target_matches_coreutils(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: none - Adds existing-target parity.
    # upstream-reason: parity.
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    for directory in (ref_dir, bench_dir):
        directory.mkdir()
        (directory / "source").write_bytes(b"source contents")
        (directory / "target").write_bytes(b"target contents")

    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, ["source", "target"], ref_dir)
    actual = run_bench_utility(candidate, ["source", "target"], bench_dir)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert expected[2] == actual[2] == 1
    for directory in (ref_dir, bench_dir):
        assert (directory / "source").read_bytes() == b"source contents"
        assert (directory / "target").read_bytes() == b"target contents"


# Failed creation diagnostics quote special characters in both pathnames.
@pytest.mark.parametrize("source", ["a'b", 'a"b', "a\nb", "a\tb", "a\\b", "a b"])
def test_quoted_missing_source_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path, source: str
) -> None:
    # upstream: none - Adds GNU path-quoting parity.
    # upstream-reason: parity.
    assert_parity(executables, [source, "target name"], tmp_path)


# An empty source pathname reports the corresponding system error.
def test_empty_source_matches_coreutils(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: none - Adds empty-source parity.
    # upstream-reason: parity.
    assert_parity(executables, ["", "target"], tmp_path)


# A target in a nonexistent directory reports an error without changing the source.
def test_missing_target_parent_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    # upstream: none - Adds missing-target-parent parity.
    # upstream-reason: parity.
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    for directory in (ref_dir, bench_dir):
        directory.mkdir()
        (directory / "source").write_bytes(b"payload")

    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, ["source", "missing/target"], ref_dir)
    actual = run_bench_utility(candidate, ["source", "missing/target"], bench_dir)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert expected[2] == actual[2] == 1
    for directory in (ref_dir, bench_dir):
        assert (directory / "source").read_bytes() == b"payload"
        assert not (directory / "missing").exists()


# Help exits successfully with the GNU help output.
def test_help_matches_coreutils(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    assert_parity(executables, ["--help"], tmp_path)


# Version exits successfully with the GNU version output.
def test_version_matches_coreutils(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    assert_parity(executables, ["--version"], tmp_path)


# An unknown long option produces GNU's option diagnostic.
def test_invalid_option_matches_coreutils(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/usage_vs_getopt.sh
    assert_parity(executables, ["--thisoptiondoesnotexist"], tmp_path)


# Help and version requests take precedence according to their argument order.
@pytest.mark.parametrize(
    "args",
    [
        ["--help", "--version"],
        ["--version", "--help"],
        ["--help", "--bad"],
        ["--bad", "--help"],
    ],
)
def test_option_precedence_matches_coreutils(
    executables: tuple[Path, Path], tmp_path: Path, args: list[str]
) -> None:
    # upstream: none - Adds mixed-option precedence parity.
    # upstream-reason: parity.
    assert_parity(executables, args, tmp_path)


# The option delimiter permits source and target names beginning with hyphens.
def test_option_like_paths_match_coreutils(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: none - Adds link-specific -- delimiter parity.
    # upstream-reason: parity.
    ref_dir = tmp_path / "reference"
    bench_dir = tmp_path / "candidate"
    for directory in (ref_dir, bench_dir):
        directory.mkdir()
        (directory / "--help").write_bytes(b"payload")

    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, ["--", "--help", "--version"], ref_dir)
    actual = run_bench_utility(candidate, ["--", "--help", "--version"], bench_dir)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert expected[2] == actual[2] == 0
    for directory in (ref_dir, bench_dir):
        assert (directory / "--help").stat().st_ino == (directory / "--version").stat().st_ino


# Check each proof module as well as the entry contract required by make check.
@pytest.mark.dafny_verify
@pytest.mark.parametrize("filename", ["LinkCore.dfy", "LinkProof.dfy", "Link.dfy"])
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks the Dafny proof surface, not GNU runtime behavior.
    run_dafny_verify(PROJECT / filename)
