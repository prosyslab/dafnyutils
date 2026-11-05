"""Benchmark oracle cases for bounded, equivalent GNU and Dafny filesystems."""

import os
import stat
import subprocess
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

import pytest

from tools.execution import run_candidate
from tools.test_support import (
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
UTILITY = "rmdir"
PROJECT = ROOT / "bench" / "utils" / UTILITY


@dataclass(frozen=True)
class Entry:
    kind: int
    mode: int
    uid: int
    gid: int
    links: int
    identity: str
    contents: bytes
    target: str


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    """Build only the two oracle executables, once for this bounded suite."""
    build_bench_utility(ROOT, UTILITY)
    build_coreutils_utility(ROOT, UTILITY)
    return (
        coreutils_binary_path(ROOT, ROOT / "_build/coreutils/src" / UTILITY),
        bench_dll_path(ROOT, ROOT / "_build/bench" / f"{UTILITY}_bench.dll"),
    )


def snapshot(cwd: Path) -> dict[str, Entry]:
    """Compare at most twelve entries with short contents and normalized aliases."""
    identities: dict[tuple[int, int], str] = {}
    entries: dict[str, Entry] = {}
    for path in [cwd, *sorted(cwd.rglob("*"))]:
        metadata = path.lstat()
        relative = path.relative_to(cwd).as_posix()
        identity = identities.setdefault((metadata.st_dev, metadata.st_ino), relative)
        entries[relative] = Entry(
            stat.S_IFMT(metadata.st_mode),
            stat.S_IMODE(metadata.st_mode),
            metadata.st_uid,
            metadata.st_gid,
            metadata.st_nlink,
            identity,
            path.read_bytes() if stat.S_ISREG(metadata.st_mode) else b"",
            os.readlink(path) if stat.S_ISLNK(metadata.st_mode) else "",
        )
    return entries


def assert_parity(
    executables: tuple[Path, Path],
    args: list[str],
    workspace: Path,
    setup: Callable[[Path], None] | None = None,
) -> tuple[tuple[bytes, bytes, int], dict[str, Entry]]:
    """Compare both streams, status, and every normalized filesystem entry."""
    reference_dir = workspace / "reference"
    candidate_dir = workspace / "candidate"
    for cwd in (reference_dir, candidate_dir):
        cwd.mkdir(mode=0o700)
        cwd.chmod(0o700)
        if setup is not None:
            setup(cwd)
    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, args, reference_dir)
    actual = run_bench_utility(candidate, args, candidate_dir)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    entries = snapshot(reference_dir)
    assert snapshot(candidate_dir) == entries
    return expected, entries


# Removing an empty directory preserves unrelated content and hard-link identity.
def test_empty_directory(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    # Port the ordinary rmdir_setup empty-directory operand.
    def setup(cwd: Path) -> None:
        (cwd / "dir").mkdir()
        (cwd / "keep").write_bytes(b"unchanged\n")
        os.link(cwd / "keep", cwd / "alias")

    result, entries = assert_parity(executables, ["dir"], tmp_path, setup)
    assert result == (b"", b"", 0)
    assert set(entries) == {".", "keep", "alias"}
    assert entries["keep"].identity == entries["alias"].identity


# Parent removal strips trailing slashes before looking for the next ancestor.
@pytest.mark.parametrize("operand", ["dir/", "dir///", "dir/sub/", "dir//sub///"])
def test_parent_trailing_slash(
    executables: tuple[Path, Path], tmp_path: Path, operand: str
) -> None:
    # upstream: coreutils/tests/rmdir/t-slash.sh
    # Preserve its dir/ scenario and extend the same slash rule to one parent.
    def setup(cwd: Path) -> None:
        (cwd / "dir").mkdir()
        if "sub" in operand:
            (cwd / "dir/sub").mkdir()

    result, entries = assert_parity(executables, ["-pv", operand], tmp_path, setup)
    assert result[2] == 0
    assert set(entries) == {"."}


# Nonempty ancestors stop quietly after earlier descendants have been removed.
def test_ignore_nonempty_parent(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rmdir/ignore.sh
    # Port the a/b/c chain with a/x retained.
    def setup(cwd: Path) -> None:
        (cwd / "a/b/c").mkdir(parents=True)
        (cwd / "a/x").mkdir()

    result, entries = assert_parity(
        executables, ["-pv", "--ignore-fail-on-non-empty", "a/b/c"], tmp_path, setup
    )
    assert result == (
        b"rmdir: removing directory, 'a/b/c'\nrmdir: removing directory, 'a/b'\n"
        b"rmdir: removing directory, 'a'\n",
        b"",
        0,
    )
    assert set(entries) == {".", "a", "a/x"}


# An ordinary failed parent removal reports its separate directory diagnostic.
def test_nonempty_parent_failure(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rmdir/ignore.sh
    # Use the same sibling fixture without ignoring the nonempty parent.
    def setup(cwd: Path) -> None:
        (cwd / "a/b").mkdir(parents=True)
        (cwd / "a/x").mkdir()

    result, entries = assert_parity(executables, ["-p", "a/b"], tmp_path, setup)
    assert result == (b"", b"rmdir: failed to remove directory 'a': Directory not empty\n", 1)
    assert set(entries) == {".", "a", "a/x"}


# A symlink encountered while removing parents uses the non-directory diagnostic.
def test_parent_symlink_failure(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rmdir/symlink-errors.sh
    # Port rmdir -p sl/dir2 and retain the symlink and its empty target.
    def setup(cwd: Path) -> None:
        (cwd / "dir/dir2").mkdir(parents=True)
        (cwd / "sl").symlink_to("dir")

    result, entries = assert_parity(executables, ["-pv", "sl/dir2"], tmp_path, setup)
    assert result[1:] == (b"rmdir: failed to remove 'sl': Not a directory\n", 1)
    assert set(entries) == {".", "dir", "sl"}


# Trailing-slash symlinks distinguish directories, missing targets, and regular files.
@pytest.mark.parametrize(
    ("target", "reason"),
    [
        ("dir", "Symbolic link not followed"),
        ("missing", "Symbolic link not followed"),
        ("file", "Not a directory"),
    ],
)
def test_symlink_trailing_slash(
    executables: tuple[Path, Path], tmp_path: Path, target: str, reason: str
) -> None:
    # upstream: coreutils/tests/rmdir/symlink-errors.sh
    # Port the sl/, dl/, and fl/ diagnostic cases separately.
    def setup(cwd: Path) -> None:
        (cwd / "dir").mkdir()
        (cwd / "file").write_bytes(b"retained")
        (cwd / "link").symlink_to(target)

    result, _ = assert_parity(executables, ["link/"], tmp_path, setup)
    assert result == (b"", f"rmdir: failed to remove 'link/': {reason}\n".encode(), 1)


# Earlier failures survive successful later operands and partial parent progress.
def test_ordered_partial_effects(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rmdir/fail-perm.sh
    # Preserve its initial nonempty d operand followed by d/e/f parent processing.
    def setup(cwd: Path) -> None:
        (cwd / "d/e/f").mkdir(parents=True)
        (cwd / "last").mkdir()

    result, entries = assert_parity(executables, ["-pv", "d", "d/e/f", "last"], tmp_path, setup)
    assert result[2] == 1
    assert result[1] == b"rmdir: failed to remove 'd': Directory not empty\n"
    assert set(entries) == {"."}


# Missing and invalid operands fail without damaging valid fixture entries.
@pytest.mark.parametrize("operand", ["missing", "", "file", "file/", "file/child", ".", ".."])
def test_operand_errors(executables: tuple[Path, Path], tmp_path: Path, operand: str) -> None:
    # upstream: none - Checks rmdir.c's ordinary failed-rmdir branch on safe local operands.
    def setup(cwd: Path) -> None:
        (cwd / "file").write_bytes(b"retained")

    result, entries = assert_parity(executables, ["-v", operand], tmp_path, setup)
    assert result[2] == 1
    assert set(entries) == {".", "file"}


# Every verbose attempt uses GNU shell quoting for literal names.
@pytest.mark.parametrize("operand", ["a'b", "a b", "tab\tname", "line\nbreak", "한글"])
def test_verbose_quoting(executables: tuple[Path, Path], tmp_path: Path, operand: str) -> None:
    # upstream: none - Checks quoteaf bytes in rmdir.c's attempt and failure diagnostics.
    def setup(cwd: Path) -> None:
        (cwd / operand).mkdir()

    result, entries = assert_parity(executables, ["-v", operand, operand], tmp_path, setup)
    assert result[2] == 1
    assert set(entries) == {"."}


# Parent aliases and unambiguous abbreviations preserve the GNU synonym rule.
@pytest.mark.parametrize("option", ["-p", "--parents", "--path", "--p", "--pa", "--pat", "--par"])
def test_parent_options(executables: tuple[Path, Path], tmp_path: Path, option: str) -> None:
    # upstream: none - Checks rmdir.c's parents/path aliases and getopt_long synonym matching.
    def setup(cwd: Path) -> None:
        (cwd / "a/b").mkdir(parents=True)

    result, entries = assert_parity(executables, [option, "a/b"], tmp_path, setup)
    assert result == (b"", b"", 0)
    assert set(entries) == {"."}


# The option terminator keeps a literal option-looking operand removable.
def test_double_dash(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    def setup(cwd: Path) -> None:
        (cwd / "--help").mkdir()

    result, entries = assert_parity(executables, ["-v", "--", "--help"], tmp_path, setup)
    assert result[2] == 0
    assert set(entries) == {"."}


# Information requests stop parsing at the first request unless an earlier option failed.
@pytest.mark.parametrize(
    "args",
    [
        ["--help"],
        ["--version"],
        ["--help", "--bad"],
        ["--bad", "--help"],
        ["--help", "--version"],
        ["--version", "--help"],
        ["missing", "--help"],
    ],
)
def test_information_options(
    executables: tuple[Path, Path], tmp_path: Path, args: list[str]
) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    assert_parity(executables, args, tmp_path)


# Malformed options preserve GNU's canonical long names and the first invalid bundled byte.
@pytest.mark.parametrize(
    "args",
    [
        [],
        ["-v"],
        ["--bogus"],
        ["-x"],
        ["-pvx"],
        ["-é"],
        ["--v"],
        ["--v=1"],
        ["--verbose=1"],
        ["--verbo=1"],
        ["--help=1"],
        ["--p=1"],
        ["--pa=1"],
        ["--pat=1"],
        ["--par=1"],
        ["--ignore=1"],
        ["--="],
        ["--=x"],
    ],
)
def test_cli_errors(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    result, entries = assert_parity(executables, args, tmp_path)
    assert result[2] == 1
    assert set(entries) == {"."}


# An empty directory behind an unwritable parent still fails with --ignore enabled.
def test_ignore_empty_permission_failure(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rmdir/ignore.sh
    # Port the x/y empty-directory permission case under the ordinary test identity.
    def setup(cwd: Path) -> None:
        (cwd / "x/y").mkdir(parents=True)
        (cwd / "x").chmod(0o555)

    try:
        result, entries = assert_parity(
            executables, ["--ignore-fail-on-non-empty", "x/y"], tmp_path, setup
        )
        if os.geteuid() != 0:
            assert result[2] == 1
            assert "x/y" in entries
    finally:
        for variant in ("reference", "candidate"):
            (tmp_path / variant / "x").chmod(0o755)


# A readable nonempty directory suppresses even a permission error from rmdir itself.
def test_ignore_nonempty_permission_failure(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rmdir/ignore.sh
    # Port the x/y/z variant that must return success for the retained nonempty y.
    def setup(cwd: Path) -> None:
        (cwd / "x/y").mkdir(parents=True)
        (cwd / "x/y/z").write_bytes(b"retained")
        (cwd / "x").chmod(0o555)

    try:
        result, entries = assert_parity(
            executables, ["--ignore-fail-on-non-empty", "x/y"], tmp_path, setup
        )
        assert result == (b"", b"", 0)
        assert set(entries) == {".", "x", "x/y", "x/y/z"}
    finally:
        for variant in ("reference", "candidate"):
            (tmp_path / variant / "x").chmod(0o755)


# An unreadable empty directory cannot establish the nonempty suppression condition.
def test_ignore_unreadable_permission_failure(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    # upstream: coreutils/tests/rmdir/ignore.sh
    # Port the final unreadable x/y variant without adding any hidden descendants.
    def setup(cwd: Path) -> None:
        (cwd / "x/y").mkdir(parents=True)
        (cwd / "x/y").chmod(0o111)
        (cwd / "x").chmod(0o555)

    try:
        result, entries = assert_parity(
            executables, ["--ignore-fail-on-non-empty", "x/y"], tmp_path, setup
        )
        if os.geteuid() != 0:
            assert result[2] == 1
            assert "x/y" in entries
    finally:
        for variant in ("reference", "candidate"):
            parent = tmp_path / variant / "x"
            parent.chmod(0o755)
            if (parent / "y").exists():
                (parent / "y").chmod(0o755)


# A failed verbose flush preserves both completed removals and reports the write error.
def test_verbose_write_failure(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/write-errors.sh
    # Apply its /dev/full ENOSPC scenario to rmdir's finite verbose output.
    reference, candidate = executables
    reference_dir, candidate_dir = tmp_path / "reference", tmp_path / "candidate"
    for cwd in (reference_dir, candidate_dir):
        cwd.mkdir()
        (cwd / "first").mkdir()
        (cwd / "last").mkdir()
    args = ["-v", "first", "last"]
    with Path("/dev/full").open("wb") as full:
        expected = subprocess.run(
            [UTILITY, *args],
            executable=str(reference),
            cwd=reference_dir,
            stdout=full,
            stderr=subprocess.PIPE,
            check=False,
            env=parity_env(),
            timeout=BENCH_COMMAND_TIMEOUT_SEC,
        )
        actual = run_candidate(
            candidate,
            args,
            cwd=candidate_dir,
            stdout=full,
            stderr=subprocess.PIPE,
            check=False,
            env=parity_env(),
            timeout=BENCH_COMMAND_TIMEOUT_SEC,
        )
    assert_result_matches_reference(
        (b"", expected.stderr, expected.returncode),
        (b"", actual.stderr, actual.returncode),
        ignore_stderr_when_exit_nonzero=False,
    )
    assert expected.stderr == b"rmdir: write error: No space left on device\n"
    assert expected.returncode == 1
    assert snapshot(candidate_dir) == snapshot(reference_dir)
    assert set(snapshot(candidate_dir)) == {"."}


# Verify the candidate proof closure separately from runtime oracle comparisons.
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename",
    ["Impl/RmdirCore.dfy", "Spec/RmdirSpec.dfy", "Proof/RmdirProof.dfy", "Impl/Rmdir.dfy"],
)
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks the entry contract and proof surface, not runtime behavior.
    run_dafny_verify(PROJECT / filename)
