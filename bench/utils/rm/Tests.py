"""Strict GNU oracle cases for rm's finite noninteractive filesystem scope."""

import os
import stat
import subprocess
from dataclasses import dataclass
from pathlib import Path

import pytest

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
UTILITY = "rm"
PROJECT = ROOT / "bench" / "utils" / UTILITY


@dataclass(frozen=True)
class EntryState:
    mode: int
    uid: int
    gid: int
    link_count: int
    data: bytes | str | None
    aliases: tuple[str, ...]


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    build_bench_utility(ROOT, UTILITY)
    build_coreutils_utility(ROOT, UTILITY)
    return (
        coreutils_binary_path(ROOT, ROOT / "_build/coreutils/src" / UTILITY),
        bench_dll_path(ROOT, ROOT / "_build/bench" / f"{UTILITY}_bench.dll"),
    )


def snapshot(root: Path) -> dict[str, EntryState]:
    """Normalize identities by their complete name classes in this tiny fixture."""
    paths = [root, *sorted(root.rglob("*"))]
    groups: dict[tuple[int, int], list[str]] = {}
    for path in paths:
        info = path.lstat()
        groups.setdefault((info.st_dev, info.st_ino), []).append(path.relative_to(root).as_posix())
    result = {}
    for path in paths:
        info = path.lstat()
        data = (
            os.readlink(path)
            if stat.S_ISLNK(info.st_mode)
            else path.read_bytes()
            if stat.S_ISREG(info.st_mode)
            else None
        )
        result[path.relative_to(root).as_posix()] = EntryState(
            info.st_mode,
            info.st_uid,
            info.st_gid,
            info.st_nlink,
            data,
            tuple(groups[(info.st_dev, info.st_ino)]),
        )
    return result


def parity(
    executables: tuple[Path, Path], args: list[str], reference: Path, candidate: Path
) -> None:
    native, dll = executables
    expected = run_coreutils_utility(native, UTILITY, args, reference)
    actual = run_bench_utility(dll, args, candidate)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(reference) == snapshot(candidate)


def pair(tmp_path: Path) -> tuple[Path, Path]:
    roots = tmp_path / "reference", tmp_path / "candidate"
    for root in roots:
        root.mkdir()
    return roots


# Remove an ordinary file and one hard-link name, preserving the surviving alias.
def test_files_and_aliases(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rm/r-1.sh
    # Adapt the ordinary-file verbose case with a surviving hard-link alias.
    roots = pair(tmp_path)
    for root in roots:
        (root / "file").write_bytes(b"payload")
        (root / "alias").hardlink_to(root / "file")
        (root / "other").write_bytes(b"other")
    parity(executables, ["-fv", "alias", "other"], *roots)


# Force ignores both absent names and paths below regular files.
@pytest.mark.parametrize("operand", ["missing", "file/child", ""])
def test_force_missing(executables: tuple[Path, Path], tmp_path: Path, operand: str) -> None:
    # upstream: coreutils/tests/rm/f-1.sh
    # The regular-file prefix is the regression in coreutils/tests/rm/ignorable.sh.
    roots = pair(tmp_path)
    for root in roots:
        (root / "file").write_bytes(b"keep")
    parity(executables, ["-f", operand], *roots)


# A middle empty operand reports its error while the later file is still removed.
def test_empty_operand_continues(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rm/empty-name.pl
    # empty-name-2 preserves the a, empty, b operand order.
    roots = pair(tmp_path)
    for root in roots:
        (root / "a").write_bytes(b"a")
        (root / "b").write_bytes(b"b")
    parity(executables, ["a", "", "b"], *roots)


# Without recursion, directories are rejected and their complete contents survive.
def test_directory_rejection(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rm/dir-nonrecur.sh
    roots = pair(tmp_path)
    for root in roots:
        (root / "d").mkdir()
        (root / "d/file").write_bytes(b"keep")
    parity(executables, ["-f", "d"], *roots)


# Bare preserve-root leaves its following pathname available as an operand.
def test_detached_optional_argument(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rm/i-never.sh
    # The same GNU getopt optional-value grammar applies to preserve-root.
    roots = pair(tmp_path)
    for root in roots:
        (root / "file").write_bytes(b"remove")
    parity(executables, ["--preserve-root", "file"], *roots)


# Once-only interaction with at most three nonrecursive operands needs no prompt.
def test_once_without_prompt(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rm/interactive-once.sh
    roots = pair(tmp_path)
    for root in roots:
        (root / "file").write_bytes(b"remove")
    parity(executables, ["-I", "file"], *roots)


# Force and never-interactive settings suppress simulated-terminal prompts in either order.
@pytest.mark.parametrize(
    "options",
    [
        ["-f", "---presume-input-tty"],
        ["---presume-input-tty", "-f"],
        ["--interactive=never", "---presume-input-tty"],
        ["---presume-input-tty", "--interactive=never"],
    ],
)
def test_never_interactive_simulated_terminal(
    executables: tuple[Path, Path], tmp_path: Path, options: list[str]
) -> None:
    # upstream: coreutils/tests/rm/i-never.sh and coreutils/tests/rm/isatty.sh
    # Retain i-never's protected file and isatty's terminal simulation.
    roots = pair(tmp_path)
    for root in roots:
        (root / "file").write_bytes(b"remove")
        (root / "file").chmod(0)
    parity(executables, [*options, "file"], *roots)


# The directory option removes empty directories and ordinary files with distinct verbose lines.
def test_directory_option(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rm/d-1.sh
    roots = pair(tmp_path)
    for root in roots:
        (root / "a").mkdir()
        (root / "b").write_bytes(b"")
    parity(executables, ["--dir", "--verbose", "a", "b"], *roots)


# A nonempty directory fails under -d and preserves its child.
def test_nonempty_directory_option(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rm/d-2.sh
    roots = pair(tmp_path)
    for root in roots:
        (root / "d").mkdir()
        (root / "d/a").write_bytes(b"a")
    parity(executables, ["-d", "d"], *roots)


# Recursive removal visits both operand hierarchies and retains external symlink targets.
def test_recursive_two_trees(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rm/dot-rel.sh
    roots = pair(tmp_path)
    for root in roots:
        for name in ("a", "b"):
            (root / name).mkdir()
            (root / name / "f").write_bytes(b"remove")
        (root / "target").write_bytes(b"preserve")
        (root / "a/link").symlink_to("../target")
    parity(executables, ["-rv", "a", "b"], *roots)


# Repeated trailing slashes produce GNU's single-slash root display and slash-free child display.
def test_verbose_trailing_slash(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rm/v-slash.sh
    roots = pair(tmp_path)
    for root in roots:
        (root / "a").mkdir()
        (root / "a/x").write_bytes(b"")
    parity(executables, ["--verbose", "-r", "a///"], *roots)


# Both dangling and directory symbolic links are removed without following their targets.
@pytest.mark.parametrize("target", ["missing", "directory"])
def test_symlinks(executables: tuple[Path, Path], tmp_path: Path, target: str) -> None:
    # upstream: coreutils/tests/rm/dangling-symlink.sh
    roots = pair(tmp_path)
    for root in roots:
        (root / "directory").mkdir()
        (root / "directory/file").write_bytes(b"keep")
        (root / "link").symlink_to(target)
    parity(executables, ["-rv", "link"], *roots)


# An unreadable empty directory can still be removed through its writable parent.
@pytest.mark.parametrize("options", [["-rf"], ["-d"]])
def test_unreadable_empty_directory(
    executables: tuple[Path, Path], tmp_path: Path, options: list[str]
) -> None:
    # upstream: coreutils/tests/rm/empty-inacc.sh
    roots = pair(tmp_path)
    for root in roots:
        (root / "inacc").mkdir(mode=0)
    parity(executables, [*options, "inacc"], *roots)


# Delete a child before its parent removal fails in an unwritable containing directory.
def test_partial_recursive_effect(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/rm/no-give-up.sh
    roots = pair(tmp_path)
    for root in roots:
        (root / "d").mkdir()
        (root / "d/f").write_bytes(b"remove child")
        root.chmod(0o555)
    try:
        parity(executables, ["-rfv", "d"], *roots)
    finally:
        for root in roots:
            root.chmod(0o755)


# A failed descendant preserves its ancestors while later writable siblings are still removed.
def test_failed_descendant_preserves_ancestors(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    # upstream: coreutils/tests/rm/rm1.sh
    roots = pair(tmp_path)
    for root in roots:
        (root / "b").mkdir()
        (root / "b/a").mkdir()
        (root / "b/a/p").mkdir()
        (root / "b/c").mkdir()
        (root / "b/d").mkdir()
        (root / "b/a").chmod(0o555)
    try:
        parity(executables, ["-rf", "b"], *roots)
    finally:
        for root in roots:
            (root / "b/a").chmod(0o755)


# Recursive requests refuse terminal dot components without entering or changing the hierarchy.
@pytest.mark.parametrize("operand", [".", "a/..", "a/."])
def test_dot_safeguard(executables: tuple[Path, Path], tmp_path: Path, operand: str) -> None:
    # upstream: coreutils/tests/rm/r-4.sh
    roots = pair(tmp_path)
    for root in roots:
        (root / "a").mkdir()
        (root / "a/file").write_bytes(b"keep")
    parity(executables, ["-rf", operand], *roots)


# A filename mistaken for an option receives GNU's removal hint with exact shell quoting.
@pytest.mark.parametrize("name", ["-z", "-a b", "-a:b", "-a'b", "-a\nb", "-x=y"])
def test_leading_hyphen_hint(executables: tuple[Path, Path], tmp_path: Path, name: str) -> None:
    # upstream: coreutils/tests/misc/usage_vs_getopt.sh
    # Extend its invalid-option case with the source's diagnose_leading_hyphen fixture.
    roots = pair(tmp_path)
    for root in roots:
        (root / name).write_bytes(b"keep")
    parity(executables, [name], *roots)


# GNU informational and malformed option cases preserve every filesystem entry.
@pytest.mark.parametrize(
    "args",
    [
        [],
        ["-f"],
        ["--help"],
        ["--version"],
        ["--help", "--bad"],
        ["--version", "--help"],
        ["--bad", "--help"],
        ["--v"],
        ["--force=1"],
        ["--no-preserve-ro"],
        ["--preserve-root=no"],
        ["--interactive=wrong"],
        # GNU gnulib/lib/argmatch.c treats the empty prefix as ambiguous.
        ["--interactive="],
        # Empty long names match every declaration in GNU getopt's order.
        ["--=value"],
        # GNU diagnoses missing operands before deciding whether to prompt.
        ["-i"],
        ["--interactive"],
        ["--interactive=always"],
        ["-I", "-r"],
        ["--interactive=once", "-r"],
        ["---presume-input-tty"],
        ["-f", "-i"],
        # Preserve native NAME_MAX failure after the metadata ENOENT mapping.
        ["-f", "n" * 256],
        ["---p=1"],
    ],
)
def test_cli(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: coreutils/tests/help/help-version-getopt.sh
    roots = pair(tmp_path)
    parity(executables, args, *roots)


# A malformed bundle reports the first invalid byte after its valid short options.
@pytest.mark.parametrize("option", ["-fz", "-rfz", "-f=1", "-fé", "-f--"])
def test_invalid_short_bundle(executables: tuple[Path, Path], tmp_path: Path, option: str) -> None:
    # upstream: coreutils/tests/help/help-version-getopt.sh
    # Source: coreutils/src/rm.c's getopt_long short-option declaration.
    roots = pair(tmp_path)
    parity(executables, [option], *roots)


# A failed final verbose flush preserves all completed removals and reports ENOSPC.
def test_verbose_write_failure(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/write-errors.sh
    # Apply its /dev/full case to rm's finite buffered verbose output.
    native, candidate = executables
    roots = pair(tmp_path)
    for root in roots:
        (root / "first").write_bytes(b"first")
        (root / "last").write_bytes(b"last")
    args = ["-v", "first", "last"]
    with Path("/dev/full").open("wb") as full:
        expected = subprocess.run(
            [UTILITY, *args],
            executable=str(native),
            cwd=roots[0],
            stdout=full,
            stderr=subprocess.PIPE,
            check=False,
            env=parity_env(),
            timeout=BENCH_COMMAND_TIMEOUT_SEC,
        )
        actual = run_candidate(
            candidate,
            args,
            cwd=roots[1],
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
    assert expected.stderr == b"rm: write error: No space left on device\n"
    assert expected.returncode == 1
    assert snapshot(roots[0]) == snapshot(roots[1])
    assert set(snapshot(roots[1])) == {"."}


# Check the entry, implementation and all proof declarations independently.
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename", ["Spec/RmSpec.dfy", "Impl/RmCore.dfy", "Proof/RmProof.dfy", "Impl/Rm.dfy"]
)
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks the required Dafny proof surface.
    # upstream-reason: verification.
    run_dafny_verify(
        PROJECT / filename,
        (
            "--boogie=/randomSeed:42",
            "--isolate-assertions",
            "--verification-time-limit:30",
        ),
    )
