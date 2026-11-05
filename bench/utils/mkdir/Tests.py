"""Benchmark oracle/scoring cases comparing bounded GNU and Dafny fixtures."""

import os
import stat
import subprocess
from collections.abc import Callable
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
UTILITY = "mkdir"
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
    """Build each benchmark target once, independently of development tests."""
    build_bench_utility(ROOT, UTILITY)
    build_coreutils_utility(ROOT, UTILITY)
    return (
        coreutils_binary_path(ROOT, ROOT / "_build/coreutils/src" / UTILITY),
        bench_dll_path(ROOT, ROOT / "_build/bench" / f"{UTILITY}_bench.dll"),
    )


def snapshot(cwd: Path) -> dict[str, Entry]:
    """Observe this benchmark's fixtures of at most six short paths and bytes."""
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
    """Compare streams, status and complete fixture effects on equivalent inputs."""
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
    expected_fs = snapshot(reference_dir)
    assert snapshot(candidate_dir) == expected_fs
    return expected, expected_fs


# The ordinary help-version setup creates a previously absent subdirectory.
def test_creates_directory(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    # Port mkdir_setup's absent subdir operand.
    result, entries = assert_parity(executables, ["subdir"], tmp_path)
    assert result == (b"", b"", 0)
    assert stat.S_ISDIR(entries["subdir"].kind)


# Nonrecursive creation accepts trailing slashes on a new directory.
@pytest.mark.parametrize("operand", ["d2/", "d2///"])
def test_trailing_slash(executables: tuple[Path, Path], tmp_path: Path, operand: str) -> None:
    # upstream: coreutils/tests/mkdir/t-slash.sh
    # Port the non--parents d2/ creation block.
    result, entries = assert_parity(executables, [operand], tmp_path)
    assert result == (b"", b"", 0)
    assert stat.S_ISDIR(entries["d2"].kind)


# Verbose success uses GNU's double-quote shortcut for initial shell-special bytes.
@pytest.mark.parametrize("name", ["#can't", "~can't", "at@quote'"])
def test_verbose_path_quoting(executables: tuple[Path, Path], tmp_path: Path, name: str) -> None:
    # upstream: none - Covers the shared native quoting regression on creation.
    result, entries = assert_parity(executables, ["-v", name], tmp_path)
    assert result[2] == 0
    assert stat.S_ISDIR(entries[name].kind)


# An existing directory fails when --parents was not requested.
def test_existing_directory(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/mkdir/parents.sh
    # Port the assertion that plain mkdir e-dir fails.
    def setup(cwd: Path) -> None:
        (cwd / "e-dir").mkdir(mode=0o700)

    result, _ = assert_parity(executables, ["e-dir"], tmp_path, setup)
    assert result == (b"", b"mkdir: cannot create directory 'e-dir': File exists\n", 1)


# A missing parent fails without implicitly creating any ancestor.
def test_missing_parent(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/mkdir/special-1.sh
    # Port the plain mkdir t/sub failure without the separately unsupported -m.
    result, entries = assert_parity(executables, ["t/sub"], tmp_path)
    assert result[2] == 1
    assert set(entries) == {"."}


# Default directory modes honor each default-mode umask row in perm.sh.
@pytest.mark.parametrize("mask", [0o000, 0o077, 0o050, 0o160])
def test_default_mode_umask(executables: tuple[Path, Path], tmp_path: Path, mask: int) -> None:
    # upstream: coreutils/tests/mkdir/perm.sh
    # Port empty-mode/non--parents rows, with an already searchable parent.
    def setup(cwd: Path) -> None:
        (cwd / "parent").mkdir(mode=0o700)
        (cwd / "parent").chmod(0o700)

    previous = os.umask(mask)
    try:
        result, entries = assert_parity(executables, ["parent/sub"], tmp_path, setup)
    finally:
        os.umask(previous)
    assert result == (b"", b"", 0)
    assert entries["parent/sub"].mode == 0o777 & ~mask


# Earlier success survives a later failure, and the final operand is still attempted.
def test_partial_effects(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: none - Checks mkdir.c/savewd_process_files ordered-operand behavior.
    result, entries = assert_parity(executables, ["first", "missing/child", "last"], tmp_path)
    assert result[2] == 1
    assert set(entries) == {".", "first", "last"}


# A later operand can use the parent made by an earlier operand.
def test_ordered_parent_then_child(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: none - Checks sequential dependencies between default mkdir operands.
    result, entries = assert_parity(executables, ["parent", "parent/child"], tmp_path)
    assert result == (b"", b"", 0)
    assert set(entries) == {".", "parent", "parent/child"}


# Repeated operands announce successes and diagnose duplicates in operand order.
def test_verbose_duplicate(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/mkdir/p-v.sh
    # Port announce_mkdir's exact spelling to default-mode duplicate operands.
    result, _ = assert_parity(executables, ["-v", "one", "one", "two"], tmp_path)
    assert result == (
        b"mkdir: created directory 'one'\nmkdir: created directory 'two'\n",
        b"mkdir: cannot create directory 'one': File exists\n",
        1,
    )


# Verbose output preserves GNU quoting for special and non-ASCII names.
@pytest.mark.parametrize(
    "operand", ["a'b", "a b", "line\nbreak", "tab\tname", "back\\slash", "한글"]
)
def test_verbose_quoting(executables: tuple[Path, Path], tmp_path: Path, operand: str) -> None:
    # upstream: none - Checks quoteaf announcements for literal Linux filenames.
    result, entries = assert_parity(executables, ["--verbose", operand], tmp_path)
    assert result[2] == 0
    assert operand in entries


# Missing paths use GNU's diagnostic quoting, including control and UTF-8 bytes.
@pytest.mark.parametrize(
    "operand", ["a'b", "a b", "line\nbreak", "tab\tname", "back\\slash", "한글"]
)
def test_quoted_failure(executables: tuple[Path, Path], tmp_path: Path, operand: str) -> None:
    # upstream: none - Distinguishes quote_mem error text from quoteaf announcements.
    result, entries = assert_parity(executables, [operand + "/child"], tmp_path)
    assert result[2] == 1
    assert set(entries) == {"."}


# One duplicate operand uses different GNU quoting styles in its announcement and error.
def test_quoted_duplicate(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: none - Exercises both quoteaf and quote for the same literal path.
    result, entries = assert_parity(executables, ["-v", "a'b", "a'b"], tmp_path)
    assert result[2] == 1
    assert set(entries) == {".", "a'b"}


# Intermediate symbolic links are followed without replacing the link itself.
def test_symlink_parent(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/mkdir/p-thru-slink.sh
    # Port slink-to-dot; this existing parent does not need -p.
    def setup(cwd: Path) -> None:
        (cwd / "slink").symlink_to(".", target_is_directory=True)

    result, entries = assert_parity(executables, ["slink/x"], tmp_path, setup)
    assert result == (b"", b"", 0)
    assert entries["slink"].target == "."
    assert "x" in entries


# Terminal symlinks remain existing entries even with trailing separators.
@pytest.mark.parametrize("operand", ["link", "link/", "dangling", "dangling/"])
def test_terminal_symlink(executables: tuple[Path, Path], tmp_path: Path, operand: str) -> None:
    # upstream: none - Checks mkdir's terminal no-follow behavior.
    def setup(cwd: Path) -> None:
        (cwd / "directory").mkdir()
        (cwd / "link").symlink_to("directory", target_is_directory=True)
        (cwd / "dangling").symlink_to("absent")

    result, entries = assert_parity(executables, [operand], tmp_path, setup)
    assert result[2] == 1
    assert entries["link"].target == "directory"
    assert entries["dangling"].target == "absent"


# Invalid path operands report exact syscall errors without creating entries.
@pytest.mark.parametrize("operand", ["", ".", "..", "file/child", "file/", "loop/child"])
def test_path_error(executables: tuple[Path, Path], tmp_path: Path, operand: str) -> None:
    # upstream: none - Checks Linux path failures exposed by the shared IO contracts.
    def setup(cwd: Path) -> None:
        (cwd / "file").write_bytes(b"retained")
        (cwd / "loop").symlink_to("loop")

    result, entries = assert_parity(executables, [operand], tmp_path, setup)
    assert result[2] == 1
    assert set(entries) == {".", "file", "loop"}


# A double dash makes option-looking directory names ordinary operands.
def test_double_dash(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    # Port the option-termination convention for option-like operands.
    result, entries = assert_parity(executables, ["-v", "--", "--help", "-v"], tmp_path)
    assert result[2] == 0
    assert set(entries) == {".", "--help", "-v"}


# Informational requests use exact GNU bytes, including accepted abbreviations.
@pytest.mark.parametrize("args", [["--help"], ["--version"], ["--he"], ["--vers"]])
def test_information(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    result, entries = assert_parity(executables, args, tmp_path)
    assert result[2] == 0
    assert set(entries) == {"."}


# GNU acts on the first information request or earlier parse error.
@pytest.mark.parametrize(
    "args",
    [
        ["--help", "--bogus"],
        ["--bogus", "--help"],
        ["--version", "--help"],
        ["--help", "--version"],
        ["new", "--help", "--bogus"],
    ],
)
def test_information_precedence(
    executables: tuple[Path, Path], tmp_path: Path, args: list[str]
) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    assert_parity(executables, args, tmp_path)


# Missing operands fail before any filesystem mutation.
@pytest.mark.parametrize("args", [[], ["-v"]])
def test_missing_operand(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: none - Checks mkdir.c's missing-operand branch.
    result, entries = assert_parity(executables, args, tmp_path)
    assert result == (b"", b"mkdir: missing operand\nTry 'mkdir --help' for more information.\n", 1)
    assert set(entries) == {"."}


# Malformed options preserve GNU bytes, including unknown bytes inside bundles.
@pytest.mark.parametrize(
    "args",
    [
        ["--bogus"],
        ["-Q"],
        ["-vQ"],
        ["--verbose=value"],
        ["--ver"],
        ["--help=value"],
        ["-é"],
        ["--="],
        ["--=x"],
        ["--=é"],
        ["--ve=x"],
    ],
)
def test_parse_error(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    result, entries = assert_parity(executables, args, tmp_path)
    assert result[2] == 1
    assert set(entries) == {"."}


# A failed verbose write reports ENOSPC after retaining every successful directory.
def test_verbose_write_error_keeps_directories(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    # upstream: coreutils/tests/misc/write-errors.sh
    # Apply its /dev/full ENOSPC scenario to mkdir's finite verbose writer.
    reference, candidate = executables
    expected_dir = tmp_path / "reference"
    actual_dir = tmp_path / "candidate"
    expected_dir.mkdir()
    actual_dir.mkdir()
    args = ["-v", "first", "last"]
    with Path("/dev/full").open("wb") as full:
        expected = subprocess.run(
            [UTILITY, *args],
            executable=str(reference),
            cwd=expected_dir,
            stdout=full,
            stderr=subprocess.PIPE,
            check=False,
            env=parity_env(),
            timeout=BENCH_COMMAND_TIMEOUT_SEC,
        )
        actual = run_candidate(
            candidate,
            args,
            cwd=actual_dir,
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
    assert expected.returncode == 1
    assert expected.stderr == b"mkdir: write error: No space left on device\n"
    assert snapshot(actual_dir) == snapshot(expected_dir)
    assert set(snapshot(actual_dir)) == {".", "first", "last"}


# Check specification well-formedness, helpers and the entry obligation separately.
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename",
    ["Spec/MkdirSpec.dfy", "Impl/MkdirCore.dfy", "Proof/MkdirProof.dfy", "Impl/Mkdir.dfy"],
)
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks proof obligations rather than GNU runtime behavior.
    run_dafny_verify(PROJECT / filename)
