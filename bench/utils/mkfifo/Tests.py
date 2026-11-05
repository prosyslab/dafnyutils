"""Benchmark oracle/scoring cases comparing bounded GNU and Dafny mkfifo fixtures."""

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
UTILITY = "mkfifo"
PROJECT = ROOT / "bench" / "utils" / UTILITY
INVALID_MODE = b"mkfifo: invalid mode\n"
SPECIAL_BITS = b"mkfifo: mode must specify only file permission bits\n"
MISSING_OPERAND = b"mkfifo: missing operand\nTry 'mkfifo --help' for more information.\n"


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
    """Observe this benchmark's small fixtures: kind, mode, owner, links and bytes."""
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


def restore_access(cwd: Path) -> None:
    """Let pytest remove fixtures whose directories were made read-only."""
    for path in [cwd, *cwd.rglob("*")]:
        if path.is_dir() and not path.is_symlink():
            path.chmod(0o700)


def assert_parity(
    executables: tuple[Path, Path],
    args: list[str],
    workspace: Path,
    setup: Callable[[Path], None] | None = None,
    mask: int = 0o022,
) -> tuple[tuple[bytes, bytes, int], dict[str, Entry]]:
    """Compare streams, status and complete fixture effects under one umask."""
    reference_dir = workspace / "reference"
    candidate_dir = workspace / "candidate"
    for cwd in (reference_dir, candidate_dir):
        cwd.mkdir(mode=0o700)
        cwd.chmod(0o700)
        if setup is not None:
            setup(cwd)
    reference, candidate = executables
    previous = os.umask(mask)
    try:
        expected = run_coreutils_utility(reference, UTILITY, args, reference_dir)
        actual = run_bench_utility(candidate, args, candidate_dir)
    finally:
        os.umask(previous)
    try:
        assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
        expected_fs = snapshot(reference_dir)
        assert snapshot(candidate_dir) == expected_fs
    finally:
        restore_access(reference_dir)
        restore_access(candidate_dir)
    return expected, expected_fs


# A plain operand creates one FIFO with the default mode.
def test_creates_fifo(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/mknod.sh
    # Port mkfifo_or_skip_'s plain "mkfifo fifo" creation.
    result, entries = assert_parity(executables, ["fifo"], tmp_path)
    assert result == (b"", b"", 0)
    assert stat.S_ISFIFO(entries["fifo"].kind)
    assert entries["fifo"].mode == 0o644


# An octal MODE is applied exactly, even when the umask clears every bit.
def test_octal_mode_ignores_umask(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/mknod.sh
    # Port "umask 777; mkfifo -m 734 f2".
    result, entries = assert_parity(executables, ["-m", "734", "f2"], tmp_path, mask=0o777)
    assert result == (b"", b"", 0)
    assert entries["f2"].mode == 0o734


# A symbolic MODE with a who list starts from a=rw and ignores the umask.
def test_symbolic_mode_with_who(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/mknod.sh
    # Port "umask 777; mkfifo --mode='ug+rw,o+r' f5".
    result, entries = assert_parity(executables, ["--mode=ug+rw,o+r", "f5"], tmp_path, mask=0o777)
    assert result == (b"", b"", 0)
    assert entries["f5"].mode == 0o666


# Without -m, the native creation applies the process umask to a=rw.
@pytest.mark.parametrize("mask", [0o000, 0o022, 0o077, 0o137])
def test_default_mode_umask(executables: tuple[Path, Path], tmp_path: Path, mask: int) -> None:
    # upstream: none - Checks src/mkfifo.c's default MODE_RW_UGO creation.
    result, entries = assert_parity(executables, ["p"], tmp_path, mask=mask)
    assert result == (b"", b"", 0)
    assert entries["p"].mode == 0o666 & ~mask


# Symbolic actions apply left to right; actions without who use the umask.
@pytest.mark.parametrize(
    "mode",
    [
        "u+x",
        "=rw,+x",
        "-w",
        "a-rw",
        "+644,u+x",
        "+X",
        "u+x,+X",
        "u=g",
        "g=u,o-r",
        "go=",
        "a=",
        "=",
        "+",
        "uu+r",
        "o+s",
        "g+t",
        "u=rwx,g=rx,o=",
        "0",
        "00000000644",
    ],
)
@pytest.mark.parametrize("mask", [0o002, 0o022, 0o077])
def test_mode_expression(
    executables: tuple[Path, Path], tmp_path: Path, mode: str, mask: int
) -> None:
    # upstream: none - Checks gnulib modechange.c mode_compile/mode_adjust from 0666.
    result, entries = assert_parity(executables, ["-m", mode, "p"], tmp_path, mask=mask)
    assert result == (b"", b"", 0)
    assert stat.S_ISFIFO(entries["p"].kind)


# A MODE that no grammar expression spells is rejected before any creation.
@pytest.mark.parametrize(
    "mode",
    ["bad", "", "u", "+ur", "u+644", "+644u", "+644+r", "u+r,", ",u+r", "u+r,,g+w", "10000", "8"],
)
def test_invalid_mode(executables: tuple[Path, Path], tmp_path: Path, mode: str) -> None:
    # upstream: none - Checks gnulib modechange.c mode_compile rejections.
    result, entries = assert_parity(executables, ["-m", mode, "p", "q"], tmp_path)
    assert result == (b"", INVALID_MODE, 1)
    assert set(entries) == {"."}


# Long MODE strings: one argument stays below Linux's 128 KiB limit.
LONG_MODE = 100_000


@pytest.mark.parametrize(
    "mode",
    [
        pytest.param("0" * LONG_MODE + "600", id="leading-zeros"),
        pytest.param("u" * LONG_MODE + "+r", id="who-letters"),
        pytest.param("a+" + "r" * LONG_MODE, id="permission-letters"),
        pytest.param("+r" * (LONG_MODE // 2), id="actions"),
        pytest.param(",".join(["u+r"] * (LONG_MODE // 4)), id="clauses"),
        pytest.param("+" + "0" * LONG_MODE + "644", id="octal-after-operator"),
    ],
)
def test_long_mode(executables: tuple[Path, Path], tmp_path: Path, mode: str) -> None:
    # upstream: none - Checks that a long MODE is parsed and applied without deep recursion.
    result, entries = assert_parity(executables, ["-m", mode, "p"], tmp_path)
    assert result == (b"", b"", 0)
    assert stat.S_ISFIFO(entries["p"].kind)


@pytest.mark.parametrize(
    "mode",
    [
        pytest.param("7" * LONG_MODE, id="digits"),
        pytest.param("0" * LONG_MODE + "10000", id="leading-zeros"),
    ],
)
def test_long_invalid_mode(executables: tuple[Path, Path], tmp_path: Path, mode: str) -> None:
    # upstream: none - Checks mode_compile's 07777 limit on a long digit run.
    result, entries = assert_parity(executables, ["-m", mode, "p"], tmp_path)
    assert result == (b"", INVALID_MODE, 1)
    assert set(entries) == {"."}


# A MODE whose result has set-ID or sticky bits is rejected before any creation.
@pytest.mark.parametrize("mode", ["u+s", "+s", "+t", "4644", "7777", "g+s,o+t"])
def test_special_bits(executables: tuple[Path, Path], tmp_path: Path, mode: str) -> None:
    # upstream: none - Checks src/mkfifo.c's S_IRWXUGO check after mode_adjust.
    result, entries = assert_parity(executables, ["-m", mode, "p"], tmp_path)
    assert result == (b"", SPECIAL_BITS, 1)
    assert set(entries) == {"."}


# MODE is checked only after an operand is known to exist.
@pytest.mark.parametrize("args", [[], ["-m", "600"], ["-m", "bad"]])
def test_missing_operand(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: none - Checks src/mkfifo.c's missing-operand branch before MODE.
    result, entries = assert_parity(executables, args, tmp_path)
    assert result == (b"", MISSING_OPERAND, 1)
    assert set(entries) == {"."}


# Every kind of existing name is an error that leaves the entry unchanged.
@pytest.mark.parametrize("operand", ["file", "directory", "fifo", "link", "dangling"])
@pytest.mark.parametrize("args", [[], ["-m", "600"]])
def test_existing_name(
    executables: tuple[Path, Path], tmp_path: Path, operand: str, args: list[str]
) -> None:
    # upstream: none - Checks mkfifo(3)'s EEXIST without following a terminal symlink.
    def setup(cwd: Path) -> None:
        (cwd / "file").write_bytes(b"kept")
        (cwd / "directory").mkdir()
        os.mkfifo(cwd / "fifo", 0o600)
        (cwd / "link").symlink_to("file")
        (cwd / "dangling").symlink_to("absent")

    result, entries = assert_parity(executables, [*args, operand], tmp_path, setup)
    assert result[2] == 1
    assert entries["file"].contents == b"kept"
    assert entries["fifo"].mode == 0o600


# Invalid paths report the exact syscall error without creating entries.
@pytest.mark.parametrize("operand", ["", ".", "file/child", "missing/child", "loop/child"])
def test_path_error(executables: tuple[Path, Path], tmp_path: Path, operand: str) -> None:
    # upstream: none - Checks Linux path failures exposed by the shared IO contracts.
    def setup(cwd: Path) -> None:
        (cwd / "file").write_bytes(b"retained")
        (cwd / "loop").symlink_to("loop")

    result, entries = assert_parity(executables, [operand], tmp_path, setup)
    assert result[2] == 1
    assert set(entries) == {".", "file", "loop"}


# A directory without write permission refuses the FIFO; later operands still run.
def test_unwritable_directory(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: none - Checks EACCES from mkfifo(3) and continued processing.
    def setup(cwd: Path) -> None:
        (cwd / "locked").mkdir()
        (cwd / "locked").chmod(0o555)

    result, entries = assert_parity(executables, ["locked/p", "open"], tmp_path, setup)
    assert result[2] == 1
    assert "locked/p" not in entries
    assert stat.S_ISFIFO(entries["open"].kind)


# Earlier FIFOs survive a later failure, and the last operand is still tried.
@pytest.mark.parametrize("args", [[], ["-m", "600"], ["-m", "g+w"]])
def test_partial_effects(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: none - Checks src/mkfifo.c's ordered-operand loop.
    result, entries = assert_parity(
        executables, [*args, "first", "missing/child", "last"], tmp_path
    )
    assert result[2] == 1
    assert set(entries) == {".", "first", "last"}


# A repeated operand is created once and then reported as existing.
def test_repeated_operand(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: none - Checks sequential effects between operands.
    result, entries = assert_parity(executables, ["-m", "640", "p", "p"], tmp_path)
    assert result[2] == 1
    assert entries["p"].mode == 0o640


# Failure diagnostics quote names with GNU's quoteaf rules.
@pytest.mark.parametrize(
    "operand", ["can't/p", "a b/p", "#hash/p", "~tilde/p", "tab\tname/p", "nl\nname/p", "é/p"]
)
def test_quoted_failure(executables: tuple[Path, Path], tmp_path: Path, operand: str) -> None:
    # upstream: none - Checks quoteaf in "cannot create fifo" diagnostics.
    result, entries = assert_parity(executables, [operand], tmp_path)
    assert result[2] == 1
    assert set(entries) == {"."}


# -m may follow operands, repeat (last wins), attach its value or be abbreviated.
@pytest.mark.parametrize(
    "args",
    [
        ["x", "-m", "640", "y"],
        ["-m", "600", "-m", "640", "z"],
        ["-m600", "p"],
        ["--mode", "600", "p"],
        ["--mode=600", "p"],
        ["--mo=700", "p"],
        ["--m", "700", "p"],
    ],
)
def test_mode_option_forms(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    # Port getopt_long permutation, abbreviation and attached-value conventions.
    result, _ = assert_parity(executables, args, tmp_path)
    assert result == (b"", b"", 0)


# A double dash makes option-looking names ordinary operands.
def test_double_dash(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    result, entries = assert_parity(executables, ["--", "-j", "--help"], tmp_path)
    assert result == (b"", b"", 0)
    assert set(entries) == {".", "-j", "--help"}


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
        ["-m", "bad", "--help"],
        ["--help", "-m"],
    ],
)
def test_information_precedence(
    executables: tuple[Path, Path], tmp_path: Path, args: list[str]
) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    result, entries = assert_parity(executables, args, tmp_path)
    assert set(entries) == {"."}
    assert result[2] in (0, 1)


# Malformed options preserve GNU bytes and create nothing.
@pytest.mark.parametrize(
    "args",
    [
        ["--bogus", "p"],
        ["-Q", "p"],
        ["-Qm", "600", "p"],
        ["-m"],
        ["--mode"],
        ["--mo"],
        ["--help=value"],
        ["--version=1"],
        ["--he=x"],
        ["-é", "p"],
        ["--=", "p"],
        ["--=x", "p"],
    ],
)
def test_parse_error(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    result, entries = assert_parity(executables, args, tmp_path)
    assert result[2] == 1
    assert set(entries) == {"."}


def run_with_full_stream(
    executables: tuple[Path, Path], tmp_path: Path, args: list[str], stream: str
) -> tuple[tuple[bytes, bytes, int], tuple[bytes, bytes, int]]:
    """Run both programs with one standard stream connected to /dev/full."""
    reference, candidate = executables
    results = []
    for name, runner in (("reference", "gnu"), ("candidate", "dafny")):
        cwd = tmp_path / name
        cwd.mkdir()
        with Path("/dev/full").open("wb") as full:
            streams = {
                "stdout": full if stream == "stdout" else subprocess.PIPE,
                "stderr": full if stream == "stderr" else subprocess.PIPE,
            }
            common = {
                "cwd": cwd,
                "check": False,
                "env": parity_env(),
                "timeout": BENCH_COMMAND_TIMEOUT_SEC,
                **streams,
            }
            if runner == "gnu":
                done = subprocess.run([UTILITY, *args], executable=str(reference), **common)
            else:
                done = run_candidate(candidate, args, **common)
        results.append((done.stdout or b"", done.stderr or b"", done.returncode, snapshot(cwd)))
    (gout, gerr, gcode, gfs), (dout, derr, dcode, dfs) = results
    assert gfs == dfs
    return (gout, gerr, gcode), (dout, derr, dcode)


# A full stdout does not matter: mkfifo writes nothing there on success.
def test_full_stdout_success(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/write-errors.sh
    # Apply its /dev/full scenario; close_stdout has nothing to flush.
    expected, actual = run_with_full_stream(executables, tmp_path, ["p"], "stdout")
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert expected[2] == 0


# A full stderr keeps the creation effects and the failure status.
def test_full_stderr_failure(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/write-errors.sh
    # Apply its /dev/full scenario to the diagnostic stream.
    expected, actual = run_with_full_stream(
        executables, tmp_path, ["first", "missing/child"], "stderr"
    )
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert expected[2] == 1


# Check specification well-formedness, helpers and the entry obligation separately.
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename",
    [
        "Spec/MkfifoSpec.dfy",
        "Impl/MkfifoModeCore.dfy",
        "Proof/MkfifoModeProof.dfy",
        "Impl/MkfifoCore.dfy",
        "Proof/MkfifoProof.dfy",
        "Impl/Mkfifo.dfy",
    ],
)
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks proof obligations rather than GNU runtime behavior.
    run_dafny_verify(PROJECT / filename)
