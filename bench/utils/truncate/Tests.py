"""Benchmark oracle cases for GNU truncate; separate from development tests/."""

import os
import stat
import subprocess
from pathlib import Path

import pytest

from benchmark_tools.execution import run_candidate
from benchmark_tools.test_support import (
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
UTILITY = "truncate"
PROJECT = ROOT / "bench" / "utils" / UTILITY


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    """Build once for the separate benchmark runtime oracle tier."""
    build_bench_utility(ROOT, UTILITY)
    build_coreutils_utility(ROOT, UTILITY)
    return (
        coreutils_binary_path(ROOT, ROOT / "_build/coreutils/src" / UTILITY),
        bench_dll_path(ROOT, ROOT / "_build/bench" / f"{UTILITY}_bench.dll"),
    )


def fixture(directory: Path) -> None:
    """Create one bounded oracle tree: two directories, four files and four aliases."""
    directory.mkdir()
    (directory / "dir").mkdir()
    (directory / "blocked").mkdir()
    (directory / "a").write_bytes(b"abcdef")
    (directory / "ref").write_bytes(b"1234")
    (directory / "readonly").write_bytes(b"keep")
    (directory / "readonly").chmod(0o444)
    (directory / "dir" / "keep").write_bytes(b"untouched")
    (directory / "link").symlink_to("a")
    (directory / "dangling").symlink_to("new")
    (directory / "loop").symlink_to("loop")
    (directory / "alias").hardlink_to(directory / "a")
    (directory / "blocked").chmod(0o555)


def snapshot(directory: Path) -> dict[str, tuple[object, ...]]:
    """Compare contents, modes, owners, link counts and equivalence of file aliases."""
    observed: dict[str, tuple[object, ...]] = {}
    aliases: dict[tuple[int, int], list[str]] = {}
    for path in sorted(directory.rglob("*")):
        metadata = path.lstat()
        name = str(path.relative_to(directory))
        mode = stat.S_IMODE(metadata.st_mode)
        if path.is_symlink():
            observed[name] = ("symlink", os.readlink(path), mode, metadata.st_uid, metadata.st_gid)
        elif path.is_dir():
            observed[name] = ("directory", mode, metadata.st_uid, metadata.st_gid)
        else:
            assert metadata.st_size <= 16_384, "oracle payload must stay bounded"
            observed[name] = (
                "regular",
                path.read_bytes(),
                mode,
                metadata.st_uid,
                metadata.st_gid,
                metadata.st_nlink,
            )
            aliases.setdefault((metadata.st_dev, metadata.st_ino), []).append(name)
    observed["<aliases>"] = tuple(sorted(tuple(names) for names in aliases.values()))
    return observed


def assert_parity(executables: tuple[Path, Path], args: list[str], directory: Path) -> None:
    """Run one GNU scenario in two small, independent benchmark oracle fixtures."""
    reference_dir = directory / "reference"
    candidate_dir = directory / "candidate"
    fixture(reference_dir)
    fixture(candidate_dir)
    reference, candidate = executables
    try:
        expected = run_coreutils_utility(reference, UTILITY, args, reference_dir)
        actual = run_bench_utility(candidate, args, candidate_dir)
        assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
        assert snapshot(candidate_dir) == snapshot(reference_dir)
    finally:
        (reference_dir / "blocked").chmod(0o755)
        (candidate_dir / "blocked").chmod(0o755)


# Each size form truncates, extends, clamps or rounds one stable regular file.
@pytest.mark.parametrize(
    "size",
    [
        "0",
        "3",
        "10",
        "+2",
        "-2",
        "-99",
        "<3",
        "<9",
        ">3",
        ">9",
        "/4",
        "%4",
        "  <  3",
        "010",
        "1K",
        "1KB",
        "1KiB",
        "1KD",
        "k",
        "0Q",
    ],
)
def test_size_form(executables: tuple[Path, Path], tmp_path: Path, size: str) -> None:
    # upstream: coreutils/tests/truncate/truncate-parameters.sh
    assert_parity(executables, ["-s", size, "a"], tmp_path)


# Each invalid size fails before touching files, preserving exact GNU diagnostics.
@pytest.mark.parametrize(
    "size",
    [
        "",
        " ",
        "+",
        "-",
        "1 ",
        "0x10",
        "1b",
        "1B",
        "+k",
        "++2",
        "1Ki",
        "<+3",
        "> -1",
        "+>0",
        "/0",
        "%0",
        "9223372036854775808",
        "1Q",
    ],
)
def test_invalid_size(executables: tuple[Path, Path], tmp_path: Path, size: str) -> None:
    # upstream: coreutils/tests/truncate/truncate-relative.sh
    assert_parity(executables, ["-s", size, "a"], tmp_path)


# Full signed-64 parser boundaries use no-create missing operands to avoid giant payloads.
@pytest.mark.parametrize("size", ["9223372036854775807", "-9223372036854775808"])
def test_signed_boundary(executables: tuple[Path, Path], tmp_path: Path, size: str) -> None:
    # upstream: coreutils/tests/truncate/truncate-overflow.sh
    assert_parity(executables, ["-c", "-s", size, "missing"], tmp_path)


# Missing operands, incompatible options and parse precedence each retain GNU exit behavior.
@pytest.mark.parametrize(
    "args",
    [
        [],
        ["a"],
        ["-s", "3"],
        ["-r", "ref", "-s", "2", "a"],
        ["-or", "ref", "a"],
        ["--help"],
        ["--version"],
        ["--help", "--bad"],
        ["--bad", "--help"],
        ["-s", "bad", "--help"],
        ["--help", "-s", "bad"],
        ["-s", "bad", "--bad"],
        ["--=x"],
        ["--n=bad"],
        ["--s"],
        ["-s"],
        ["-r"],
        ["-cz"],
        ["-s", "+1", "-s", "+2", "a"],
        ["-s", "/2", "-s", "3", "a"],
        ["-s", "+1", "-s", "2", "a"],
        ["a", "--size=3"],
        ["--si=3", "--", "a"],
    ],
)
def test_cli_scenario(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: coreutils/tests/truncate/truncate-parameters.sh
    assert_parity(executables, args, tmp_path)


# Each pathname scenario compares exact diagnostics and all preceding/succeeding file effects.
@pytest.mark.parametrize(
    "args",
    [
        ["-s", "2", "new"],
        ["-c", "-s", "2", "missing"],
        ["-s", "2", "link"],
        ["-s", "2", "dangling"],
        ["-c", "-s", "2", "dangling"],
        ["-s", "+2", "alias", "a"],
        ["-s", "2", "dir", "a", "missing/child", "ref"],
        ["-cs", "2", "missing/child", "a"],
        ["-s", "2", "new/"],
        ["-s", "2", "a/"],
        ["-s", "2", "loop"],
        ["-s", "2", ""],
        ["-s", "2", "readonly"],
        ["-s", "2", "blocked/new"],
        ["-s", "2", "quote' space"],
        ["-r", "ref", "a"],
        ["-r", "link", "new"],
        ["-r", "ref", "-s", "+2", "new", "a"],
        ["-r", "missing", "a"],
        ["-o", "-s", "1", "a"],
        ["-o", "-s", "9223372036854775807", "new"],
        ["-s", "+9223372036854775807", "a"],
        ["-s", "-9223372036854775808", "a"],
        ["-r", "ref", "-s", "+9223372036854775807", "new"],
    ],
)
def test_filesystem_scenario(
    executables: tuple[Path, Path], tmp_path: Path, args: list[str]
) -> None:
    # upstream: coreutils/tests/truncate/truncate-dangling-symlink.sh
    assert_parity(executables, args, tmp_path)


# Apostrophe diagnostics use GNU's positional double-quote shortcut for these bytes.
@pytest.mark.parametrize("name", ["#can't", "~can't", "at@quote'"])
def test_reference_path_quoting(executables: tuple[Path, Path], tmp_path: Path, name: str) -> None:
    # upstream: none - Regression for strict differential seed1 iteration476.
    assert_parity(executables, ["-r", name, "a"], tmp_path)


# GNU reports a stdout failure for help/version when the output device rejects bytes.
@pytest.mark.parametrize("option", ["--help", "--version"])
def test_stdout_failure(executables: tuple[Path, Path], tmp_path: Path, option: str) -> None:
    # upstream: coreutils/tests/misc/usage_vs_getopt.sh
    reference, candidate = executables
    with Path("/dev/full").open("wb") as output:
        expected = subprocess.run(
            [UTILITY, option],
            executable=str(reference),
            cwd=tmp_path,
            stdout=output,
            stderr=subprocess.PIPE,
            env=parity_env(),
            check=False,
        )
        actual = run_candidate(
            candidate,
            [option],
            cwd=tmp_path,
            stdout=output,
            stderr=subprocess.PIPE,
            env=parity_env(),
            check=False,
        )
    assert expected.returncode == actual.returncode == 1
    assert actual.stderr == expected.stderr


# Verify the complete candidate modules, including the entry's direct Spec postcondition.
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename",
    [
        "Spec/TruncateSpec.dfy",
        "Impl/TruncateCore.dfy",
        "Proof/TruncateProof.dfy",
        "Impl/Truncate.dfy",
    ],
)
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks the declared proof surface, not GNU runtime behavior.
    # upstream-reason: verification.
    run_dafny_verify(PROJECT / filename)
