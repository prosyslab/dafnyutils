"""Bounded GNU differential oracle cases for the mutating cp benchmark."""

import os
import stat
import subprocess
from dataclasses import dataclass
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
UTILITY = "cp"
PROJECT = ROOT / "bench" / "utils" / UTILITY


@dataclass(frozen=True)
class Node:
    kind: int
    mode: int
    uid: int
    gid: int
    links: int
    data: bytes | str | None


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    """Build each target once for the benchmark runtime oracle tier."""
    build_bench_utility(ROOT, UTILITY)
    reference = coreutils_binary_path(ROOT, ROOT / "_build/coreutils/src" / UTILITY)
    if not reference.is_file():
        build_coreutils_utility(ROOT, UTILITY)
    return reference, bench_dll_path(ROOT, ROOT / "_build/bench" / "cp_bench.dll")


def make_fixture(root: Path) -> None:
    """Create thirteen bounded oracle nodes with fewer than 64 data bytes."""
    root.mkdir()
    for name, content, mode in [
        ("src", b"abc\x00\xff\n", 0o640),
        ("old", b"old\n", 0o600),
        ("readonly", b"protected\n", 0o444),
    ]:
        (root / name).write_bytes(content)
        (root / name).chmod(mode)
    os.link(root / "src", root / "alias")
    os.symlink("src", root / "sym")
    os.utime(
        root / "sym",
        ns=(1_234_567_890_000_000_000, 1_234_567_890_000_000_000),
        follow_symlinks=False,
    )
    os.symlink("absent", root / "dangling")
    (root / "destdir").mkdir()
    (root / "tree").mkdir()
    (root / "tree/sub").mkdir()
    (root / "tree/one").write_bytes(b"1\n")
    (root / "tree/sub/two").write_bytes(b"2\n")
    os.symlink("../one", root / "tree/sub/symlink")
    (root / "tree/sub").chmod(0o555)


def snapshot(root: Path) -> tuple[dict[str, Node], list[list[str]]]:
    """Compare complete bounded trees and inode aliases without host inode numbers."""
    nodes: dict[str, Node] = {}
    aliases: dict[tuple[int, int], list[str]] = {}
    for path in [root, *sorted(root.rglob("*"))]:
        value = path.lstat()
        relative = str(path.relative_to(root))
        kind = stat.S_IFMT(value.st_mode)
        data: bytes | str | None = None
        if stat.S_ISLNK(value.st_mode):
            data = os.readlink(path)
        elif stat.S_ISREG(value.st_mode):
            data = path.read_bytes()
        nodes[relative] = Node(
            kind,
            stat.S_IMODE(value.st_mode),
            value.st_uid,
            value.st_gid,
            value.st_nlink,
            data,
        )
        aliases.setdefault((value.st_dev, value.st_ino), []).append(relative)
    return nodes, sorted(sorted(paths) for paths in aliases.values() if len(paths) > 1)


def assert_parity(
    executables: tuple[Path, Path], args: list[str], root: Path, env: dict[str, str] | None = None
) -> tuple[bytes, bytes, int]:
    reference_tree, candidate_tree = root / "reference", root / "candidate"
    make_fixture(reference_tree)
    make_fixture(candidate_tree)
    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree, env=env)
    actual = run_bench_utility(candidate, args, candidate_tree, env=env)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)
    return actual


# Preserve bytes, creation permissions, existing modes, and pre-existing inode aliases.
@pytest.mark.parametrize(
    "args",
    [
        ["src", "out"],
        ["src", "old"],
        ["src", "sym"],
        ["--attributes-only", "src", "old"],
        ["--preserve=mode", "src", "old"],
        ["--no-preserve=mode", "src", "out"],
        ["--no-preserve=mode", "src", "old"],
        ["--preserve=timestamps", "src", "out"],
        ["-v", "src", "out"],
        ["-n", "src", "old"],
        ["-f", "src", "readonly"],
        ["-fv", "src", "readonly"],
        ["--remove-destination", "src", "old"],
    ],
)
def test_regular_file_effects(
    executables: tuple[Path, Path], args: list[str], tmp_path: Path
) -> None:
    # upstream: coreutils/tests/cp/perm.sh
    assert_parity(executables, args, tmp_path)


# Attributes-only must open an existing destination for writing while preserving its bytes.
@pytest.mark.parametrize(
    "options",
    [["--attributes-only"], ["--attributes-only", "-f"], ["--attributes-only", "--preserve=mode"]],
)
def test_attributes_only_destination_permissions(
    executables: tuple[Path, Path], tmp_path: Path, options: list[str]
) -> None:
    # upstream: src/copy.c copy_reg open_flags; fuzz seed1/iteration950.
    assert_parity(executables, [*options, "src", "readonly"], tmp_path)


# Attributes-only still rejects an unreadable source before opening the destination.
def test_attributes_only_source_permissions(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: src/copy.c copy_reg source_desc open before data_copy_required.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    make_fixture(reference_tree)
    make_fixture(candidate_tree)
    for root in (reference_tree, candidate_tree):
        (root / "src").chmod(0)
    try:
        reference, candidate = executables
        args = ["--attributes-only", "src", "old"]
        expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
        actual = run_bench_utility(candidate, args, candidate_tree)
        assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
        for root in (reference_tree, candidate_tree):
            assert stat.S_IMODE((root / "src").stat().st_mode) == 0
            (root / "src").chmod(0o640)
        assert snapshot(candidate_tree) == snapshot(reference_tree)
    finally:
        for root in (reference_tree, candidate_tree):
            (root / "src").chmod(0o640)


# Reject same-inode copies before unlinking, truncating, or creating a self-referential link.
@pytest.mark.parametrize(
    "args",
    [
        ["src", "src"],
        ["src", "alias"],
        ["--remove-destination", "src", "src"],
        ["-s", "src", "src"],
        ["-n", "src", "src"],
        ["--remove-destination", "src", "alias"],
        ["-l", "src", "src"],
        ["-l", "src", "alias"],
    ],
)
def test_same_file_aliases(executables: tuple[Path, Path], args: list[str], tmp_path: Path) -> None:
    # upstream: coreutils/tests/cp/same-file.sh
    assert_parity(executables, args, tmp_path)


# Preserve GNU same-file priority across referents, aliases, removal, backup, and update policies.
@pytest.mark.parametrize(
    "args",
    [
        [*options, source, target]
        for options in [
            ["--remove-destination"],
            ["--backup=existing"],
            ["--update=older"],
            ["--update=none"],
            ["--update=none-fail"],
        ]
        for source, target in [("src", "src"), ("src", "alias"), ("sym", "src"), ("sym", "alias")]
    ]
    + [
        ["sym", "src"],
        ["sym", "alias"],
        ["-P", "sym", "src"],
        ["-P", "--remove-destination", "sym", "src"],
        ["-P", "--backup=existing", "sym", "src"],
        ["-P", "--update=older", "sym", "src"],
        ["-l", "src", "alias"],
        ["-l", "sym", "src"],
        ["-l", "--update=older", "src", "alias"],
        ["-l", "--update=older", "sym", "src"],
        ["-Pl", "sym", "src"],
        ["-Pl", "--remove-destination", "sym", "src"],
        ["-s", "--remove-destination", "src", "alias"],
        ["-s", "--remove-destination", "sym", "src"],
        ["-Ps", "sym", "src"],
        ["-s", "--backup=existing", "src", "alias"],
    ],
)
def test_same_file_policy_order(
    executables: tuple[Path, Path], args: list[str], tmp_path: Path
) -> None:
    # upstream: src/copy.c same_file_ok and UPDATE_OLDER handling before return_now.
    assert_parity(executables, args, tmp_path)


# Refuse a backup that would move a symlink source's regular referent before reading it.
@pytest.mark.parametrize("args", [["--backup=existing", "sym", "src"], ["-b", "sym", "alias"]])
def test_backup_symlink_referent(
    executables: tuple[Path, Path], tmp_path: Path, args: list[str]
) -> None:
    # upstream: src/copy.c same_file_ok backup guard; fuzz seed19/iteration102.
    assert_parity(executables, args, tmp_path)


# Preserve GNU's later open failure and backup rollback through a two-symlink chain.
def test_backup_symlink_chain(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: src/copy.c same_file_ok FIXME a -> b -> c, cp -b a b.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    for root in (reference_tree, candidate_tree):
        make_fixture(root)
        os.symlink("sym", root / "chain")
    reference, candidate = executables
    args = ["-b", "chain", "sym"]
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
    actual = run_bench_utility(candidate, args, candidate_tree)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# Distinguish copied symlinks, dereferenced source links, explicit links, and dangling destinations.
@pytest.mark.parametrize(
    "args",
    [
        ["sym", "out"],
        ["-P", "sym", "out"],
        ["-P", "sym", "old"],
        ["src", "dangling"],
        ["--remove-destination", "src", "dangling"],
        ["-l", "src", "out"],
        ["-l", "src", "old"],
        ["-s", "src", "old"],
        ["-lP", "sym", "out"],
        ["-l", "sym", "out"],
        ["-s", "src", "out"],
        ["-s", "src", "tree/out"],
        ["-P", "sym", "tree/sub/out"],
        ["-v", "--remove-destination", "src", "old"],
    ],
)
def test_link_policies(executables: tuple[Path, Path], args: list[str], tmp_path: Path) -> None:
    # upstream: coreutils/tests/cp/link-deref.sh
    assert_parity(executables, args, tmp_path)


# Keep existing destination entries as GNU simple, existing, or numbered backups.
@pytest.mark.parametrize(
    "args",
    [
        ["-b", "src", "old"],
        ["--backup", "src", "old"],
        ["--backup=simple", "src", "old"],
        ["--backup=numbered", "src", "old"],
        ["--backup=existing", "src", "old"],
        ["--backup", "src", "dangling"],
        ["-Rb", "tree", "old"],
        ["-Rvb", "tree", "old"],
        ["-Tb", "src", "tree"],
        ["--backup=t", "-v", "src", "old"],
        ["-S", ".save", "src", "old"],
        ["--suffix=", "src", "old"],
        ["--suffix=bad/path", "src", "old"],
        ["--backup=none", "src", "alias"],
        ["-b", "src", "alias"],
        ["-fb", "src", "src"],
        ["--backup", "--update=none", "src", "old"],
        ["--backup=bad", "src", "old"],
        ["--backup=n", "src", "old"],
    ],
)
def test_backups(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: tests/cp/backup-1.sh and backup-is-src.sh.
    assert_parity(executables, args, tmp_path)


# Select one greater than the highest existing backup even when version numbers have gaps.
@pytest.mark.parametrize("control", ["numbered", "existing"])
def test_numbered_backup_gap(executables: tuple[Path, Path], tmp_path: Path, control: str) -> None:
    # upstream: gnulib/lib/backupfile.c numbered_backup.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    for root in (reference_tree, candidate_tree):
        make_fixture(root)
        (root / "old.~3~").write_bytes(b"3")
        (root / "old.~7~").write_bytes(b"7")
    reference, candidate = executables
    args = [f"--backup={control}", "src", "old"]
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
    actual = run_bench_utility(candidate, args, candidate_tree)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# Resolve GNU backup environment controls without consuming the following source operand.
@pytest.mark.parametrize(
    "values",
    [
        {"VERSION_CONTROL": "numbered"},
        {"VERSION_CONTROL": "simple", "SIMPLE_BACKUP_SUFFIX": ".save"},
        {"VERSION_CONTROL": "invalid"},
        {"VERSION_CONTROL": ""},
    ],
)
def test_backup_environment(
    executables: tuple[Path, Path], tmp_path: Path, values: dict[str, str]
) -> None:
    # upstream: gnulib/lib/backup-find.c xget_version and backupfile.c set_simple_backup_suffix.
    env = parity_env()
    env.update(values)
    assert_parity(executables, ["--backup", "src", "old"], tmp_path, env)


# Restore the old destination backup after the source cannot be opened.
def test_backup_rollback(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: src/copy.c un_backup; tests/cp/backup-1.sh.
    source = tmp_path / "unreadable"
    source.write_bytes(b"x")
    source.chmod(0)
    assert_parity(executables, ["-vb", "../unreadable", "old"], tmp_path)


# Copy the complete source pathname and restore private intermediate permissions.
@pytest.mark.parametrize(
    "args",
    [
        ["--parents", "tree/sub/two", "destdir"],
        ["-v", "--parents", "tree/sub/two", "destdir"],
        ["--parents", "--preserve=mode,timestamps", "tree/sub/two", "destdir"],
        ["--parents", "--no-preserve=mode", "tree/sub/two", "destdir"],
        ["--parents", "-R", "tree/sub", "destdir"],
        ["--parents", "src/child", "destdir"],
        ["--parents", "missing/sub/file", "destdir"],
        ["--parents", "tree/sub/two", "out"],
    ],
)
def test_parents(executables: tuple[Path, Path], tmp_path: Path, args: list[str]) -> None:
    # upstream: tests/cp/cp-parents.sh.
    assert_parity(executables, args, tmp_path)


# Preserve aliases across separate source operands without linking to the source.
@pytest.mark.parametrize("option", ["-d", "--preserve=links", "--preserve=l,mode,timestamps"])
def test_preserve_links(executables: tuple[Path, Path], tmp_path: Path, option: str) -> None:
    # upstream: tests/cp/link-preserve.sh.
    assert_parity(executables, [option, "src", "alias", "destdir"], tmp_path)


# Parse GNU optional long arguments only when attached, including abbreviated values.
@pytest.mark.parametrize(
    "args",
    [
        ["--update", "src", "old"],
        ["--update=a", "src", "out"],
        ["--update=n", "src", "out"],
        ["--preserve=t,m", "src", "out"],
        ["--no-preserve=all", "src", "out"],
        ["--preserve=mode,unknown", "src", "out"],
        ["--preserve=", "src", "out"],
        ["-t", "--update", "src"],
        ["--target-directory", "--preserve", "src"],
    ],
)
def test_optional_arguments(
    executables: tuple[Path, Path], tmp_path: Path, args: list[str]
) -> None:
    # upstream: src/cp.c decode_preserve_arg and getopt_long; tests/cp/preserve-mode.sh.
    assert_parity(executables, args, tmp_path)


# Refuse loss of an earlier operand when two distinct sources share a destination basename.
@pytest.mark.parametrize(
    "options", [[], ["-v"], ["-l"], ["-b"], ["--backup=numbered"], ["--parents"]]
)
def test_just_created_destination(
    executables: tuple[Path, Path], tmp_path: Path, options: list[str]
) -> None:
    # upstream: src/copy.c dest_info guard; tests/cp/copy-FMR.sh.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    for root in (reference_tree, candidate_tree):
        make_fixture(root)
        for name, content in [("left", b"L"), ("right", b"R")]:
            (root / name).mkdir()
            (root / name / "file").write_bytes(content)
    reference, candidate = executables
    args = [*options, "left/file", "right/file", "destdir"]
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
    actual = run_bench_utility(candidate, args, candidate_tree)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# Refuse to copy a later source through a symlink created by an earlier operand.
def test_just_created_symlink(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: src/copy.c command-line symlink dest_info guard.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    for root in (reference_tree, candidate_tree):
        make_fixture(root)
        (root / "left").mkdir()
        (root / "right").mkdir()
        os.symlink("../src", root / "left/file")
        (root / "right/file").write_bytes(b"R")
    reference, candidate = executables
    args = ["-P", "left/file", "right/file", "destdir"]
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
    actual = run_bench_utility(candidate, args, candidate_tree)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# A skipped newer destination supplies the preserved alias when the later name is new.
def test_update_preserved_alias(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: src/copy.c UPDATE_OLDER remember_copied branch; tests/cp/link-preserve.sh.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    for root in (reference_tree, candidate_tree):
        make_fixture(root)
        (root / "destdir/src").write_bytes(b"new")
        os.utime(root / "destdir/src", ns=(2_000_000_000_000_000_000, 2_000_000_000_000_000_000))
    reference, candidate = executables
    args = ["-u", "--preserve=links", "src", "alias", "destdir"]
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
    actual = run_bench_utility(candidate, args, candidate_tree)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# POSIXLY_CORRECT follows an existing dangling destination and creates its referent.
def test_posix_dangling_destination(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: src/cp.c cp_option_init open_dangling_dest_symlink.
    env = parity_env()
    env["POSIXLY_CORRECT"] = ""
    assert_parity(executables, ["src", "dangling"], tmp_path, env)


# Restrictive umasks cannot prevent temporary owner access while a directory tree is copied.
@pytest.mark.parametrize(
    "options", [["-R"], ["-R", "--no-preserve=mode"], ["-R", "--preserve=mode"]]
)
def test_recursive_restrictive_umask(
    executables: tuple[Path, Path], tmp_path: Path, options: list[str]
) -> None:
    # upstream: tests/cp/preserve-mode.sh; src/copy.c new-directory temporary permissions.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    make_fixture(reference_tree)
    make_fixture(candidate_tree)
    try:
        reference, candidate = executables
        args = [*options, "tree", "copy"]
        expected = subprocess.run(
            [UTILITY, *args],
            executable=str(reference),
            cwd=reference_tree,
            env=parity_env(),
            preexec_fn=lambda: os.umask(0o300),
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
        )
        actual = run_candidate(
            candidate,
            args,
            cwd=candidate_tree,
            env=parity_env(),
            preexec_fn=lambda: os.umask(0o300),
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
        )
        assert_result_matches_reference(
            (expected.stdout, expected.stderr, expected.returncode),
            (actual.stdout, actual.stderr, actual.returncode),
            ignore_stderr_when_exit_nonzero=False,
        )
        # Restore read/search access only after comparing the inaccessible final mode,
        # so the bounded oracle can inspect copied file bytes during snapshotting.
        for root in (reference_tree, candidate_tree):
            assert stat.S_IMODE((root / "copy").stat().st_mode) == (
                0o755
                if "--preserve=mode" in options
                else (0o477 if "--no-preserve=mode" in options else 0o455)
            )
            (root / "copy").chmod(0o755)
            assert stat.S_IMODE((root / "copy/sub").stat().st_mode) == (
                0o555
                if "--preserve=mode" in options
                else (0o477 if "--no-preserve=mode" in options else 0o455)
            )
            (root / "copy/sub").chmod(0o755)
        assert snapshot(candidate_tree) == snapshot(reference_tree)
    finally:
        # These eight known directories are the entire restrictive fixture domain.
        for root in (reference_tree, candidate_tree):
            for relative in ("tree", "tree/sub", "copy", "copy/sub"):
                path = root / relative
                if path.is_dir() and not path.is_symlink():
                    path.chmod(0o755)


# Stop sibling traversal after self-copy detection, retaining only preceding partial effects.
def test_recursive_self_copy_stops_later_alias(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    # upstream: src/copy.c copy_dir local_copy_into_self break; fuzz seed1/iteration328.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    for root in (reference_tree, candidate_tree):
        root.mkdir()
        allocated = [root / f"inode-{i}" for i in range(4)]
        for path in allocated:
            path.mkdir()
        # savedir sorts by d_ino: align the two inputs without assuming allocation order.
        for path, name in zip(
            sorted(allocated, key=lambda path: path.stat().st_ino),
            ("before", "source", "copy", "later"),
            strict=True,
        ):
            path.rename(root / name)
        (root / "before/value").write_bytes(b"x")
        os.symlink("missing", root / "source/broken")
        os.symlink("../source", root / "later/alias")
    reference, candidate = executables
    args = ["-R", "-L", ".", "copy"]
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
    actual = run_bench_utility(candidate, args, candidate_tree)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# Skip actual backups for dot sources while retaining exact replacement and self-copy effects.
@pytest.mark.parametrize("source", [".", "inside/.."])
@pytest.mark.parametrize("options", [[], ["-v"], ["--attributes-only"]])
def test_recursive_dot_backup_destination(
    executables: tuple[Path, Path], tmp_path: Path, source: str, options: list[str]
) -> None:
    # upstream: src/copy.c dot_or_dotdot backup guard; fuzz seed19/iteration249.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    for root in (reference_tree, candidate_tree):
        root.mkdir()
        (root / "inside").mkdir()
        (root / "inside/target").write_bytes(b"x")
    reference, candidate = executables
    args = ["-r", "--backup=nil", *options, source, "inside/target"]
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
    actual = run_bench_utility(candidate, args, candidate_tree)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# Detect self-copy after backing up an ordinary directory source's existing file target.
def test_recursive_backup_file_target_self_copy(
    executables: tuple[Path, Path], tmp_path: Path
) -> None:
    # upstream: src/copy.c copy_dir local_copy_into_self and backup_file_rename.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    for root in (reference_tree, candidate_tree):
        root.mkdir()
        (root / "inside").mkdir()
        (root / "inside/target").write_bytes(b"x")
    reference, candidate = executables
    args = ["-r", "--backup=nil", "inside", "inside/target"]
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
    actual = run_bench_utility(candidate, args, candidate_tree)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# Keep the native sticky bit on newly created --parents directories after a missing leaf.
@pytest.mark.parametrize("options", [[], ["--no-preserve=mode"], ["--preserve=mode"]])
def test_parents_special_mode_missing_leaf(
    executables: tuple[Path, Path], tmp_path: Path, options: list[str]
) -> None:
    # upstream: src/cp.c make_dir_parents_private CHMOD_MODE_BITS; fuzz seed1/iteration61.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    for root in (reference_tree, candidate_tree):
        make_fixture(root)
        (root / "tree/sub").chmod(0o1777)
    reference, candidate = executables
    args = ["--parents", *options, "tree/sub/missing", "destdir"]
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
    actual = run_bench_utility(candidate, args, candidate_tree)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# Recursive creation keeps native directory special bits and applies requested preservation.
@pytest.mark.parametrize("mode", [0o1777, 0o2777, 0o4777])
@pytest.mark.parametrize("options", [[], ["--no-preserve=mode"], ["--preserve=mode"]])
def test_recursive_special_modes(
    executables: tuple[Path, Path], tmp_path: Path, mode: int, options: list[str]
) -> None:
    # upstream: src/copy.c omitted_permissions and restore_dst_mode.
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    for root in (reference_tree, candidate_tree):
        make_fixture(root)
        (root / "tree").chmod(mode)
    reference, candidate = executables
    args = ["-R", *options, "tree", "copy"]
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
    actual = run_bench_utility(candidate, args, candidate_tree)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# Preserve a symlink's requested mtime without dereferencing its target.
def test_preserve_symlink_mtime(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/cp/preserve-slink-time.sh
    assert_parity(executables, ["-P", "--preserve=timestamps", "sym", "out"], tmp_path)
    for side in ["reference", "candidate"]:
        tree = tmp_path / side
        assert (tree / "out").lstat().st_mtime_ns == (tree / "sym").lstat().st_mtime_ns


# Recursively reproduce directories, modes, symlinks, verbose order, and copy-into-self effects.
@pytest.mark.parametrize(
    "args",
    [
        ["-R", "tree", "copy"],
        ["-RL", "tree", "copy"],
        ["-RH", "tree", "copy"],
        ["-Rx", "tree", "copy"],
        ["-R", "--no-preserve=mode", "tree", "copy"],
        ["-R", "tree", "tree/inside"],
        ["-R", "tree", "tree/one"],
    ],
)
def test_recursive_effects(executables: tuple[Path, Path], args: list[str], tmp_path: Path) -> None:
    # upstream: coreutils/tests/cp/into-self.sh
    assert_parity(executables, args, tmp_path)


# Use identical source inode observations for GNU's exact recursive verbose ordering.
def test_recursive_verbose_order(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/cp/copy-FMR.sh
    # GNU savedir sorts by d_ino; sharing read-only source nodes preserves that input.
    make_fixture(tmp_path / "source")
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    reference_tree.mkdir()
    candidate_tree.mkdir()
    args = ["-Rv", "../source/tree", "copy"]
    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, args, reference_tree)
    actual = run_bench_utility(candidate, args, candidate_tree)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# Keep successful earlier operands when another source fails and continue to later operands.
@pytest.mark.parametrize(
    "args",
    [
        ["src", "old", "tree"],
        ["-t", "tree", "src", "old"],
        ["src", "missing", "old", "tree"],
        ["src", "src", "tree"],
        ["src", "./src", "destdir"],
        ["-b", "src", "src", "destdir"],
        ["--backup=numbered", "src", "src", "destdir"],
        ["missing", "missing", "tree"],
        ["-R", "tree", "tree", "destdir"],
        ["-R", "tree", "./tree", "destdir"],
        ["-R", "tree", "tree", "tree/sub"],
        ["src", "alias", "tree"],
    ],
)
def test_multiple_source_effects(
    executables: tuple[Path, Path], args: list[str], tmp_path: Path
) -> None:
    # upstream: coreutils/tests/cp/copy-FMR.sh
    assert_parity(executables, args, tmp_path)


# Preserve exact GNU diagnostics and exit codes for malformed operands and option forms.
@pytest.mark.parametrize(
    "args",
    [
        [],
        ["src"],
        ["missing", "out"],
        ["src", "missing/out"],
        ["tree", "out"],
        ["-T", "src", "old", "tree"],
        ["-t", "missing", "src"],
        ["src", "old", "missing"],
        ["--help=bad"],
        ["--not-an-option"],
        ["-t"],
    ],
)
def test_error_results(executables: tuple[Path, Path], args: list[str], tmp_path: Path) -> None:
    # upstream: coreutils/tests/cp/abuse.sh
    assert_parity(executables, args, tmp_path)


# Honor GNU help/version precedence, including an earlier help request before a later parse error.
@pytest.mark.parametrize(
    "args", [["--help"], ["--version"], ["--help", "--bad"], ["--version", "--help"]]
)
def test_information_requests(
    executables: tuple[Path, Path], args: list[str], tmp_path: Path
) -> None:
    # upstream: coreutils/tests/misc/help-version.sh
    assert_parity(executables, args, tmp_path)


# Report a verbose stdout write failure after retaining the completed file copy.
def test_verbose_stdout_full(executables: tuple[Path, Path], tmp_path: Path) -> None:
    # upstream: coreutils/tests/misc/close-stdout.sh and tests/cp/copy-FMR.sh
    reference_tree, candidate_tree = tmp_path / "reference", tmp_path / "candidate"
    make_fixture(reference_tree)
    make_fixture(candidate_tree)
    reference, candidate = executables
    args = ["-v", "src", "out"]
    with Path("/dev/full").open("wb", buffering=0) as full:
        expected = subprocess.run(
            [UTILITY, *args],
            executable=str(reference),
            cwd=reference_tree,
            input=b"",
            stdout=full,
            stderr=subprocess.PIPE,
            env=parity_env(),
            check=False,
            timeout=60,
        )
        actual = run_candidate(
            candidate,
            args,
            cwd=candidate_tree,
            input=b"",
            stdout=full,
            stderr=subprocess.PIPE,
            env=parity_env(),
            check=False,
            text=False,
            timeout=60,
        )
    assert (actual.stderr, actual.returncode) == (expected.stderr, expected.returncode)
    assert snapshot(candidate_tree) == snapshot(reference_tree)


# Verify the implementation, connecting proof, and required direct entry postcondition separately.
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename",
    [
        "Spec/CpSpec.dfy",
        "Impl/CpCore.dfy",
        "Proof/CpPathProof.dfy",
        "Proof/CpProof.dfy",
        "Impl/Cp.dfy",
    ],
)
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks the fixed Dafny proof contract rather than GNU runtime output.
    run_dafny_verify(PROJECT / filename)
