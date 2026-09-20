"""Check mv rename parity against GNU coreutils and verify its Dafny proof surface."""

import fcntl
import os
import re
import tempfile
from pathlib import Path

import pytest

from tools.bench.bench_test_support import (
    assert_requested_message_behavior,
    assert_result_matches_reference,
    bench_dll_path,
    build_bench_utility,
    build_coreutils_utility,
    coreutils_binary_path,
    evaluation_target_root,
    latest_bench_utility_source_mtime,
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])

DEFAULT_COREUTILS_MV = ROOT / "_build" / "coreutils" / "src" / "mv"
BENCH_MV_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "mv_bench.dll")
COREUTILS_MV = coreutils_binary_path(ROOT, DEFAULT_COREUTILS_MV)
MV_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "mv" / "MvSchema.dfy",
    ROOT / "bench" / "utils" / "mv" / "MvCore.dfy",
    ROOT / "bench" / "utils" / "mv" / "MvSpec.dfy",
    ROOT / "bench" / "utils" / "mv" / "MvProof.dfy",
    ROOT / "bench" / "utils" / "mv" / "Mv.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_mv_once(request: pytest.FixtureRequest) -> None:
    # Source verification needs no candidate or GNU executable build.
    if request.session.items and all(
        item.get_closest_marker("dafny_verify") for item in request.session.items
    ):
        return
    lock_path = ROOT / "_build" / "bench" / ".build_bench_lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("w", encoding="utf-8") as lock_file:
        fcntl.flock(lock_file, fcntl.LOCK_EX)
        if (
            not BENCH_MV_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "mv") > BENCH_MV_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "mv")
        if not COREUTILS_MV.exists():
            build_coreutils_utility(ROOT, "mv")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_mv(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_MV_DLL, args, cwd)


def run_system_mv(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_MV, "mv", args, cwd)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
    *,
    ignore_stderr_when_exit_nonzero: bool = True,
) -> None:
    def normalize_help_hint(stderr: bytes) -> bytes:
        text = stderr.decode("latin1")
        text = re.sub(
            r"Try '.*mv --help' for more information\.\n",
            "Try 'mv --help' for more information.\n",
            text,
        )
        return text.encode("latin1")

    assert_result_matches_reference(
        ref_result,
        bench_result,
        ignore_stderr_when_exit_nonzero=ignore_stderr_when_exit_nonzero,
        stderr_normalizer=normalize_help_hint,
    )


def test_missing_operand_and_destination_match_coreutils() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_same_result(run_system_mv([], cwd), run_bench_mv([], cwd))
        assert_same_result(run_system_mv(["source"], cwd), run_bench_mv(["source"], cwd))


def test_rename_regular_file_preserves_contents() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "source.txt").write_bytes(b"payload\n")

        args = ["source.txt", "renamed.txt"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert not (ref_cwd / "source.txt").exists()
        assert not (bench_cwd / "source.txt").exists()
        assert (ref_cwd / "renamed.txt").read_bytes() == b"payload\n"
        assert (bench_cwd / "renamed.txt").read_bytes() == b"payload\n"


def test_move_file_into_existing_directory_with_verbose_output() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "dest").mkdir()
            (cwd / "source.txt").write_bytes(b"payload\n")

        args = ["-v", "source.txt", "dest"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert (ref_cwd / "dest" / "source.txt").read_bytes() == b"payload\n"
        assert (bench_cwd / "dest" / "source.txt").read_bytes() == b"payload\n"


def test_target_directory_option_moves_multiple_sources() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "dest").mkdir()
            (cwd / "a.txt").write_bytes(b"a\n")
            (cwd / "b.txt").write_bytes(b"b\n")

        args = ["-t", "dest", "a.txt", "b.txt"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        for name, payload in [("a.txt", b"a\n"), ("b.txt", b"b\n")]:
            assert (ref_cwd / "dest" / name).read_bytes() == payload
            assert (bench_cwd / "dest" / name).read_bytes() == payload


def test_no_target_directory_rejects_directory_destination() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "dest").mkdir()
            (cwd / "source.txt").write_bytes(b"payload\n")

        args = ["-T", "source.txt", "dest"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)

        assert (ref_cwd / "source.txt").exists()
        assert (bench_cwd / "source.txt").exists()
        assert not (ref_cwd / "dest" / "source.txt").exists()
        assert not (bench_cwd / "dest" / "source.txt").exists()


def test_no_target_directory_rejects_nonempty_directory_destination() -> None:
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/dir2dir.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "srcdir").mkdir()
            (cwd / "full-dest").mkdir()
            (cwd / "full-dest" / "entry").write_bytes(b"payload\n")

        args = ["-T", "srcdir", "full-dest"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)


def test_move_directory_into_its_child_reports_dedicated_diagnostic() -> None:
    # upstream: coreutils/tests/mv/into-self.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "srcdir").mkdir()

        args = ["srcdir", "srcdir/child"]
        expected = (
            b"",
            b"mv: cannot move 'srcdir' to a subdirectory of itself, 'srcdir/child'\n",
            1,
        )
        assert run_system_mv(args, ref_cwd) == expected
        assert run_bench_mv(args, bench_cwd) == expected


# Preserve the dedicated diagnostic when the descendant target is absolute.
def test_move_relative_directory_to_absolute_child_reports_dedicated_diagnostic() -> None:
    # upstream: none - Extends the self-subdirectory diagnostic to an absolute
    # destination spelling absent from GNU's relative-path test.
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "srcdir").mkdir()

        ref_target = str(ref_cwd / "srcdir" / "child")
        bench_target = str(bench_cwd / "srcdir" / "child")
        ref_expected = (
            b"",
            f"mv: cannot move 'srcdir' to a subdirectory of itself, '{ref_target}'\n".encode(),
            1,
        )
        bench_expected = (
            b"",
            f"mv: cannot move 'srcdir' to a subdirectory of itself, '{bench_target}'\n".encode(),
            1,
        )
        assert run_system_mv(["srcdir", ref_target], ref_cwd) == ref_expected
        assert run_bench_mv(["srcdir", bench_target], bench_cwd) == bench_expected


# Preserve GNU's cannot-stat diagnostic for an empty source operand.
def test_empty_source_path_reports_cannot_stat() -> None:
    # upstream: none - Covers empty-source cannot-stat diagnostics and error
    # ordering absent from GNU mv tests.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        expected = (b"", b"mv: cannot stat '': No such file or directory\n", 1)
        assert run_system_mv(["", "child"], cwd) == expected
        assert run_bench_mv(["", "child"], Path(tmp_dir)) == expected


# Preserve GNU's cannot-stat diagnostic for a symlink loop in the source path.
def test_symlink_loop_in_source_path_reports_cannot_stat() -> None:
    # upstream: none - Covers ELOOP propagation through source metadata lookup
    # absent from GNU mv tests.
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "loop").symlink_to("loop")

        args = ["loop/source", "child"]
        expected = (
            b"",
            b"mv: cannot stat 'loop/source': Too many levels of symbolic links\n",
            1,
        )
        assert run_system_mv(args, ref_cwd) == expected
        assert run_bench_mv(args, bench_cwd) == expected


# Preserve the general rename failure instead of treating an empty target as self-descendant.
def test_empty_target_path_is_not_self_descendant() -> None:
    # upstream: none - Guards against treating an empty rename target as a
    # self-descendant and preserves the source.
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "f").write_bytes(b"payload\n")

        args = ["f", ""]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)

        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)
        for cwd in [ref_cwd, bench_cwd]:
            assert [path.name for path in cwd.iterdir()] == ["f"]
            assert (cwd / "f").read_bytes() == b"payload\n"


def test_no_clobber_preserves_existing_destination_and_source() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "source.txt").write_bytes(b"new\n")
            (cwd / "dest.txt").write_bytes(b"old\n")

        args = ["-n", "source.txt", "dest.txt"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert (ref_cwd / "source.txt").read_bytes() == b"new\n"
        assert (bench_cwd / "source.txt").read_bytes() == b"new\n"
        assert (ref_cwd / "dest.txt").read_bytes() == b"old\n"
        assert (bench_cwd / "dest.txt").read_bytes() == b"old\n"


def test_no_copy_same_filesystem_rename_matches_coreutils() -> None:
    # upstream: coreutils/tests/mv/no-copy.sh
    # Upstream no-copy semantics are observable only after cross-device rename failures.
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "source.txt").write_bytes(b"payload\n")

        args = ["--no-copy", "source.txt", "renamed.txt"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert not (ref_cwd / "source.txt").exists()
        assert not (bench_cwd / "source.txt").exists()
        assert (ref_cwd / "renamed.txt").read_bytes() == b"payload\n"
        assert (bench_cwd / "renamed.txt").read_bytes() == b"payload\n"


def test_backup_numbered_preserves_old_destination_as_numbered_backup() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "source.txt").write_bytes(b"new\n")
            (cwd / "dest.txt").write_bytes(b"old\n")

        args = ["-v", "--backup=numbered", "source.txt", "dest.txt"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert not (ref_cwd / "source.txt").exists()
        assert not (bench_cwd / "source.txt").exists()
        assert (ref_cwd / "dest.txt").read_bytes() == b"new\n"
        assert (bench_cwd / "dest.txt").read_bytes() == b"new\n"
        assert (ref_cwd / "dest.txt.~1~").read_bytes() == b"old\n"
        assert (bench_cwd / "dest.txt.~1~").read_bytes() == b"old\n"


def test_backup_suffix_short_option_uses_requested_suffix() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "source.txt").write_bytes(b"new\n")
            (cwd / "dest.txt").write_bytes(b"old\n")

        args = ["-v", "-b", "-S", ".bak", "source.txt", "dest.txt"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert not (ref_cwd / "source.txt").exists()
        assert not (bench_cwd / "source.txt").exists()
        assert (ref_cwd / "dest.txt").read_bytes() == b"new\n"
        assert (bench_cwd / "dest.txt").read_bytes() == b"new\n"
        assert (ref_cwd / "dest.txt.bak").read_bytes() == b"old\n"
        assert (bench_cwd / "dest.txt.bak").read_bytes() == b"old\n"


def test_debug_reports_skipped_no_clobber_target() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "source.txt").write_bytes(b"new\n")
            (cwd / "dest.txt").write_bytes(b"old\n")

        args = ["--debug", "-n", "source.txt", "dest.txt"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert (ref_cwd / "source.txt").read_bytes() == b"new\n"
        assert (bench_cwd / "source.txt").read_bytes() == b"new\n"
        assert (ref_cwd / "dest.txt").read_bytes() == b"old\n"
        assert (bench_cwd / "dest.txt").read_bytes() == b"old\n"


def test_strip_trailing_slashes_normalizes_source_operand() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "dir").mkdir()

        args = ["--strip-trailing-slashes", "dir////", "moved"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert not (ref_cwd / "dir").exists()
        assert not (bench_cwd / "dir").exists()
        assert (ref_cwd / "moved").is_dir()
        assert (bench_cwd / "moved").is_dir()


def test_update_none_skips_existing_destination_without_error() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "source.txt").write_bytes(b"new\n")
            (cwd / "dest.txt").write_bytes(b"old\n")

        args = ["--debug", "--update=none", "source.txt", "dest.txt"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert (ref_cwd / "source.txt").read_bytes() == b"new\n"
        assert (bench_cwd / "source.txt").read_bytes() == b"new\n"
        assert (ref_cwd / "dest.txt").read_bytes() == b"old\n"
        assert (bench_cwd / "dest.txt").read_bytes() == b"old\n"


def test_update_none_fail_reports_not_replacing_target() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "source.txt").write_bytes(b"new\n")
            (cwd / "dest.txt").write_bytes(b"old\n")

        args = ["--update=none-fail", "source.txt", "dest.txt"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert (ref_cwd / "source.txt").read_bytes() == b"new\n"
        assert (bench_cwd / "source.txt").read_bytes() == b"new\n"
        assert (ref_cwd / "dest.txt").read_bytes() == b"old\n"
        assert (bench_cwd / "dest.txt").read_bytes() == b"old\n"


def test_update_older_skips_when_destination_is_newer() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "source.txt").write_bytes(b"new\n")
            (cwd / "dest.txt").write_bytes(b"old\n")
            os.utime(cwd / "source.txt", (1_700_000_100, 1_700_000_100))
            os.utime(cwd / "dest.txt", (1_700_000_200, 1_700_000_200))

        args = ["--debug", "--update=older", "source.txt", "dest.txt"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert (ref_cwd / "source.txt").read_bytes() == b"new\n"
        assert (bench_cwd / "source.txt").read_bytes() == b"new\n"
        assert (ref_cwd / "dest.txt").read_bytes() == b"old\n"
        assert (bench_cwd / "dest.txt").read_bytes() == b"old\n"


def test_update_short_option_moves_when_source_is_newer() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "source.txt").write_bytes(b"new\n")
            (cwd / "dest.txt").write_bytes(b"old\n")
            os.utime(cwd / "source.txt", (1_700_000_300, 1_700_000_300))
            os.utime(cwd / "dest.txt", (1_700_000_200, 1_700_000_200))

        args = ["-u", "source.txt", "dest.txt"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert not (ref_cwd / "source.txt").exists()
        assert not (bench_cwd / "source.txt").exists()
        assert (ref_cwd / "dest.txt").read_bytes() == b"new\n"
        assert (bench_cwd / "dest.txt").read_bytes() == b"new\n"


def test_invalid_backup_argument_matches_coreutils() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["--backup=bogus", "source.txt", "dest.txt"]
        assert_same_result(run_system_mv(args, cwd), run_bench_mv(args, cwd))


def test_invalid_update_argument_matches_coreutils() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["--update=bogus", "source.txt", "dest.txt"]
        assert_same_result(run_system_mv(args, cwd), run_bench_mv(args, cwd))


def test_symlink_operand_is_renamed_as_link() -> None:
    # upstream: coreutils/tests/mv/diag.sh
    # upstream: coreutils/tests/mv/mv-n.sh
    # upstream: coreutils/tests/mv/no-target-dir.sh
    # upstream: coreutils/tests/mv/mv-special-1.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "target.txt").write_bytes(b"target\n")
            (cwd / "link").symlink_to("target.txt")

        args = ["link", "renamed-link"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)
        assert_same_result(ref, bench)

        assert os.readlink(ref_cwd / "renamed-link") == "target.txt"
        assert os.readlink(bench_cwd / "renamed-link") == "target.txt"
        assert not (ref_cwd / "link").exists()
        assert not (bench_cwd / "link").exists()


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_mv(["--help"], cwd),
            run_bench_mv(["--help"], cwd),
        )
        assert_requested_message_behavior(
            run_system_mv(["--version"], cwd),
            run_bench_mv(["--version"], cwd),
        )


# Preserve GNU's same-entry rejection without changing the sole file.
def test_same_path_reports_same_file() -> None:
    # upstream: coreutils/tests/mv/force.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "f").write_bytes(b"payload\n")

        ref = run_system_mv(["f", "f"], ref_cwd)
        bench = run_bench_mv(["f", "f"], bench_cwd)

        assert ref == (b"", b"mv: 'f' and 'f' are the same file\n", 1)
        for cwd in [ref_cwd, bench_cwd]:
            assert (cwd / "f").read_bytes() == b"payload\n"
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Preserve GNU's byte-exact C-locale quoting of a non-ASCII same path.
def test_non_ascii_same_path_uses_utf8_diagnostic() -> None:
    # upstream: none - Covers byte-exact C-locale UTF-8 quoting for a same-path diagnostic.
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "파일").write_bytes(b"payload\n")

        args = ["파일", "파일"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)

        assert ref == (
            b"",
            b"mv: ''$'\\355\\214\\214\\354\\235\\274' and "
            b"''$'\\355\\214\\214\\354\\235\\274' are the same file\n",
            1,
        )
        for cwd in [ref_cwd, bench_cwd]:
            assert (cwd / "파일").read_bytes() == b"payload\n"
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Preserve GNU's same-inode rejection for distinct hard-link names.
def test_distinct_hardlinks_report_same_file() -> None:
    # upstream: coreutils/tests/mv/force.sh
    # upstream: coreutils/tests/mv/hard-4.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "f").write_bytes(b"payload\n")
            os.link(cwd / "f", cwd / "h")

        ref = run_system_mv(["f", "h"], ref_cwd)
        bench = run_bench_mv(["f", "h"], bench_cwd)

        assert ref == (b"", b"mv: 'f' and 'h' are the same file\n", 1)
        for cwd in [ref_cwd, bench_cwd]:
            f_stat = (cwd / "f").stat()
            h_stat = (cwd / "h").stat()
            assert (cwd / "f").read_bytes() == b"payload\n"
            assert (cwd / "h").read_bytes() == b"payload\n"
            assert f_stat.st_ino == h_stat.st_ino
            assert f_stat.st_nlink == h_stat.st_nlink == 2
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Preserve GNU's backup exception for two hard-link names of one file.
def test_hardlinks_with_simple_backup_move_source() -> None:
    # upstream: coreutils/tests/mv/hard-4.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "f").write_bytes(b"payload\n")
            os.link(cwd / "f", cwd / "h")

        ref = run_system_mv(["--backup=simple", "f", "h"], ref_cwd)
        bench = run_bench_mv(["--backup=simple", "f", "h"], bench_cwd)

        assert ref == (b"", b"", 0)
        for cwd in [ref_cwd, bench_cwd]:
            h_stat = (cwd / "h").stat()
            backup_stat = (cwd / "h~").stat()
            assert not (cwd / "f").exists()
            assert (cwd / "h").read_bytes() == b"payload\n"
            assert (cwd / "h~").read_bytes() == b"payload\n"
            assert h_stat.st_ino == backup_stat.st_ino
            assert h_stat.st_nlink == backup_stat.st_nlink == 2
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Preserve GNU's rejection when a source symlink points at its target operand.
def test_symlink_onto_referent_reports_same_file() -> None:
    # upstream: coreutils/tests/mv/into-self-2.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "f").write_bytes(b"payload\n")
            (cwd / "s").symlink_to("f")

        ref = run_system_mv(["s", "f"], ref_cwd)
        bench = run_bench_mv(["s", "f"], bench_cwd)

        assert ref == (b"", b"mv: 's' and 'f' are the same file\n", 1)
        for cwd in [ref_cwd, bench_cwd]:
            assert (cwd / "f").read_bytes() == b"payload\n"
            assert os.readlink(cwd / "s") == "f"
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Preserve GNU's backup exception when a source symlink points at its target operand.
def test_symlink_onto_referent_with_simple_backup_succeeds() -> None:
    # upstream: coreutils/tests/mv/part-symlink.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "a").write_bytes(b"payload\n")
            (cwd / "s").symlink_to("a")

        args = ["--backup=simple", "s", "a"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)

        assert ref == (b"", b"", 0)
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)
        for cwd in [ref_cwd, bench_cwd]:
            assert sorted(path.name for path in cwd.iterdir()) == ["a", "a~"]
            assert (cwd / "a").is_symlink()
            assert os.readlink(cwd / "a") == "a"
            assert (cwd / "a~").read_bytes() == b"payload\n"


# Preserve GNU's successful replacement of an alternate hard-link with a symlink.
def test_symlink_onto_alternate_hardlink_succeeds() -> None:
    # upstream: none - Covers replacing an alternate hard-link name with a
    # symlink, which the upstream symlink tests do not exercise.
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "f").write_bytes(b"payload\n")
            os.link(cwd / "f", cwd / "h")
            (cwd / "s").symlink_to("f")

        ref = run_system_mv(["s", "h"], ref_cwd)
        bench = run_bench_mv(["s", "h"], bench_cwd)

        assert ref == (b"", b"", 0)
        for cwd in [ref_cwd, bench_cwd]:
            assert not (cwd / "s").exists()
            assert (cwd / "f").read_bytes() == b"payload\n"
            assert os.readlink(cwd / "h") == "f"
            assert (cwd / "f").stat().st_nlink == 1
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Preserve GNU's refusal to overwrite the source while making a simple backup.
def test_backup_name_equal_to_source_is_rejected() -> None:
    # upstream: coreutils/tests/mv/backup-is-src.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "a~").write_bytes(b"source\n")
            (cwd / "a").write_bytes(b"destination\n")

        ref = run_system_mv(["--backup=simple", "a~", "a"], ref_cwd)
        bench = run_bench_mv(["--backup=simple", "a~", "a"], bench_cwd)

        assert ref == (
            b"",
            b"mv: backing up 'a' might destroy source;  'a~' not moved\n",
            1,
        )
        for cwd in [ref_cwd, bench_cwd]:
            assert (cwd / "a~").read_bytes() == b"source\n"
            assert (cwd / "a").read_bytes() == b"destination\n"
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Preserve GNU's backup refusal when the backup name is a source hard link.
def test_simple_backup_hardlink_alias_preserves_source_and_destination() -> None:
    # upstream: none - Extends backup-is-source protection to a differently
    # spelled hard-link alias across directories.
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "x").mkdir()
            (cwd / "y").mkdir()
            (cwd / "x" / "a~").write_bytes(b"source\n")
            os.link(cwd / "x" / "a~", cwd / "y" / "a~")
            (cwd / "y" / "a").write_bytes(b"destination\n")

        args = ["--backup=simple", "x/a~", "y/a"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)

        assert ref == (
            b"",
            b"mv: backing up 'y/a' might destroy source;  'x/a~' not moved\n",
            1,
        )
        source_stat = (ref_cwd / "x" / "a~").stat()
        backup_stat = (ref_cwd / "y" / "a~").stat()
        assert (ref_cwd / "x" / "a~").read_bytes() == b"source\n"
        assert (ref_cwd / "y" / "a~").read_bytes() == b"source\n"
        assert (ref_cwd / "y" / "a").read_bytes() == b"destination\n"
        assert source_stat.st_ino == backup_stat.st_ino
        assert source_stat.st_nlink == backup_stat.st_nlink == 2
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)
        source_stat = (bench_cwd / "x" / "a~").stat()
        backup_stat = (bench_cwd / "y" / "a~").stat()
        assert (bench_cwd / "x" / "a~").read_bytes() == b"source\n"
        assert (bench_cwd / "y" / "a~").read_bytes() == b"source\n"
        assert (bench_cwd / "y" / "a").read_bytes() == b"destination\n"
        assert source_stat.st_ino == backup_stat.st_ino
        assert source_stat.st_nlink == backup_stat.st_nlink == 2


# Preserve GNU's existing-backup refusal when the simple backup would overwrite the source.
def test_existing_backup_simple_collision_preserves_all_entries() -> None:
    # upstream: none - Ensures existing-backup mode still rejects a source-aliased
    # simple candidate when a numbered backup exists.
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "left").mkdir()
            (cwd / "right").mkdir()
            (cwd / "left" / "a~").write_bytes(b"source\n")
            (cwd / "right" / "a").write_bytes(b"destination\n")
            os.link(cwd / "left" / "a~", cwd / "right" / "a~")
            (cwd / "right" / "a.~1~").write_bytes(b"numbered backup\n")

        args = ["--backup=existing", "left/a~", "right/a"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)

        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)
        for cwd in [ref_cwd, bench_cwd]:
            source_stat = (cwd / "left" / "a~").stat()
            backup_stat = (cwd / "right" / "a~").stat()
            target_stat = (cwd / "right" / "a").stat()
            numbered_stat = (cwd / "right" / "a.~1~").stat()
            assert (cwd / "left" / "a~").read_bytes() == b"source\n"
            assert (cwd / "right" / "a").read_bytes() == b"destination\n"
            assert (cwd / "right" / "a~").read_bytes() == b"source\n"
            assert (cwd / "right" / "a.~1~").read_bytes() == b"numbered backup\n"
            assert source_stat.st_ino == backup_stat.st_ino
            assert source_stat.st_nlink == backup_stat.st_nlink == 2
            assert target_stat.st_nlink == numbered_stat.st_nlink == 1


# Preserve GNU's existing-backup move when an aliased simple candidate has a different basename.
def test_existing_backup_alias_with_different_basename_moves_source() -> None:
    # upstream: none - Ensures inode aliasing alone does not reject an
    # existing-backup move when raw basenames differ.
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "a").write_bytes(b"source\n")
            (cwd / "b").write_bytes(b"destination\n")
            os.link(cwd / "a", cwd / "b~")
            (cwd / "b.~1~").write_bytes(b"numbered backup\n")

        args = ["--backup=existing", "a", "b"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)

        assert ref == (b"", b"", 0)
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)
        for cwd in [ref_cwd, bench_cwd]:
            assert sorted(path.name for path in cwd.iterdir()) == [
                "b",
                "b.~1~",
                "b.~2~",
                "b~",
            ]
            b_stat = (cwd / "b").stat()
            backup_stat = (cwd / "b~").stat()
            assert b_stat.st_ino == backup_stat.st_ino
            assert b_stat.st_nlink == backup_stat.st_nlink == 2
            assert (cwd / "b").read_bytes() == b"source\n"
            assert (cwd / "b~").read_bytes() == b"source\n"
            assert (cwd / "b.~1~").read_bytes() == b"numbered backup\n"
            assert (cwd / "b.~2~").read_bytes() == b"destination\n"


# Preserve GNU's raw dirname handling through a symlink before a same-file check.
def test_symlink_parent_component_reports_same_file_without_mutation() -> None:
    # upstream: none - Covers raw dirname identity through a symlink and parent
    # component before the same-file decision.
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            (cwd / "p").mkdir()
            (cwd / "q" / "sub").mkdir(parents=True)
            (cwd / "p" / "link").symlink_to("../q/sub")
            (cwd / "q" / "f").write_bytes(b"payload\n")

        args = ["--backup=simple", "p/link/../f", "q/f"]
        ref = run_system_mv(args, ref_cwd)
        bench = run_bench_mv(args, bench_cwd)

        assert ref == (b"", b"mv: 'p/link/../f' and 'q/f' are the same file\n", 1)
        assert (ref_cwd / "q" / "f").read_bytes() == b"payload\n"
        assert (ref_cwd / "q" / "sub").is_dir()
        assert os.readlink(ref_cwd / "p" / "link") == "../q/sub"
        assert_same_result(ref, bench, ignore_stderr_when_exit_nonzero=False)
        assert (bench_cwd / "q" / "f").read_bytes() == b"payload\n"
        assert (bench_cwd / "q" / "sub").is_dir()
        assert os.readlink(bench_cwd / "p" / "link") == "../q/sub"


def test_deferred_mv_regressions_placeholder() -> None:
    # Not ported yet: these require cross-device moves, ACL/xattr control,
    # interactive prompts, same-file diagnostics, or descriptor-level
    # leak checks that the current parity harness does not expose.
    # upstream: coreutils/tests/cp/cp-mv-backup.sh
    # upstream: coreutils/tests/cp/cp-mv-enotsup-xattr.sh
    # upstream: coreutils/tests/mv/acl.sh
    # upstream: coreutils/tests/mv/atomic.sh
    # upstream: coreutils/tests/mv/atomic2.sh
    # upstream: coreutils/tests/mv/backup-dir.sh
    # upstream: coreutils/tests/mv/backup-is-src.sh
    # upstream: coreutils/tests/mv/childproof.sh
    # upstream: coreutils/tests/mv/dir-file.sh
    # upstream: coreutils/tests/mv/dir2dir.sh
    # upstream: coreutils/tests/mv/dup-source.sh
    # upstream: coreutils/tests/mv/force.sh
    # upstream: coreutils/tests/mv/hard-2.sh
    # upstream: coreutils/tests/mv/hard-3.sh
    # upstream: coreutils/tests/mv/hard-4.sh
    # upstream: coreutils/tests/mv/hardlink-case.sh
    # upstream: coreutils/tests/mv/hard-link-1.sh
    # upstream: coreutils/tests/mv/i-1.pl
    # upstream: coreutils/tests/mv/i-2.sh
    # upstream: coreutils/tests/mv/i-3.sh
    # upstream: coreutils/tests/mv/i-4.sh
    # upstream: coreutils/tests/mv/i-5.sh
    # upstream: coreutils/tests/mv/i-link-no.sh
    # upstream: coreutils/tests/mv/into-self.sh
    # upstream: coreutils/tests/mv/into-self-2.sh
    # upstream: coreutils/tests/mv/into-self-3.sh
    # upstream: coreutils/tests/mv/into-self-4.sh
    # upstream: coreutils/tests/mv/leak-fd.sh
    # upstream: coreutils/tests/mv/mv-exchange.sh
    # upstream: coreutils/tests/mv/mv-special-2.sh
    # upstream: coreutils/tests/mv/no-copy.sh
    # upstream: coreutils/tests/mv/part-fail.sh
    # upstream: coreutils/tests/mv/part-hardlink.sh
    # upstream: coreutils/tests/mv/part-rename.sh
    # upstream: coreutils/tests/mv/part-symlink.sh
    # upstream: coreutils/tests/mv/partition-perm.sh
    # upstream: coreutils/tests/mv/perm-1.sh
    # upstream: coreutils/tests/mv/sticky-to-xpart.sh
    # upstream: coreutils/tests/mv/meta-to-xpart.sh
    # upstream: coreutils/tests/mv/symlink-onto-hardlink.sh
    # upstream: coreutils/tests/mv/symlink-onto-hardlink-to-self.sh
    # upstream: coreutils/tests/mv/to-symlink.sh
    # upstream: coreutils/tests/mv/trailing-slash.sh
    # upstream: coreutils/tests/mv/update.sh
    pytest.skip("requires cross-device, ACL/xattr, or interactive mv fixtures")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", MV_VERIFY_TARGETS, ids=lambda path: path.name)
def test_mv_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
