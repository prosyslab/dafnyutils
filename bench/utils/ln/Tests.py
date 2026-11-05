"""Check ln symbolic-link parity against GNU coreutils and verify its proof surface."""

import fcntl
import re
import subprocess
import tempfile
from pathlib import Path

import pytest

from benchmark_tools.test_support import (
    BENCH_COMMAND_TIMEOUT_SEC,
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

BENCH_LN_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "ln_bench.dll")
COREUTILS_LN = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "ln")
LN_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "ln" / "Spec/LnSchema.dfy",
    ROOT / "bench" / "utils" / "ln" / "Impl/LnCore.dfy",
    ROOT / "bench" / "utils" / "ln" / "Spec/LnSpec.dfy",
    ROOT / "bench" / "utils" / "ln" / "Proof/LnProof.dfy",
    ROOT / "bench" / "utils" / "ln" / "Impl/Ln.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_ln_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_LN_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "ln") > BENCH_LN_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "ln")
        if not COREUTILS_LN.exists():
            build_coreutils_utility(ROOT, "ln")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_ln(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_LN_DLL, args, cwd)


def run_system_ln(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_LN, "ln", args, cwd)


def normalize_stderr(stderr: bytes) -> bytes:
    text = stderr.decode("latin1")
    text = re.sub(
        r"Try '.*ln --help' for more information\.\n",
        "Try 'ln --help' for more information.\n",
        text,
    )
    return text.encode("latin1")


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    assert_result_matches_reference(
        ref_result,
        bench_result,
        stderr_normalizer=normalize_stderr,
        ignore_stderr_when_exit_nonzero=False,
    )


def readlink_target(path: Path) -> bytes:
    completed = subprocess.run(
        ["readlink", path.name],
        cwd=path.parent,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    assert completed.returncode == 0, completed.stderr.decode("latin1")
    return completed.stdout.rstrip(b"\n")


# A single symbolic-link operand creates its basename in the current directory.
def test_one_operand_symbolic_link_matches_coreutils() -> None:
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in (ref_cwd, bench_cwd):
            (cwd / "nested").mkdir()
        args = ["-s", "nested/a.sym"]
        assert_same_result(run_system_ln(args, ref_cwd), run_bench_ln(args, bench_cwd))
        assert readlink_target(ref_cwd / "a.sym") == b"nested/a.sym"
        assert readlink_target(bench_cwd / "a.sym") == b"nested/a.sym"


# Empty source and destination operands retain GNU's exact diagnostics and link effects.
@pytest.mark.parametrize(
    "args",
    [
        pytest.param(["-s", "", "link"], id="symbolic-direct-empty-source"),
        pytest.param(["-s", ""], id="symbolic-one-empty-source"),
        pytest.param(["-s", "", ""], id="symbolic-both-empty"),
        pytest.param(["-s", "target", ""], id="symbolic-empty-destination"),
        pytest.param(["-s", "", "dest"], id="symbolic-empty-source-directory"),
        pytest.param(["-s", "", "other", "dest"], id="symbolic-batch-empty-first"),
        pytest.param(["-s", "other", "", "dest"], id="symbolic-batch-empty-last"),
        pytest.param(["", "link"], id="hard-link-empty-source"),
        pytest.param(["", ""], id="hard-link-both-empty"),
    ],
)
def test_empty_argument_matrix_matches_coreutils(args: list[str]) -> None:
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in (ref_cwd, bench_cwd):
            (cwd / "dest").mkdir()
        assert_same_result(run_system_ln(args, ref_cwd), run_bench_ln(args, bench_cwd))
        ref_links = sorted(
            (str(path.relative_to(ref_cwd)), str(path.readlink()))
            for path in ref_cwd.rglob("*")
            if path.is_symlink()
        )
        bench_links = sorted(
            (str(path.relative_to(bench_cwd)), str(path.readlink()))
            for path in bench_cwd.rglob("*")
            if path.is_symlink()
        )
        assert bench_links == ref_links


# A missing source reports GNU's access diagnostic for implicit hard links.
def test_one_operand_missing_hard_link_source_matches_coreutils() -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_same_result(
            run_system_ln(["nested/missing"], cwd),
            run_bench_ln(["nested/missing"], cwd),
        )


# A hard link shares its source inode and content after the command succeeds.
def test_hard_link_identity_matches_coreutils() -> None:
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in (ref_cwd, bench_cwd):
            (cwd / "source").write_bytes(b"payload\n")
        assert_same_result(
            run_system_ln(["source", "linked"], ref_cwd),
            run_bench_ln(["source", "linked"], bench_cwd),
        )
        for cwd in (ref_cwd, bench_cwd):
            assert (cwd / "linked").read_bytes() == b"payload\n"
            assert (cwd / "source").stat().st_ino == (cwd / "linked").stat().st_ino


# A directory destination resolves the final link name from the source basename.
def test_hard_link_into_directory_matches_coreutils() -> None:
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in (ref_cwd, bench_cwd):
            (cwd / "source").write_bytes(b"source contents")
            (cwd / "destination").mkdir()
        assert_same_result(
            run_system_ln(["source", "destination"], ref_cwd),
            run_bench_ln(["source", "destination"], bench_cwd),
        )
        for cwd in (ref_cwd, bench_cwd):
            assert (cwd / "source").stat().st_ino == (cwd / "destination/source").stat().st_ino


def test_creates_symbolic_link_to_existing_source_matches_coreutils() -> None:
    # upstream: coreutils/tests/ln/misc.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            _ = (cwd / "target.txt").write_bytes(b"payload\n")

        args = ["-s", "target.txt", "link.txt"]
        ref = run_system_ln(args, ref_cwd)
        bench = run_bench_ln(args, bench_cwd)
        assert_same_result(ref, bench)
        assert readlink_target(ref_cwd / "link.txt") == b"target.txt"
        assert readlink_target(bench_cwd / "link.txt") == b"target.txt"


def test_symbolic_long_option_allows_dangling_target_matches_coreutils() -> None:
    # upstream: coreutils/tests/ln/misc.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)

        args = ["--symbolic", "missing-target", "dangling"]
        ref = run_system_ln(args, ref_cwd)
        bench = run_bench_ln(args, bench_cwd)
        assert_same_result(ref, bench)
        assert readlink_target(ref_cwd / "dangling") == b"missing-target"
        assert readlink_target(bench_cwd / "dangling") == b"missing-target"


def test_existing_destination_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/ln/misc.sh
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in [ref_cwd, bench_cwd]:
            _ = (cwd / "link.txt").write_bytes(b"existing\n")

        args = ["-s", "target.txt", "link.txt"]
        ref = run_system_ln(args, ref_cwd)
        bench = run_bench_ln(args, bench_cwd)
        assert_same_result(ref, bench)
        assert not (ref_cwd / "link.txt").is_symlink()
        assert not (bench_cwd / "link.txt").is_symlink()
        assert (ref_cwd / "link.txt").read_bytes() == b"existing\n"
        assert (bench_cwd / "link.txt").read_bytes() == b"existing\n"


# A failed symbolic link reports the destination using GNU's shell quoting.
@pytest.mark.parametrize("name", ["semi;colon", "apost'rophe", "tab\tname", "é"])
def test_symbolic_link_error_shell_quoting_matches_coreutils(name: str) -> None:
    # upstream: coreutils/tests/ln/misc.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-s", "target", f"missing/{name}"]
        assert_same_result(run_system_ln(args, cwd), run_bench_ln(args, cwd))


@pytest.mark.parametrize("args", [[], ["-s"]])
def test_missing_operand_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/ln/misc.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_ln(args, cwd)
        bench = run_bench_ln(args, cwd)
        assert_same_result(ref, bench)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_ln(args, cwd)
            bench = run_bench_ln(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize("args", [["--bogus"], ["-Q"]])
def test_parse_errors_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_ln(args, cwd)
        bench = run_bench_ln(args, cwd)
        assert_same_result(ref, bench)


# Multiple symbolic sources create links through a symlink to a destination directory.
def test_symbolic_multi_source_symlink_directory_matches_coreutils() -> None:
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in (ref_cwd, bench_cwd):
            (cwd / "dest").mkdir()
            (cwd / "dest-alias").symlink_to("dest", target_is_directory=True)
        args = ["-s", "a", "b", "dest-alias"]
        assert_same_result(run_system_ln(args, ref_cwd), run_bench_ln(args, bench_cwd))
        for cwd in (ref_cwd, bench_cwd):
            assert readlink_target(cwd / "dest" / "a") == b"a"
            assert readlink_target(cwd / "dest" / "b") == b"b"


# A failed hard-link source does not prevent later sources from being linked.
def test_hard_link_multi_source_continues_after_failure_matches_coreutils() -> None:
    with tempfile.TemporaryDirectory() as ref_tmp, tempfile.TemporaryDirectory() as bench_tmp:
        ref_cwd = Path(ref_tmp)
        bench_cwd = Path(bench_tmp)
        for cwd in (ref_cwd, bench_cwd):
            (cwd / "present").write_bytes(b"contents")
            (cwd / "dest").mkdir()
        args = ["missing", "present", "dest"]
        assert_same_result(run_system_ln(args, ref_cwd), run_bench_ln(args, bench_cwd))
        for cwd in (ref_cwd, bench_cwd):
            assert (cwd / "present").stat().st_ino == (cwd / "dest/present").stat().st_ino
            assert not (cwd / "dest/missing").exists()


# A non-directory final operand reports GNU's target diagnostic before linking.
def test_multi_source_target_must_be_directory_matches_coreutils() -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "target").write_bytes(b"not a directory")
        args = ["-s", "a", "b", "target"]
        assert_same_result(run_system_ln(args, cwd), run_bench_ln(args, cwd))


def test_deferred_ln_upstream_inventory() -> None:
    # Not ported: --no-dereference, -f, and backups.
    # Not ported: force replacement, same-file detection, and replacement of
    # dangling or invalid symlink destinations.
    # Not ported: --relative needs canonical path resolution beyond this slice.
    # Not ported: explicit --target-directory option.
    # Not ported: backup policy and trailing-slash edge cases.
    # upstream: coreutils/tests/ln/misc.sh
    # upstream: coreutils/tests/ln/sf-1.sh
    # upstream: coreutils/tests/ln/relative.sh
    # upstream: coreutils/tests/ln/target-1.sh
    # upstream: coreutils/tests/ln/backup-1.sh
    # upstream: coreutils/tests/ln/hard-backup.sh
    # upstream: coreutils/tests/ln/hard-to-sym.sh
    # upstream: coreutils/tests/ln/slash-decorated-nonexistent-dest.sh
    pytest.skip("unsupported GNU ln modes are inventoried for this small benchmark slice")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", LN_VERIFY_TARGETS, ids=lambda path: path.name)
def test_ln_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
