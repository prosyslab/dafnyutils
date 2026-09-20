"""Check ln symbolic-link parity against GNU coreutils and verify its proof surface."""

import fcntl
import re
import subprocess
import tempfile
from pathlib import Path

import pytest

from tools.bench.bench_test_support import (
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
    ROOT / "bench" / "utils" / "ln" / "LnSchema.dfy",
    ROOT / "bench" / "utils" / "ln" / "LnCore.dfy",
    ROOT / "bench" / "utils" / "ln" / "LnSpec.dfy",
    ROOT / "bench" / "utils" / "ln" / "LnProof.dfy",
    ROOT / "bench" / "utils" / "ln" / "Ln.dfy",
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


def test_symbolic_one_operand_reports_benchmark_diagnostic() -> None:
    # upstream: none - Documents this benchmark slice rejecting GNU one-target implicit link-name
    # upstream-reason: mode.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        stdout, stderr, exit_code = run_bench_ln(["-s", "target.txt"], cwd)
        assert stdout == b""
        assert b"target-directory link modes are outside this benchmark" in stderr
        assert exit_code == 1
        assert not (cwd / "target.txt").exists()


def test_symbolic_multi_operand_reports_benchmark_diagnostic() -> None:
    # upstream: none - Documents this benchmark slice rejecting GNU multi-source target-directory
    # upstream-reason: mode.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "dest").mkdir()
        stdout, stderr, exit_code = run_bench_ln(["-s", "a", "b", "dest"], cwd)
        assert stdout == b""
        assert b"target-directory link modes are outside this benchmark" in stderr
        assert exit_code == 1
        assert not (cwd / "dest" / "a").exists()
        assert not (cwd / "dest" / "b").exists()


def test_symbolic_directory_link_name_reports_benchmark_diagnostic() -> None:
    # upstream: none - Documents this benchmark slice rejecting GNU directory destination link-name
    # upstream-reason: mode.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "dest").mkdir()
        stdout, stderr, exit_code = run_bench_ln(["-s", "target.txt", "dest"], cwd)
        assert stdout == b""
        assert b"target-directory link modes are outside this benchmark" in stderr
        assert exit_code == 1
        assert not (cwd / "dest" / "target.txt").exists()


def test_hard_links_reported_unsupported_without_creating_link() -> None:
    # upstream: none - Documents the benchmark's symbolic-link-only slice rather than GNU hard-link
    # upstream-reason: parity.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "source.txt").write_bytes(b"payload\n")
        stdout, stderr, exit_code = run_bench_ln(["source.txt", "link.txt"], cwd)
        assert stdout == b""
        assert stderr == b"ln: hard links are outside this benchmark; use -s/--symbolic\n"
        assert exit_code == 1
        assert not (cwd / "link.txt").exists()


def test_deferred_ln_upstream_inventory() -> None:
    # Not ported: hard links, one-operand implicit link names, destination-directory
    # mode, symlink-to-directory destination handling, --no-dereference, -f, and backups.
    # Not ported: force replacement, same-file detection, and replacement of
    # dangling or invalid symlink destinations.
    # Not ported: --relative needs canonical path resolution beyond this slice.
    # Not ported: --target-directory and multi-source directory mode.
    # Not ported: backup policy, hard-link conversion, and trailing-slash edge cases
    # rely on GNU behaviors intentionally outside the current symbolic-only model.
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
