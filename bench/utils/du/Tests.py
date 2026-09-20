"""Check du apparent-byte parity against GNU coreutils and verify proof surface."""

import fcntl
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

BENCH_DU_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "du_bench.dll")
COREUTILS_DU = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "du")
DU_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "du" / "DuSchema.dfy",
    ROOT / "bench" / "utils" / "du" / "DuCore.dfy",
    ROOT / "bench" / "utils" / "du" / "DuSpec.dfy",
    ROOT / "bench" / "utils" / "du" / "DuProof.dfy",
    ROOT / "bench" / "utils" / "du" / "Du.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_du_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_DU_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "du") > BENCH_DU_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "du")
        if not COREUTILS_DU.exists():
            build_coreutils_utility(ROOT, "du")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_du(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_DU_DLL, args, cwd)


def run_system_du(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_DU, "du", args, cwd)


def normalize_du_stderr(stderr: bytes) -> bytes:
    text = stderr.decode("latin1")
    text = re.sub(
        r"Try '.*du --help' for more information\.\n",
        "Try 'du --help' for more information.\n",
        text,
    )
    return text.encode("latin1")


def assert_du_parity(args: list[str], cwd: Path) -> None:
    ref = run_system_du(args, cwd)
    bench = run_bench_du(args, cwd)
    assert_result_matches_reference(
        ref,
        bench,
        stderr_normalizer=normalize_du_stderr,
        ignore_stderr_when_exit_nonzero=False,
    )


def test_regular_file_bytes_match_coreutils() -> None:
    # upstream: coreutils/tests/du/basic.sh
    # upstream: coreutils/tests/du/apparent.sh
    # upstream: coreutils/tests/du/two-args.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "alpha.txt").write_bytes(b"abcdef\n")

        assert_du_parity(["-b", "alpha.txt"], cwd)


def test_multiple_file_operands_match_coreutils() -> None:
    # upstream: coreutils/tests/du/basic.sh
    # upstream: coreutils/tests/du/apparent.sh
    # upstream: coreutils/tests/du/two-args.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "empty").write_bytes(b"")
        _ = (cwd / "payload").write_bytes(b"payload")

        assert_du_parity(["--bytes", "empty", "payload"], cwd)


def test_apparent_size_block_size_one_matches_coreutils() -> None:
    # upstream: coreutils/tests/du/basic.sh
    # upstream: coreutils/tests/du/apparent.sh
    # upstream: coreutils/tests/du/two-args.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "data.bin").write_bytes(b"\x00\x01\x02\x03")

        assert_du_parity(["--apparent-size", "--block-size=1", "data.bin"], cwd)


def test_summarize_regular_file_matches_coreutils() -> None:
    # upstream: coreutils/tests/du/basic.sh
    # upstream: coreutils/tests/du/apparent.sh
    # upstream: coreutils/tests/du/two-args.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "one").write_bytes(b"12345")

        assert_du_parity(["-b", "-s", "one"], cwd)


def test_missing_file_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/du/basic.sh
    # upstream: coreutils/tests/du/apparent.sh
    # upstream: coreutils/tests/du/two-args.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)

        assert_du_parity(["-b", "missing"], cwd)


def test_invalid_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/invalid-opt.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)

        assert_du_parity(["--bogus"], cwd)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_du(args, cwd)
            bench = run_bench_du(args, cwd)
            assert_requested_message_behavior(ref, bench)


def test_unsupported_default_accounting_reports_benchmark_diagnostic() -> None:
    # upstream: none - Documents this benchmark slice's explicit rejection of default
    # upstream-reason: allocated-block accounting.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "alpha.txt").write_bytes(b"abcdef\n")
        stdout, stderr, exit_code = run_bench_du(["alpha.txt"], cwd)

    assert stdout == b""
    assert stderr == b"du: this benchmark supports apparent byte counts only; use -b or --bytes\n"
    assert exit_code == 1


def test_deferred_du_regressions_inventory() -> None:
    # du/8gb.sh, du/long-from-unreadable.sh, du/no-deref.sh, and du/threshold.sh.
    # Not ported yet: default block accounting, recursive directory traversal,
    # hard-link and inode accounting, symlink dereference policy, mount/device
    # boundaries, huge sparse files, unreadable directories, thresholds, totals,
    # and max-depth require filesystem metadata not carried by this World slice.
    # Not ported yet: --files0-from requires NUL-delimited operand streams and
    # directory-stdin exclusion checks outside this regular-file byte slice.
    # upstream: coreutils/tests/du/basic.sh
    # upstream: coreutils/tests/du/2g.sh
    # upstream: coreutils/tests/du/8gb.sh
    # upstream: coreutils/tests/du/bind-mount-dir-cycle.sh
    # upstream: coreutils/tests/du/files0-from.pl
    # upstream: coreutils/tests/du/files0-from-dir.sh
    # upstream: coreutils/tests/du/hard-link.sh
    # upstream: coreutils/tests/du/inodes.sh
    # upstream: coreutils/tests/du/long-from-unreadable.sh
    # upstream: coreutils/tests/du/max-depth.sh
    # upstream: coreutils/tests/du/no-deref.sh
    # upstream: coreutils/tests/du/one-file-system.sh
    # upstream: coreutils/tests/du/threshold.sh
    pytest.skip("requires deferred du filesystem metadata or operand-source behavior")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", DU_VERIFY_TARGETS, ids=lambda path: path.name)
def test_du_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
