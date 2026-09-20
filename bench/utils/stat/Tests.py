"""Check numeric stat parity against GNU coreutils and verify its Dafny proof surface."""

import fcntl
import os
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
BENCH_STAT_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "stat_bench.dll")
COREUTILS_STAT = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "stat")
COREUTILS_CP = COREUTILS_STAT.with_name("cp")
STAT_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "stat" / "StatSchema.dfy",
    ROOT / "bench" / "utils" / "stat" / "StatCore.dfy",
    ROOT / "bench" / "utils" / "stat" / "StatSpec.dfy",
    ROOT / "bench" / "utils" / "stat" / "StatProof.dfy",
    ROOT / "bench" / "utils" / "stat" / "Stat.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_stat_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_STAT_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "stat") > BENCH_STAT_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "stat")
        if not COREUTILS_STAT.exists():
            build_coreutils_utility(ROOT, "stat")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def parity_env() -> dict[str, str]:
    env = os.environ.copy()
    env["LC_ALL"] = "C"
    env["LANG"] = "C"
    env["TZ"] = "UTC0"
    return env


def assert_stat_parity(args: list[str], cwd: Path) -> None:
    env = parity_env()
    reference = run_coreutils_utility(COREUTILS_STAT, "stat", args, cwd, env=env)
    bench = run_bench_utility(BENCH_STAT_DLL, args, cwd, env=env)
    assert_result_matches_reference(reference, bench)


# Timestamp regression: the whole-second %Y case preserves GNU's epoch-relative result.
def test_mtime_seconds_match_coreutils_nanoseconds_case() -> None:
    # upstream: coreutils/tests/stat/stat-nanoseconds.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        path = cwd / "k"
        path.write_bytes(b"")
        os.utime(path, ns=(67_413_023_456_789, 67_413_023_456_789))

        reference = run_coreutils_utility(
            COREUTILS_STAT,
            "stat",
            ["--format", "%Y", path.name],
            cwd,
            env=parity_env(),
        )
        assert reference == (b"67413\n", b"", 0)
        bench = run_bench_utility(
            BENCH_STAT_DLL,
            ["--format", "%Y", path.name],
            cwd,
            env=parity_env(),
        )
        assert_result_matches_reference(reference, bench)


@pytest.mark.parametrize(
    "args",
    [
        ["--format", "%f", "link1"],
        ["--format", "%f", "link1/"],
        ["--format", "%f", "link2"],
        ["-L", "--format", "%f", "link2"],
        ["--format", "%f", "link2/"],
    ],
)
# Trailing-slash regression: one symlink lookup rule matches GNU for the selected argument form.
def test_symlink_trailing_slash_policy_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/stat/stat-slash.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "file").write_bytes(b"")
        (cwd / "dir").mkdir()
        (cwd / "link1").symlink_to("file")
        (cwd / "link2").symlink_to("dir")

        assert_stat_parity(args, cwd)


# Upstream formatting regression: --format emits one newline for each operand.
def test_format_adds_newline_for_each_operand() -> None:
    # upstream: coreutils/tests/stat/stat-printf.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "first").write_bytes(b"x")
        (cwd / "second").write_bytes(b"y")

        assert_stat_parity(["--format", "%s", "first", "second"], cwd)


# Special-file regression: copied FIFOs retain the same raw kind and permission bits.
def test_copied_fifo_raw_modes_match_coreutils() -> None:
    # upstream: coreutils/tests/cp/preserve-mode.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        os.mkfifo(cwd / "fifo")
        copied = run_coreutils_utility(
            COREUTILS_CP,
            "cp",
            ["-a", "--no-preserve=mode", "fifo", "fifo_copy"],
            cwd,
            env=parity_env(),
        )
        assert copied == (b"", b"", 0)

        args = ["--format", "%f", "fifo", "fifo_copy"]
        reference = run_coreutils_utility(COREUTILS_STAT, "stat", args, cwd, env=parity_env())
        assert reference[0].splitlines()[0] == reference[0].splitlines()[1]
        bench = run_bench_utility(BENCH_STAT_DLL, args, cwd, env=parity_env())
        assert_result_matches_reference(reference, bench)


@pytest.mark.parametrize("args", [["--help"], ["--version"]])
# User-interface regression: one standard informational mode terminates successfully.
def test_help_and_version_exit_successfully(args: list[str]) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        reference = run_coreutils_utility(COREUTILS_STAT, "stat", args, cwd)
        bench = run_bench_utility(BENCH_STAT_DLL, args, cwd)
        assert_requested_message_behavior(reference, bench)


# Proof regression: schema, implementation, specification, proof, and entry point must all verify.
@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", STAT_VERIFY_TARGETS)
def test_stat_dafny_verifies(target: Path) -> None:
    # upstream: none - verifies the repository's Dafny proof surface
    run_dafny_verify(target)
