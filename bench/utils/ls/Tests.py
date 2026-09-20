"""Check deterministic ls parity against GNU coreutils and verify its Dafny proof surface."""

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
BENCH_LS_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "ls_bench.dll")
COREUTILS_LS = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "ls")
LS_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "ls" / "LsSchema.dfy",
    ROOT / "bench" / "utils" / "ls" / "LsTime.dfy",
    ROOT / "bench" / "utils" / "ls" / "LsCore.dfy",
    ROOT / "bench" / "utils" / "ls" / "LsSpec.dfy",
    ROOT / "bench" / "utils" / "ls" / "LsProof.dfy",
    ROOT / "bench" / "utils" / "ls" / "Ls.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_ls_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_LS_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "ls") > BENCH_LS_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "ls")
        if not COREUTILS_LS.exists():
            build_coreutils_utility(ROOT, "ls")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def parity_env() -> dict[str, str]:
    env = os.environ.copy()
    env["LC_ALL"] = "C"
    env["LANG"] = "C"
    env["TZ"] = "UTC0"
    env["TERM"] = "dumb"
    env["QUOTING_STYLE"] = "literal"
    return env


def assert_ls_parity(args: list[str], cwd: Path, env: dict[str, str] | None = None) -> None:
    effective_env = env or parity_env()
    reference = run_coreutils_utility(COREUTILS_LS, "ls", args, cwd, env=effective_env)
    bench = run_bench_utility(BENCH_LS_DLL, args, cwd, env=effective_env)
    assert_result_matches_reference(reference, bench)


# Name-order regression: nonterminal output is one entry per line in C byte order.
def test_default_listing_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/no-arg.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "zeta").write_bytes(b"")
        (cwd / "Alpha").write_bytes(b"")
        (cwd / "middle").mkdir()
        (cwd / ".hidden").write_bytes(b"")

        assert_ls_parity([], cwd)


# Hidden-entry regression: -a includes hidden names and synthesizes both dot entries.
def test_all_entries_mode_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/a-option.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / ".hidden").write_bytes(b"x")
        (cwd / "visible").write_bytes(b"y")

        assert_ls_parity(["-a"], cwd)


# Symlink traversal regression: sorting synthetic .. must use the followed directory's parent.
def test_all_time_sort_through_directory_symlink_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/symlink-slash.sh
    # upstream: coreutils/tests/ls/ls-time.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "actual" / "child").mkdir(parents=True)
        (cwd / "alias").symlink_to("actual/child")
        os.utime(cwd / "actual", ns=(1_600_000_000_000_000_000,) * 2)
        os.utime(cwd / "actual" / "child", ns=(1_650_000_000_000_000_000,) * 2)
        os.utime(cwd, ns=(1_700_000_000_000_000_000,) * 2)

        assert_ls_parity(["--all", "-t", "-L", "alias"], cwd)


# Size-sort traversal regression: synthetic dot must describe the followed directory target.
def test_all_size_sort_through_directory_symlink_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/a-option.sh
    # upstream: coreutils/tests/ls/symlink-slash.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "d").mkdir()
        (cwd / "d" / "payload").write_bytes(b"xx")
        (cwd / "link").symlink_to("d")

        assert_ls_parity(["--all", "-S", "link"], cwd)


# Hidden-entry regression: -A includes hidden names but excludes both dot entries.
def test_almost_all_entries_mode_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/a-option.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / ".hidden").write_bytes(b"x")
        (cwd / "visible").write_bytes(b"y")

        assert_ls_parity(["-A"], cwd)


# Numeric-long regression: all columns must share one status record.
def test_numeric_long_listing_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/nameless-uid.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        path = cwd / "payload"
        path.write_bytes(b"payload\n")
        path.chmod(0o640)
        os.utime(path, ns=(1_600_000_000_000_000_000, 1_600_000_000_000_000_000))
        (cwd / "link").symlink_to("payload")

        assert_ls_parity(["-n", "--time-style=+%s"], cwd)


# Long-ISO regression: UTC numeric-long output must render a fixed minute-precision timestamp.
def test_numeric_long_iso_time_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/ls-time.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        path = cwd / "payload"
        path.write_bytes(b"payload\n")
        os.utime(path, ns=(1_600_000_000_000_000_000, 1_600_000_000_000_000_000))

        assert_ls_parity(["-n", "--time-style=long-iso", "payload"], cwd)


# Change-time regression: numeric-long direct output must select ctime rather than mtime.
def test_numeric_long_change_time_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/ls-time.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        path = cwd / "payload"
        path.write_bytes(b"payload\n")
        os.utime(path, ns=(1_600_000_000_000_000_000, 1_600_000_000_000_000_000))

        assert_ls_parity(["-n", "-d", "--time=status", "--time-style=+%s", "payload"], cwd)


# Full-time ctime regression: the nanosecond field must come from the change timestamp.
def test_numeric_long_full_iso_change_time_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/ls-time.sh
    # Case: (--full-time ctime observation)
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        path = cwd / "payload"
        path.write_bytes(b"payload\n")
        path.chmod(0o640)

        assert_ls_parity(
            [
                "-n",
                "-d",
                "--time=status",
                "--time-style=full-iso",
                "payload",
            ],
            cwd,
        )


# Time-style diagnostic regression: invalid styles in numeric-long mode fail before listing.
def test_invalid_numeric_long_time_style_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/time-style-diag.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)

        assert_ls_parity(["-n", "--time-style=XX"], cwd)


# Short-output regression: an invalid long-format time style is ignored without numeric-long mode.
def test_short_output_ignores_invalid_time_style_like_coreutils() -> None:
    # upstream: none - GNU parity for the benchmark's short-output parsing rule
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "payload").write_bytes(b"")

        assert_ls_parity(["--time-style=XX", "payload"], cwd)


# Size-order regression: -S orders larger files before smaller files.
def test_size_sorting_matches_coreutils() -> None:
    # upstream: none - GNU parity for the benchmark's supported -S mode
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "small").write_bytes(b"1")
        (cwd / "large").write_bytes(b"123456")
        (cwd / "middle").write_bytes(b"123")

        assert_ls_parity(["-S"], cwd)


# Reverse-time regression: -tr orders older timestamps before newer timestamps.
def test_reverse_time_sorting_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/ls-time.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "small").write_bytes(b"1")
        (cwd / "large").write_bytes(b"123456")
        (cwd / "middle").write_bytes(b"123")
        os.utime(cwd / "small", ns=(1_500_000_000_000_000_000, 1_500_000_000_000_000_000))
        os.utime(cwd / "large", ns=(1_600_000_000_000_000_000, 1_600_000_000_000_000_000))
        os.utime(cwd / "middle", ns=(1_550_000_000_000_000_000, 1_550_000_000_000_000_000))

        assert_ls_parity(["-tr"], cwd)


# Block regression: 512-byte storage units are rounded in the display unit.
def test_block_size_display_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/block-size.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "payload").write_bytes(b"x" * 5000)
        env = parity_env()
        env["LS_BLOCK_SIZE"] = "1024"

        assert_ls_parity(["-s"], cwd, env)


# Long-size regression: GNU-supported block settings scale numeric-long file sizes selectively.
@pytest.mark.parametrize(
    ("arguments", "environment_key"),
    [
        (["--block-size=512"], None),
        ([], "LS_BLOCK_SIZE"),
        ([], "BLOCK_SIZE"),
        ([], "BLOCKSIZE"),
    ],
    ids=("cli", "ls-block-size", "block-size", "legacy-blocksize"),
)
def test_numeric_long_file_size_units_match_coreutils(
    arguments: list[str], environment_key: str | None
) -> None:
    # upstream: coreutils/tests/ls/block-size.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "payload").write_bytes(b"x" * 1024)
        env = parity_env()
        for key in ("LS_BLOCK_SIZE", "BLOCK_SIZE", "BLOCKSIZE"):
            env.pop(key, None)
        if environment_key is not None:
            env[environment_key] = "512"

        assert_ls_parity(["-n", "--time-style=+%s", *arguments, "payload"], cwd, env)


# Traversal regression: physical recursion must not follow symlinks.
def test_recursive_physical_listing_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/recursive.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "tree" / "child").mkdir(parents=True)
        (cwd / "tree" / "child" / "leaf").write_bytes(b"leaf")
        (cwd / "tree" / "alias").symlink_to("child")

        assert_ls_parity(["-R", "tree"], cwd)


# Section regression: a repeated empty directory gets one headed section per operand.
def test_repeated_empty_directory_sections_match_coreutils() -> None:
    # upstream: coreutils/tests/ls/ls-misc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "d").mkdir()

        assert_ls_parity(["d", "d"], cwd)


# Error-section regression: a failed operand still makes the successful directory need a heading.
def test_missing_operand_and_empty_directory_match_coreutils() -> None:
    # upstream: coreutils/tests/ls/ls-misc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "d").mkdir()

        assert_ls_parity(["no-dir", "d"], cwd)


# Dangling-link regression: default operand handling must list the link itself successfully.
def test_default_dangling_symlink_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/dangle.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "dangle").symlink_to("no-such-file")

        assert_ls_parity(["dangle"], cwd)


# Dereference regression: a name-only directory scan keeps an implicit dangling link printable.
def test_dereference_implicit_dangling_symlink_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/dangle.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "d").mkdir()
        (cwd / "d" / "dangle").symlink_to("no-such")

        assert_ls_parity(["--dereference", "d"], cwd)


# Dereference error regression: a direct dangling operand still fails as a serious error.
def test_dereference_direct_dangling_symlink_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/dangle.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "dangle").symlink_to("no-such")

        assert_ls_parity(["--dereference", "dangle"], cwd)


# Recursive-section regression: root and child directory groups have one blank line between them.
def test_multiple_recursive_directory_sections_match_coreutils() -> None:
    # upstream: coreutils/tests/ls/recursive.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for path in ("a/1", "a/2", "a/3", "b", "c"):
            (cwd / path).mkdir(parents=True)
        (cwd / "a" / "1" / "I").write_bytes(b"")
        (cwd / "a" / "1" / "II").write_bytes(b"")

        assert_ls_parity(["-R", "a", "b", "c"], cwd)


# Operand-order regression: recursive output puts the file group before directory sections.
def test_recursive_file_group_precedes_directory_sections() -> None:
    # upstream: coreutils/tests/ls/recursive.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "x").mkdir()
        (cwd / "y").mkdir()
        (cwd / "f").write_bytes(b"")

        assert_ls_parity(["-R", "x", "y", "f"], cwd)


# Cycle regression: following all directory links must terminate and report the ancestor cycle.
def test_recursive_logical_cycle_terminates_with_failure() -> None:
    # upstream: coreutils/tests/ls/infloop.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "tree" / "child").mkdir(parents=True)
        (cwd / "tree" / "child" / "back").symlink_to("..")

        reference = run_coreutils_utility(COREUTILS_LS, "ls", ["-RL", "tree"], cwd)
        bench = run_bench_utility(BENCH_LS_DLL, ["-RL", "tree"], cwd)
        assert_result_matches_reference(reference, bench)


# User-interface regression: --help terminates successfully after printing usage information.
def test_help_exits_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        reference = run_coreutils_utility(COREUTILS_LS, "ls", ["--help"], cwd)
        bench = run_bench_utility(BENCH_LS_DLL, ["--help"], cwd)
        assert_requested_message_behavior(reference, bench)


# User-interface regression: --version terminates successfully after printing version information.
def test_version_exits_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        reference = run_coreutils_utility(COREUTILS_LS, "ls", ["--version"], cwd)
        bench = run_bench_utility(BENCH_LS_DLL, ["--version"], cwd)
        assert_requested_message_behavior(reference, bench)


# Proof regression: schema, implementation, specification, proof, and entry point must all verify.
@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", LS_VERIFY_TARGETS)
def test_ls_dafny_verifies(target: Path) -> None:
    # upstream: none - verifies the repository's Dafny proof surface
    run_dafny_verify(target)
