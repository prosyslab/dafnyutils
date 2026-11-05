"""Check deterministic ls parity against GNU coreutils and verify its Dafny proof surface."""

import fcntl
import os
import socket
import tempfile
from pathlib import Path

import pytest

from tools.test_support import (
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
    ROOT / "bench" / "utils" / "ls" / "Spec/LsSchema.dfy",
    ROOT / "bench" / "utils" / "ls" / "Spec/LsTime.dfy",
    ROOT / "bench" / "utils" / "ls" / "Spec/LsNativeSpec.dfy",
    ROOT / "bench" / "utils" / "ls" / "Impl/LsNativeCore.dfy",
    ROOT / "bench" / "utils" / "ls" / "Proof/LsNativeProof.dfy",
    ROOT / "bench" / "utils" / "ls" / "Proof/LsNativeResourceProof.dfy",
    ROOT / "bench" / "utils" / "ls" / "Spec/LsNativeObservationSpec.dfy",
    ROOT / "bench" / "utils" / "ls" / "Impl/LsNativeObservationCore.dfy",
    ROOT / "bench" / "utils" / "ls" / "Proof/LsNativeObservationProof.dfy",
    ROOT / "bench" / "utils" / "ls" / "Spec/LsNativeDirectorySpec.dfy",
    ROOT / "bench" / "utils" / "ls" / "Proof/LsNativeDirectoryProof.dfy",
    ROOT / "bench" / "utils" / "ls" / "Proof/LsDirectoryTraceProof.dfy",
    ROOT / "bench" / "utils" / "ls" / "Proof/LsDirectoryPieceProof.dfy",
    ROOT / "bench" / "utils" / "ls" / "Proof/LsRunNativeProof.dfy",
    ROOT / "bench" / "utils" / "ls" / "Impl/LsCore.dfy",
    ROOT / "bench" / "utils" / "ls" / "Spec/LsSpec.dfy",
    ROOT / "bench" / "utils" / "ls" / "Proof/LsProof.dfy",
    ROOT / "bench" / "utils" / "ls" / "Impl/Ls.dfy",
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


def assert_ls_parity(
    args: list[str],
    cwd: Path,
    env: dict[str, str] | None = None,
    *,
    strict_stderr: bool = False,
) -> None:
    effective_env = env or parity_env()
    reference = run_coreutils_utility(COREUTILS_LS, "ls", args, cwd, env=effective_env)
    bench = run_bench_utility(BENCH_LS_DLL, args, cwd, env=effective_env)
    assert_result_matches_reference(
        reference, bench, ignore_stderr_when_exit_nonzero=not strict_stderr
    )


# Search permission permits status lookup while absent read permission makes opendir fail.
@pytest.mark.parametrize("args", [[], ["-R"]])
def test_searchable_unreadable_directory_exact_gnu_bytes(args: list[str], tmp_path: Path) -> None:
    # upstream: coreutils/tests/ls/ls-misc.pl - directory access diagnostics.
    if os.geteuid() == 0:
        pytest.skip("permission-denied fixture requires an unprivileged user")
    directory = tmp_path / "search-only"
    directory.mkdir()
    (directory / "entry").write_bytes(b"x")
    directory.chmod(0o111)
    try:
        reference = run_coreutils_utility(
            COREUTILS_LS, "ls", [*args, "search-only"], tmp_path, env=parity_env()
        )
        candidate = run_bench_utility(
            BENCH_LS_DLL, [*args, "search-only"], tmp_path, env=parity_env()
        )
        assert reference == (
            b"",
            b"ls: cannot open directory 'search-only': Permission denied\n",
            2,
        )
        assert_result_matches_reference(reference, candidate, ignore_stderr_when_exit_nonzero=False)
    finally:
        directory.chmod(0o700)


# File access diagnostics always shell quote path bytes, including control and UTF-8.
@pytest.mark.parametrize("name", ["semi;colon", "apost'rophe", "tab\tname", "é"])
def test_access_error_shell_quoting_matches_coreutils(name: str) -> None:
    # upstream: coreutils/tests/ls/ls-misc.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_ls_parity([f"missing/{name}"], Path(tmp_dir), strict_stderr=True)


# Invalid time values use locale quote, unlike raw block-size diagnostics.
@pytest.mark.parametrize("args", [["--time=bad'time"], ["-n", "--time-style=bad\tstyle"]])
def test_invalid_time_locale_quoting_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/ls/time-style-diag.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_ls_parity(args, Path(tmp_dir), strict_stderr=True)


# Block-size errors preserve raw operand text while encoding its UTF-8 bytes.
@pytest.mark.parametrize("value", ["é", "bad\tvalue", "bad'apostrophe"])
def test_invalid_block_size_raw_utf8_matches_coreutils(value: str) -> None:
    # upstream: coreutils/tests/ls/ls-block-size.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        assert_ls_parity([f"--block-size={value}"], Path(tmp_dir), strict_stderr=True)


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


# Implicit directory probing must preserve GNU output for missing and existing operand kinds.
@pytest.mark.parametrize(
    "operand", ["file--end", "regular", "link-file", "directory", "link-directory"]
)
def test_implicit_directory_operand_probe_matches_coreutils(operand: str) -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "regular").write_bytes(b"x")
        (cwd / "directory").mkdir()
        (cwd / "directory" / "child").write_bytes(b"y")
        (cwd / "link-file").symlink_to("regular")
        (cwd / "link-directory").symlink_to("directory")

        assert_ls_parity([operand], cwd, strict_stderr=True)


# Explicit directory/long/follow modes keep their existing one-request behavior.
@pytest.mark.parametrize("options", [["-d"], ["-n"], ["-L"], ["-H"]])
def test_explicit_operand_status_modes_match_coreutils(options: list[str]) -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "regular").write_bytes(b"x")
        (cwd / "link-file").symlink_to("regular")

        assert_ls_parity([*options, "link-file"], cwd, strict_stderr=True)


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


# Cycle diagnostics conditionally quote the recursive path when it contains a semicolon.
def test_recursive_cycle_shell_quoting_matches_coreutils() -> None:
    # upstream: coreutils/tests/ls/infloop.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "tree;name" / "child").mkdir(parents=True)
        (cwd / "tree;name" / "child" / "back").symlink_to("..")
        assert_ls_parity(["-RL", "tree;name"], cwd, strict_stderr=True)


# Recursive directory section headers retain literal names and UTF-8 output bytes.
@pytest.mark.parametrize("name", ["é-dir", "tab\tname", "apost'rophe"])
def test_recursive_directory_header_utf8_matches_coreutils(name: str) -> None:
    # upstream: coreutils/tests/ls/recursive.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / name).mkdir()
        (cwd / name / "child").write_bytes(b"data")
        assert_ls_parity(["-R", name], cwd)


# Multiple directory operands use the same raw UTF-8 section header encoding.
def test_multiple_directory_headers_utf8_match_coreutils() -> None:
    # upstream: coreutils/tests/ls/recursive.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "é-dir").mkdir()
        (cwd / "plain").mkdir()
        (cwd / "é-dir" / "child").write_bytes(b"data")
        assert_ls_parity(["é-dir", "plain"], cwd)


# User-interface regression: --help terminates successfully after printing usage information.
def test_help_exits_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        reference = run_coreutils_utility(COREUTILS_LS, "ls", ["--help"], cwd)
        bench = run_bench_utility(BENCH_LS_DLL, ["--help"], cwd)
        assert_result_matches_reference(reference, bench)


# User-interface regression: --version terminates successfully after printing version information.
def test_version_exits_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        reference = run_coreutils_utility(COREUTILS_LS, "ls", ["--version"], cwd)
        bench = run_bench_utility(BENCH_LS_DLL, ["--version"], cwd)
        assert_result_matches_reference(reference, bench)


# Proof regression: schema, implementation, specification, proof, and entry point must all verify.
@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", LS_VERIFY_TARGETS)
def test_ls_dafny_verifies(target: Path) -> None:
    # upstream: none - verifies the repository's Dafny proof surface
    run_dafny_verify(target)


# Grouped rows preserve GNU padding across sizes, links, blocks and section boundaries.
@pytest.mark.parametrize("options", [["-n"], ["-ns"], ["-s"]])
@pytest.mark.parametrize(
    "population", ["directory", "direct", "mixed", "recursive", "single", "empty"]
)
def test_grouped_columns_exact_gnu_bytes(
    options: list[str], population: str, tmp_path: Path
) -> None:
    directory = tmp_path / "listing"
    directory.mkdir()
    (directory / "zero").write_bytes(b"")
    (directory / "allocated").write_bytes(b"x" * 65536)
    with (directory / "sparse").open("wb") as stream:
        stream.truncate(10_000_000_000)
    for index in range(11):
        os.link(directory / "zero", directory / f"hard-{index:02}")
    (directory / "link").symlink_to("zero")
    child = directory / "child"
    child.mkdir()
    (child / "tiny").write_bytes(b"x")
    (tmp_path / "outside").write_bytes(b"small")
    (tmp_path / "empty").mkdir()
    operands = {
        "directory": ["listing"],
        "direct": ["listing/zero", "listing/allocated", "listing/sparse", "listing/link"],
        "mixed": ["listing/zero", "outside", "listing", "empty"],
        "recursive": ["listing"],
        "single": ["listing/zero"],
        "empty": ["empty"],
    }[population]
    args = options + (["-R"] if population == "recursive" else []) + operands
    env = parity_env()
    reference = run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
    candidate = run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env)
    assert candidate == reference


# A failed expanded entry preserves its row, diagnostic path and minor exit status.
@pytest.mark.parametrize(
    "options",
    [
        ["-nL"],
        ["-nsL"],
        ["-sL"],
        ["-L"],
        ["-SL"],
        ["-tL"],
        ["-nLr"],
        ["-nSL"],
        ["-ntL"],
        ["-nH"],
        ["-n"],
        ["-nL", "--time-style=full-iso"],
        ["-nL", "--time-style=long-iso"],
        ["-nL", "--time-style=iso"],
        ["-nL", "--time-style=+%s"],
    ],
)
@pytest.mark.parametrize("failure", ["missing", "loop"])
def test_failed_directory_entry_exact_gnu_bytes(
    options: list[str], failure: str, tmp_path: Path
) -> None:
    directory = tmp_path / "d"
    directory.mkdir()
    (directory / "bad").symlink_to("absent" if failure == "missing" else "bad")
    (directory / "aaa").write_bytes(b"x")
    (directory / "zzz").write_bytes(b"x" * 65536)
    args = options + ["d"]
    env = parity_env()
    assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
        run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
    )


# Direct failure remains serious while directory and recursive failures retain their paths.
@pytest.mark.parametrize(
    "args",
    [
        ["-nL", "d/bad"],
        ["-nH", "d/bad"],
        ["-nL", "d/bad", "d"],
        ["-nL", "absent", "d"],
        ["-nRL", "d"],
        ["-RL", "d"],
        ["-nL", "d", "other"],
        ["-nL", "d/"],
        ["-nL", "./d"],
    ],
)
def test_failed_operand_context_exact_gnu_bytes(args: list[str], tmp_path: Path) -> None:
    directory = tmp_path / "d"
    directory.mkdir()
    (directory / "bad").symlink_to("absent")
    (directory / "child").mkdir()
    (directory / "child" / "bad").symlink_to("absent")
    (tmp_path / "other").mkdir()
    env = parity_env()
    assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
        run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
    )


# Multiple access errors retain directory-read order independently from reversed output.
def test_failed_entry_diagnostic_order_exact_gnu_bytes(tmp_path: Path) -> None:
    directory = tmp_path / "d"
    directory.mkdir()
    for name in ["zzz", "aaa", "middle"]:
        (directory / name).symlink_to("absent")
    args = ["-nLr", "d"]
    env = parity_env()
    assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
        run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
    )


# The all-failed listing still prints GNU's exact placeholder columns and total.
def test_all_failed_directory_entry_exact_gnu_bytes(tmp_path: Path) -> None:
    (tmp_path / "d").mkdir()
    (tmp_path / "d" / "bad").symlink_to("absent")
    args = ["-nL", "d"]
    env = parity_env()
    assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
        run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
    )


# An implicit cwd failure uses the entry name without a synthetic directory prefix.
def test_implicit_directory_failure_exact_gnu_bytes(tmp_path: Path) -> None:
    (tmp_path / "bad").symlink_to("absent")
    args = ["-nL"]
    env = parity_env()
    assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
        run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
    )


# Unsearchable link targets keep directory failures minor and direct failures serious.
@pytest.mark.parametrize("operands", [["d"], ["d/bad"], ["d/bad", "d"]])
def test_unfollowable_entry_permission_exact_gnu_bytes(operands: list[str], tmp_path: Path) -> None:
    if os.geteuid() == 0:
        pytest.skip("permission-denied fixture requires an unprivileged user")
    (tmp_path / "d").mkdir()
    blocked = tmp_path / "blocked"
    blocked.mkdir()
    (blocked / "target").write_bytes(b"x")
    (tmp_path / "d" / "bad").symlink_to("../blocked/target")
    blocked.chmod(0)
    try:
        args = ["-nL"] + operands
        env = parity_env()
        assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
            run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
        )
    finally:
        blocked.chmod(0o700)


# Name-only options can list an unsearchable directory without child metadata failures.
@pytest.mark.parametrize("options", [[], ["-L"], ["-H"], ["-a"], ["-A"], ["-arL"]])
def test_name_only_unsearchable_directory_exact_gnu_bytes(
    options: list[str], tmp_path: Path
) -> None:
    if os.geteuid() == 0:
        pytest.skip("permission-denied fixture requires an unprivileged user")
    directory = tmp_path / "d"
    directory.mkdir()
    (directory / "plain").write_bytes(b"x")
    (directory / ".hidden").write_bytes(b"x")
    (directory / "link").symlink_to("absent")
    directory.chmod(0o400)
    try:
        args = options + ["d"]
        env = parity_env()
        assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
            run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
        )
    finally:
        directory.chmod(0o700)


# Metadata-demanding options retain failed entry diagnostics even without long output.
@pytest.mark.parametrize(
    "options",
    [
        ["-s"],
        ["-t"],
        ["-S"],
        ["-n"],
        ["-nH"],
        ["-nL"],
        ["-na"],
        ["-nA"],
        ["-sa"],
        ["-sA"],
        ["-ta"],
        ["-tA"],
        ["-Sa"],
        ["-SA"],
    ],
)
def test_metadata_required_unsearchable_directory_exact_gnu_bytes(
    options: list[str], tmp_path: Path
) -> None:
    if os.geteuid() == 0:
        pytest.skip("permission-denied fixture requires an unprivileged user")
    directory = tmp_path / "d"
    directory.mkdir()
    (directory / "plain").write_bytes(b"x")
    (directory / "link").symlink_to("absent")
    directory.chmod(0o400)
    try:
        args = options + ["d"]
        env = parity_env()
        assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
            run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
        )
    finally:
        directory.chmod(0o700)


# Failed special files keep their native directory-entry type in numeric long rows.
@pytest.mark.parametrize("kind", ["fifo", "socket"])
def test_failed_special_entry_exact_gnu_bytes(kind: str, tmp_path: Path) -> None:
    if os.geteuid() == 0:
        pytest.skip("permission-denied fixture requires an unprivileged user")
    directory = tmp_path / "d"
    directory.mkdir()
    server = None
    if kind == "fifo":
        os.mkfifo(directory / "special")
    else:
        server = socket.socket(socket.AF_UNIX)
        try:
            server.bind(str(directory / "special"))
        except PermissionError:
            server.close()
            pytest.skip("sandbox does not permit Unix-domain socket fixtures")
    directory.chmod(0o400)
    try:
        args = ["-nL", "d"]
        env = parity_env()
        assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
            run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
        )
    finally:
        directory.chmod(0o700)
        if server is not None:
            server.close()


# Recursive names-only listing defers inaccessible known directories to the open stage.
@pytest.mark.parametrize(
    "options",
    [["-R"], ["-RL"], ["-RH"], ["-aR"], ["-AR"], ["-Rr"]],
)
def test_recursive_unsearchable_directory_open_stage_exact_gnu_bytes(
    options: list[str], tmp_path: Path
) -> None:
    if os.geteuid() == 0:
        pytest.skip("permission-denied fixture requires an unprivileged user")
    directory = tmp_path / "d"
    directory.mkdir()
    (directory / "child").mkdir()
    directory.chmod(0o400)
    try:
        args = options + ["d"]
        env = parity_env()
        assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
            run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
        )
    finally:
        directory.chmod(0o700)


# Recursive metadata modes report entry stat failure before attempting a child open.
@pytest.mark.parametrize("options", [["-nR"], ["-sR"], ["-tR"], ["-SR"], ["-nRL"], ["-sRH"]])
def test_recursive_metadata_failure_stage_exact_gnu_bytes(
    options: list[str], tmp_path: Path
) -> None:
    if os.geteuid() == 0:
        pytest.skip("permission-denied fixture requires an unprivileged user")
    directory = tmp_path / "d"
    directory.mkdir()
    (directory / "child").mkdir()
    directory.chmod(0o400)
    try:
        args = options + ["d"]
        env = parity_env()
        assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
            run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
        )
    finally:
        directory.chmod(0o700)


# Open failures suppress child headers and remain serious only for command-line operands.
@pytest.mark.parametrize("args", [["-R", "d"], ["-nR", "d"], ["-R", "d/child"]])
def test_recursive_unreadable_child_exact_gnu_bytes(args: list[str], tmp_path: Path) -> None:
    if os.geteuid() == 0:
        pytest.skip("permission-denied fixture requires an unprivileged user")
    child = tmp_path / "d" / "child"
    child.mkdir(parents=True)
    child.chmod(0)
    try:
        env = parity_env()
        assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
            run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
        )
    finally:
        child.chmod(0o700)


# Recursive follow modes preserve directory identities across physical and symlink paths.
@pytest.mark.parametrize(
    "args",
    [["-R", "alias"], ["-RH", "alias"], ["-RL", "alias"], ["-nR", "alias"], ["-nRL", "alias"]],
)
def test_recursive_symlink_open_identity_exact_gnu_bytes(args: list[str], tmp_path: Path) -> None:
    directory = tmp_path / "d"
    directory.mkdir()
    child = directory / "child"
    child.mkdir()
    (child / "leaf").write_bytes(b"x")
    (directory / "linked").symlink_to("child")
    (child / "back").symlink_to("..")
    (tmp_path / "alias").symlink_to("d")
    env = parity_env()
    assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
        run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
    )


# Queued directories preserve the file-group separator even if every directory open fails.
@pytest.mark.parametrize("options", [[], ["-R"], ["-nR"]])
def test_failed_directory_after_file_separator_exact_gnu_bytes(
    options: list[str], tmp_path: Path
) -> None:
    if os.geteuid() == 0:
        pytest.skip("permission-denied fixture requires an unprivileged user")
    (tmp_path / "file").write_bytes(b"x")
    directory = tmp_path / "d"
    directory.mkdir()
    directory.chmod(0)
    try:
        args = options + ["file", "d"]
        env = parity_env()
        assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
            run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
        )
    finally:
        directory.chmod(0o700)


# Recursive child paths remove trailing slashes while preserving the root operand spelling.
@pytest.mark.parametrize("option", ["-R", "-RL", "-nR", "-nRL"])
@pytest.mark.parametrize("operand", ["d/", "d//", "d///", "./d//", "d/./", "d/../d/"])
def test_recursive_trailing_slash_exact_gnu_bytes(
    option: str, operand: str, tmp_path: Path
) -> None:
    child = tmp_path / "d" / "child"
    child.mkdir(parents=True)
    (child / "file").write_bytes(b"x")
    (child / "back").symlink_to("..")
    (tmp_path / "d" / "broken").symlink_to("missing")
    args = [option, operand]
    env = parity_env()
    assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
        run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
    )


# Terminal operand slashes require a directory even when the operand names a symlink.
@pytest.mark.parametrize("options", [[], ["-n"], ["-nd"], ["-nR"], ["-d"], ["-L"], ["-H"]])
@pytest.mark.parametrize(
    "operand",
    [
        "",
        "alias",
        "alias/",
        "alias//",
        "file/",
        "file_alias/",
        "missing_alias/",
        "file/.",
        "file/..",
        "file/../d",
        "missing/../d",
    ],
)
def test_operand_trailing_slash_lookup_exact_gnu_bytes(
    options: list[str], operand: str, tmp_path: Path
) -> None:
    (tmp_path / "d").mkdir()
    (tmp_path / "d" / "leaf").write_bytes(b"x")
    (tmp_path / "file").write_bytes(b"x")
    (tmp_path / "alias").symlink_to("d")
    (tmp_path / "file_alias").symlink_to("file")
    (tmp_path / "missing_alias").symlink_to("missing")
    args = options + [operand]
    env = parity_env()
    assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
        run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
    )


# An explicit empty operand stays an access failure alongside a successful file.
@pytest.mark.parametrize("options", [[], ["-n"], ["-d"]])
def test_mixed_empty_operand_exact_gnu_bytes(options: list[str], tmp_path: Path) -> None:
    (tmp_path / "file").write_bytes(b"x")
    args = options + ["", "file"]
    env = parity_env()
    assert run_bench_utility(BENCH_LS_DLL, args, tmp_path, env=env) == (
        run_coreutils_utility(COREUTILS_LS, "ls", args, tmp_path, env=env)
    )
