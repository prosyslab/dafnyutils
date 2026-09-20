"""Check readlink symlink-target parity against GNU coreutils and verify its proof surface."""

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

BENCH_READLINK_DLL = bench_dll_path(
    ROOT,
    ROOT / "_build" / "bench" / "readlink_bench.dll",
)
COREUTILS_READLINK = coreutils_binary_path(
    ROOT,
    ROOT / "_build" / "coreutils" / "src" / "readlink",
)
READLINK_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "readlink" / "ReadlinkCore.dfy",
    ROOT / "bench" / "utils" / "readlink" / "ReadlinkProof.dfy",
    ROOT / "bench" / "utils" / "readlink" / "Readlink.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_readlink_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_READLINK_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "readlink")
            > BENCH_READLINK_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "readlink")
        if not COREUTILS_READLINK.exists():
            build_coreutils_utility(ROOT, "readlink")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_readlink(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_READLINK_DLL, args, cwd)


def run_system_readlink(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_READLINK, "readlink", args, cwd)


def verify_readlink_module(target: Path) -> None:
    run_dafny_verify(target)


def normalize_stderr(stderr: bytes) -> bytes:
    text = stderr.decode("utf-8")
    text = text.replace("‘", "'").replace("’", "'")
    text = re.sub(r"(?m)^[^\n]*readlink: ", "readlink: ", text)
    text = re.sub(
        r"Try '.*readlink --help' for more information\.\n",
        "Try 'readlink --help' for more information.\n",
        text,
    )
    return text.encode("utf-8")


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
    *,
    check_error_stderr: bool = False,
) -> None:
    assert_result_matches_reference(
        ref_result,
        bench_result,
        stderr_normalizer=normalize_stderr,
        ignore_stderr_when_exit_nonzero=not check_error_stderr,
    )


def make_link_fixture(cwd: Path) -> None:
    _ = (cwd / "target.txt").write_text("target\n", encoding="utf-8")
    _ = (cwd / "regular.txt").write_text("regular\n", encoding="utf-8")
    (cwd / "dir").mkdir()
    (cwd / "link").symlink_to("target.txt")
    (cwd / "broken").symlink_to("missing-target")
    (cwd / "dir" / "nested-link").symlink_to("../target.txt")


def make_gnulib_readlink_fixture(cwd: Path) -> None:
    _ = (cwd / "file").write_text("regular\n", encoding="utf-8")
    (cwd / "dir").mkdir()
    (cwd / "link-to-dir").symlink_to("dir")
    (cwd / "link-chain-to-dir").symlink_to("link-to-dir")
    (cwd / "link-to-file").symlink_to("file")


@pytest.mark.parametrize("args", [["link"], ["broken"], ["dir/nested-link"]])
def test_reads_symlink_target_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/readlink/rl-1.sh
    # upstream: coreutils/tests/readlink/multi.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        make_link_fixture(cwd)
        ref = run_system_readlink(args, cwd)
        bench = run_bench_readlink(args, cwd)
        assert_same_result(ref, bench)


# Symlink target text must be emitted as UTF-8 bytes, including non-ASCII characters.
def test_unicode_symlink_target_matches_coreutils() -> None:
    # upstream: none - Repository regression for UTF-8 encoding of Unicode symlink targets.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        target = "대상-😀.txt"
        (cwd / "link").symlink_to(target)
        ref = run_system_readlink(["link"], cwd)
        bench = run_bench_readlink(["link"], cwd)
        assert ref == (target.encode("utf-8") + b"\n", b"", 0)
        assert_same_result(ref, bench)


@pytest.mark.parametrize("args", [["-n", "link"], ["--no-newline", "link"], ["-z", "link"]])
def test_delimiter_options_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/readlink/rl-1.sh
    # upstream: coreutils/tests/readlink/multi.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        make_link_fixture(cwd)
        ref = run_system_readlink(args, cwd)
        bench = run_bench_readlink(args, cwd)
        assert_same_result(ref, bench)


@pytest.mark.parametrize("args", [["link", "broken"], ["-z", "link", "broken"]])
def test_multiple_symlink_operands_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/readlink/rl-1.sh
    # upstream: coreutils/tests/readlink/multi.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        make_link_fixture(cwd)
        ref = run_system_readlink(args, cwd)
        bench = run_bench_readlink(args, cwd)
        assert_same_result(ref, bench)


def test_no_newline_warning_with_multiple_operands_matches_coreutils() -> None:
    # upstream: coreutils/tests/readlink/rl-1.sh
    # upstream: coreutils/tests/readlink/multi.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        make_link_fixture(cwd)
        args = ["-n", "link", "broken"]
        ref = run_system_readlink(args, cwd)
        bench = run_bench_readlink(args, cwd)
        assert_same_result(ref, bench, check_error_stderr=True)


@pytest.mark.parametrize("path_arg", ["regular.txt", "missing", "dir"])
def test_default_silent_read_errors_match_coreutils(path_arg: str) -> None:
    # upstream: coreutils/tests/readlink/rl-1.sh
    # upstream: coreutils/tests/readlink/multi.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        make_link_fixture(cwd)
        ref = run_system_readlink([path_arg], cwd)
        bench = run_bench_readlink([path_arg], cwd)
        assert_same_result(ref, bench)
        assert bench[0] == b""
        assert bench[1] == b""


def test_verbose_read_error_matches_coreutils() -> None:
    # upstream: coreutils/tests/readlink/rl-1.sh
    # upstream: coreutils/tests/readlink/multi.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        make_link_fixture(cwd)
        args = ["-v", "regular.txt"]
        ref = run_system_readlink(args, cwd)
        bench = run_bench_readlink(args, cwd)
        assert_same_result(ref, bench, check_error_stderr=True)


def test_verbose_read_error_quotes_shell_sensitive_path_matches_coreutils() -> None:
    # upstream: coreutils/tests/readlink/rl-1.sh
    # upstream: coreutils/tests/readlink/multi.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["-v", "2001-09-09 01:46:40 UTC"]
        ref = run_system_readlink(args, cwd)
        bench = run_bench_readlink(args, cwd)
        assert_same_result(ref, bench, check_error_stderr=True)


# GNU readlink rejects empty, non-symlink, and trailing-slash ordinary paths.
@pytest.mark.parametrize(
    "path_arg",
    [
        "",
        "no_such/",
        ".",
        "./",
        "file",
        "file/",
        "link-to-dir",
        "link-to-dir/",
        "link-chain-to-dir/",
        "link-to-file/",
    ],
)
def test_gnulib_readlink_ordinary_paths_match_coreutils(path_arg: str) -> None:
    # upstream: coreutils/gnulib-tests/test-readlink
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        make_gnulib_readlink_fixture(cwd)
        args = ["-v", path_arg]
        ref = run_system_readlink(args, cwd)
        bench = run_bench_readlink(args, cwd)
        assert_same_result(ref, bench, check_error_stderr=True)


@pytest.mark.parametrize(
    "args",
    [
        ["--quiet", "--verbose", "regular.txt"],
        ["--verbose", "--quiet", "regular.txt"],
        ["--verbose", "--silent", "regular.txt"],
    ],
)
def test_last_diagnostic_option_wins_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/readlink/rl-1.sh
    # upstream: coreutils/tests/readlink/multi.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        make_link_fixture(cwd)
        ref = run_system_readlink(args, cwd)
        bench = run_bench_readlink(args, cwd)
        assert_same_result(ref, bench, check_error_stderr=True)


def test_missing_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/readlink/rl-1.sh
    # upstream: coreutils/tests/readlink/multi.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_readlink([], cwd)
        bench = run_bench_readlink([], cwd)
        assert_same_result(ref, bench, check_error_stderr=True)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_readlink(args, cwd)
            bench = run_bench_readlink(args, cwd)
            assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize("args", [["--help", "--version"], ["--version", "--help"]])
def test_help_version_precedence_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_readlink(args, cwd)
        bench = run_bench_readlink(args, cwd)
        assert_requested_message_behavior(ref, bench)


@pytest.mark.parametrize("args", [["--bogus"], ["-/"]], ids=["unknown-long", "unknown-short"])
def test_parse_errors_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/readlink/rl-1.sh
    # upstream: coreutils/tests/readlink/multi.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_readlink(args, cwd)
        bench = run_bench_readlink(args, cwd)
        assert_same_result(ref, bench, check_error_stderr=True)


def test_deferred_readlink_canonicalize_placeholder() -> None:
    # Not ported yet: the benchmark parses canonicalization flags but marks
    # them unsupported, and the remaining cases need POSIXLY_CORRECT, root-path
    # canonicalization, or loop-detection fixtures that are outside this model.
    # upstream: coreutils/tests/readlink/readlink-posix.sh
    # upstream: coreutils/tests/readlink/can-e.sh
    # upstream: coreutils/tests/readlink/can-f.sh
    # upstream: coreutils/tests/readlink/can-m.sh
    # upstream: coreutils/tests/readlink/readlink-root.sh
    # upstream: coreutils/tests/readlink/readlink-fp-loop.sh
    pytest.skip("canonicalization and POSIX readlink modes are outside this benchmark")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", READLINK_VERIFY_TARGETS, ids=lambda path: path.name)
def test_readlink_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_readlink_module(target)
