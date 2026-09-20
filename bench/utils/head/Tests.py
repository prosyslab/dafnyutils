"""Check head line and byte selection parity against GNU coreutils and verify proof surface."""

import fcntl
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

BENCH_HEAD_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "head_bench.dll")
COREUTILS_HEAD = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "head")
HEAD_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "head" / "HeadSchema.dfy",
    ROOT / "bench" / "utils" / "head" / "HeadCore.dfy",
    ROOT / "bench" / "utils" / "head" / "HeadSpec.dfy",
    ROOT / "bench" / "utils" / "head" / "HeadProof.dfy",
    ROOT / "bench" / "utils" / "head" / "Head.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_head_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_HEAD_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "head") > BENCH_HEAD_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "head")
        if not COREUTILS_HEAD.exists():
            build_coreutils_utility(ROOT, "head")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_head(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_HEAD_DLL, args, cwd, input_data=input_data)


def run_system_head(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_HEAD, "head", args, cwd, input_data=input_data)


def assert_head_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_head(args, cwd, input_data=input_data)
    bench = run_bench_head(args, cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench)


@pytest.mark.parametrize(
    "payload",
    [
        b"",
        b"a",
        b"\n",
        b"a\n",
        b"1\n2\n3\n4\n5\n6\n7\n8\n9\n0\n",
        b"1\n2\n3\n4\n5\n6\n7\n8\n9\n0\nb\n",
    ],
)
def test_stdin_default_first_ten_lines_match_coreutils(payload: bytes) -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_head_parity([], cwd, input_data=payload)


def test_single_file_default_first_ten_lines_match_coreutils() -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"1\n2\n3\n4\n5\n6\n7\n8\n9\n0\nb\n")

        assert_head_parity(["input.txt"], cwd)


def test_file_and_stdin_operands_with_headers_match_coreutils() -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "first.txt").write_bytes(b"file-a\nfile-b\n")
        _ = (cwd / "second.txt").write_bytes(b"tail-a\ntail-b\n")

        assert_head_parity(
            ["first.txt", "-", "second.txt"],
            cwd,
            input_data=b"stdin-a\nstdin-b\n",
        )


def test_repeated_dash_consumes_stdin_once_match_coreutils() -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_head_parity(["-n", "2", "-", "-"], cwd, input_data=b"a\nb\nc\n")


@pytest.mark.parametrize(
    "args",
    [
        ["first.txt", "second.txt"],
        ["--quiet", "first.txt", "second.txt"],
        ["--silent", "first.txt", "second.txt"],
        ["--verbose", "first.txt"],
    ],
)
def test_header_modes_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "first.txt").write_bytes(b"a\nb\n")
        _ = (cwd / "second.txt").write_bytes(b"c\nd\n")

        assert_head_parity(args, cwd)


@pytest.mark.parametrize(
    "args",
    [
        ["-n", "2", "input.txt"],
        ["--lines=2", "input.txt"],
        ["-n", "0", "input.txt"],
        ["-n", "08", "input.txt"],
        ["--lines=-1", "input.txt"],
        ["-n", "-0", "input.txt"],
    ],
)
def test_line_count_options_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/head/head.pl
    # upstream: coreutils/tests/head/head-elide-tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"a\nb\nc\nd")

        assert_head_parity(args, cwd)


@pytest.mark.parametrize(
    "args",
    [
        ["-c", "3", "input.bin"],
        ["--bytes=3", "input.bin"],
        ["-c", "0", "input.bin"],
        ["-c", "08", "input.bin"],
        ["--bytes=-2", "input.bin"],
        ["-c", "-0", "input.bin"],
    ],
)
def test_byte_count_options_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/head/head.pl
    # upstream: coreutils/tests/head/head-elide-tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.bin").write_bytes(b"abcdefghij")

        assert_head_parity(args, cwd)


# Obsolete first-option line counts select the requested decimal line prefix.
def test_legacy_line_count_first_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_head_parity(["-08"], cwd, input_data=b"\n" * 12)


# Obsolete first-option byte counts match GNU's documented legacy forms.
@pytest.mark.parametrize("args", [["-1c"], ["-2b"], ["-1k"]])
def test_legacy_byte_count_first_option_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        payload = b"".join(f"{i}\n".encode() for i in range(601))
        assert_head_parity(args, cwd, input_data=payload)


# Obsolete first-option header suffixes match GNU quiet and verbose behavior.
@pytest.mark.parametrize("args", [["-1q", "first.txt", "second.txt"], ["-1v", "first.txt"]])
def test_legacy_header_suffixes_first_option_match_coreutils(args: list[str]) -> None:
    # upstream: none - Documents GNU head obsolete first-option suffix behavior.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "first.txt").write_bytes(b"a\nb\n")
        _ = (cwd / "second.txt").write_bytes(b"c\nd\n")

        assert_head_parity(args, cwd)


# Multiplier suffixes on modern count options use GNU finite stream semantics.
def test_multiplier_count_suffixes_match_coreutils() -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.bin").write_bytes(b"x" * 1500)

        assert_head_parity(["-c", "2b", "input.bin"], cwd)


# Zero-terminated line mode treats NUL as the record delimiter.
def test_zero_terminated_first_records_match_coreutils() -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_head_parity(["-z", "-n", "2"], cwd, input_data=b"a\0b\0c\0")


# Negative zero-terminated line mode elides records from the end.
def test_zero_terminated_all_but_last_record_matches_coreutils() -> None:
    # upstream: coreutils/tests/head/head.pl
    # upstream: coreutils/tests/head/head-elide-tail.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_head_parity(["--zero-terminated", "-n", "-1"], cwd, input_data=b"a\0b\0c\0")


def test_missing_file_continues_to_later_operand_match_coreutils() -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        _ = (cwd / "input.txt").write_bytes(b"ok\n")

        assert_head_parity(["missing.txt", "input.txt"], cwd)


def test_missing_file_with_space_operand_quotes_diagnostic_matches_coreutils() -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        args = ["a b"]
        ref = run_system_head(args, cwd)
        bench = run_bench_head(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


@pytest.mark.parametrize("args", [["-n", "1", "dir"], ["-n", "-1", "dir"], ["-c", "1", "dir"]])
def test_directory_operand_diagnostic_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/read-errors.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "dir").mkdir()
        ref = run_system_head(args, cwd)
        bench = run_bench_head(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


@pytest.mark.parametrize("args", [["-n", "bad"], ["--bytes=nope"]])
def test_invalid_count_diagnostic_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/head/head.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_head(args, cwd)
        bench = run_bench_head(args, cwd)
        assert_result_matches_reference(
            ref,
            bench,
            ignore_stderr_when_exit_nonzero=False,
        )


# Earlier invalid counts are reported before a later missing option value.
def test_invalid_count_before_missing_value_matches_coreutils() -> None:
    # upstream: none - Adds head diagnostic ordering parity for invalid and missing count values.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_head(["-q", "-n", "-z", "--lines"], cwd)
        bench = run_bench_head(["-q", "-n", "-z", "--lines"], cwd)
        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


def test_help_and_version_exit_successfully() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_head(args, cwd)
            bench = run_bench_head(args, cwd)
            assert_requested_message_behavior(ref, bench)


def test_deferred_head_regressions_inventory() -> None:
    # Not ported: obsolete first-argument syntax with unsupported trailing
    # letters outside `b`, `k`, `m`, `c`, `l`, `q`, `v`, and `z`.
    # Not ported: overflow diagnostics for very large counts are outside the
    # unbounded mathematical count parser used by this slice.
    # Not ported: write-errors entry `head -z -n-1 /dev/zero`.
    # Not ported: /dev/zero write-error behavior requires unbounded device
    # input and write-failure surfaces not modeled by the runner.
    # Not ported: head-c shell sequencing and buffering regressions.
    # Not ported: shell sequencing that observes shared stdin file offsets,
    # memory-limit behavior for huge negative byte counts, and procfs/sysfs
    # quasi-seekable files are outside the current subprocess/World model.
    # Not ported: it observes the input descriptor position after `head`
    # exits and includes large seekable-file positioning stress cases.
    # RUN_EXPENSIVE_TESTS and `---presume-input-pipe` variants.
    # Not ported: these are compile-time/internal buffering strategy tests.
    # Not ported: /dev/full, closed-pipe, and injected EIO behavior require
    # write-failure/fault-injection surfaces not modeled by the runner.
    # upstream: coreutils/tests/head/head.pl
    # upstream: coreutils/tests/head/head-c.sh
    # upstream: coreutils/tests/head/head-elide-tail.pl
    # upstream: coreutils/tests/head/head-pos.sh
    # upstream: coreutils/tests/head/head-write-error.sh
    # upstream: coreutils/tests/misc/io-errors.sh
    # upstream: coreutils/tests/misc/write-errors.sh
    pytest.skip("requires deferred head options or unmodeled host effects")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", HEAD_VERIFY_TARGETS)
def test_head_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
