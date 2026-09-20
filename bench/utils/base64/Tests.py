"""Check base64 byte-transform parity against GNU coreutils and verify proof surface."""

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

BENCH_BASE64_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "base64_bench.dll")
COREUTILS_BASE64 = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "base64")
BASE64_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "base64" / "Base64Schema.dfy",
    ROOT / "bench" / "utils" / "base64" / "Base64Core.dfy",
    ROOT / "bench" / "utils" / "base64" / "Base64Spec.dfy",
    ROOT / "bench" / "utils" / "base64" / "Base64Proof.dfy",
    ROOT / "bench" / "utils" / "base64" / "Base64.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_base64_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_BASE64_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "base64") > BENCH_BASE64_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "base64")
        if not COREUTILS_BASE64.exists():
            build_coreutils_utility(ROOT, "base64")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_base64(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_BASE64_DLL, args, cwd, input_data=input_data)


def run_system_base64(
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_BASE64, "base64", args, cwd, input_data=input_data)


def assert_base64_parity(args: list[str], cwd: Path, *, input_data: bytes = b"") -> None:
    ref = run_system_base64(args, cwd, input_data=input_data)
    bench = run_bench_base64(args, cwd, input_data=input_data)
    assert_result_matches_reference(ref, bench)


# Encoding stdin emits RFC 4648 base64 with the default trailing newline.
def test_encode_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_base64_parity([], cwd, input_data=b"aaaaa")


# Decoding stdin accepts a normal padded base64 payload.
def test_decode_stdin_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_base64_parity(["--decode"], cwd, input_data=b"YWE=")


# Decoding continues after valid padded quartets.
def test_decode_concatenated_padded_groups_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_base64_parity(["--decode"], cwd, input_data=b"MTIzNA==MTIzNA")


# Decode with --ignore-garbage skips non-alphabet bytes and succeeds.
def test_decode_ignore_garbage_skips_non_alphabet_bytes_matches_coreutils() -> None:
    # upstream: none - Adds base64 --ignore-garbage parity beyond upstream runtime coverage.
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_base64_parity(
            ["--decode", "--ignore-garbage"],
            cwd,
            input_data=b"Y W!F\tu\n",
        )


# Wrap width splits encoded output and keeps GNU's terminating newline.
def test_wrap_width_option_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_base64_parity(["--wrap=5"], cwd, input_data=b"aaaaa")


# Wrap width zero disables encoded line wrapping and the trailing newline.
def test_wrap_zero_disables_newline_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_base64_parity(["--wrap", "0"], cwd, input_data=b"a")


# Gnulib base64 encode vectors must match the utility's observable encoding.
@pytest.mark.parametrize(
    "payload",
    [
        b"",
        b"a",
        b"ab",
        b"abc",
        b"abcd",
        b"abcdefghijklmnop",
    ],
)
def test_gnulib_base64_encode_vectors_match_coreutils(payload: bytes) -> None:
    # upstream: coreutils/gnulib-tests/test-base64
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_base64_parity(["--wrap=0"], cwd, input_data=payload)


# Gnulib base64 decode context accepts embedded newlines across chunks.
def test_gnulib_base64_decode_newline_chunks_match_coreutils() -> None:
    # upstream: coreutils/gnulib-tests/test-base64
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        payload = b"YWJjZG\nVmZ2hp\namtsbW5vcA=="
        assert_base64_parity(["--decode"], cwd, input_data=payload)


# Gnulib invalid decode inputs must fail like GNU base64 decode.
@pytest.mark.parametrize(
    "payload",
    [
        b" ! ",
        b"abc\ndef",
        b"aa",
        b"aa=",
        b"aax",
        b"aa=X",
        b"aax=X",
        b"SGVsbG9=",
        b"TR==",
        b"TWF=TWE=",
    ],
)
def test_gnulib_base64_rejects_invalid_decode_inputs(payload: bytes) -> None:
    # upstream: coreutils/gnulib-tests/test-base64
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_base64_parity(["--decode"], cwd, input_data=payload)


# Invalid wrap before help is reported before the help request.
def test_invalid_wrap_before_help_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_base64(["--wrap=bad", "--help"], cwd)
        bench = run_bench_base64(["--wrap=bad", "--help"], cwd)
        assert_result_matches_reference(ref, bench)


# Help before a later missing required option value exits successfully.
def test_help_before_missing_wrap_value_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_base64(["--help", "operand", "--wrap"], cwd),
            run_bench_base64(["--help", "operand", "--wrap"], cwd),
        )


# First invalid wrap value is reported before a later help request.
def test_first_invalid_wrap_before_help_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_base64(["--wrap", "--decode", "--help", "-w", "-i"], cwd)
        bench = run_bench_base64(["--wrap", "--decode", "--help", "-w", "-i"], cwd)
        assert_result_matches_reference(ref, bench)


# Earlier invalid wrap values are reported before a later missing wrap value.
def test_invalid_wrap_before_missing_wrap_value_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_base64(["-w", "-w", "-d", "-w"], cwd)
        bench = run_bench_base64(["-w", "-w", "-d", "-w"], cwd)
        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Invalid wrap before version is reported before the version request.
def test_invalid_wrap_before_version_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_base64(["--wrap=bad", "--version"], cwd)
        bench = run_bench_base64(["--wrap=bad", "--version"], cwd)
        assert_result_matches_reference(ref, bench)


# Invalid wrap is reported before checking extra operands.
def test_invalid_wrap_before_extra_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_base64(["--wrap=bad", "one", "two"], cwd)
        bench = run_bench_base64(["--wrap=bad", "one", "two"], cwd)
        assert_result_matches_reference(ref, bench)


# A single named input file is encoded instead of stdin.
def test_named_file_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "payload.txt").write_bytes(b"abc")
        assert_base64_parity(["payload.txt"], cwd, input_data=b"ignored")


# A symlink to a directory reports GNU base64's stream read diagnostic.
def test_symlink_to_directory_read_error_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "target").mkdir()
        (cwd / "input-link").symlink_to("target", target_is_directory=True)
        ref = run_system_base64(["input-link"], cwd)
        bench = run_bench_base64(["input-link"], cwd)
        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


# Invalid decode input reports failure without hiding stdout or exit status.
def test_invalid_decode_input_matches_coreutils_exit_and_stdout() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_base64(["--decode"], cwd, input_data=b"a")
        bench = run_bench_base64(["--decode"], cwd, input_data=b"a")
        assert_result_matches_reference(ref, bench)


# Decode rejects non-newline whitespace without ignore-garbage.
def test_decode_rejects_tab_without_ignore_garbage_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_base64(["--decode"], cwd, input_data=b"\t")
        bench = run_bench_base64(["--decode"], cwd, input_data=b"\t")
        assert_result_matches_reference(ref, bench)


# Invalid one-byte padding bits preserve partial stdout and fail.
def test_invalid_one_byte_padding_bits_match_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_base64(["--decode"], cwd, input_data=b"YR==")
        bench = run_bench_base64(["--decode"], cwd, input_data=b"YR==")
        assert_result_matches_reference(ref, bench)


# Invalid two-byte padding bits preserve partial stdout and fail.
def test_invalid_two_byte_padding_bits_match_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_base64(["--decode"], cwd, input_data=b"YWF=")
        bench = run_bench_base64(["--decode"], cwd, input_data=b"YWF=")
        assert_result_matches_reference(ref, bench)


# A second file operand is rejected like GNU base64.
def test_extra_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/basenc/base64.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        (cwd / "one").write_bytes(b"a")
        (cwd / "two").write_bytes(b"b")
        assert_base64_parity(["one", "two"], cwd)


# Help exits successfully with the shared requested-message contract.
def test_help_exits_successfully_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_base64(["--help"], cwd),
            run_bench_base64(["--help"], cwd),
        )


# Version exits successfully with the shared requested-message contract.
def test_version_exits_successfully_matches_coreutils() -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_requested_message_behavior(
            run_system_base64(["--version"], cwd),
            run_bench_base64(["--version"], cwd),
        )


# Deferred basenc regressions identify broad behavior outside this first slice.
def test_deferred_base64_regressions_inventory() -> None:
    # Not ported yet: bounded-memory behavior requires large streaming fixtures.
    # Not ported yet: non-base64 alphabets belong to the broader basenc family.
    # upstream: coreutils/tests/basenc/basenc.pl
    # upstream: coreutils/tests/basenc/bounded-memory.sh
    pytest.skip("requires broader basenc alphabet and bounded-memory coverage")


# Dafny modules for base64 verify independently.
@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", BASE64_VERIFY_TARGETS, ids=lambda path: path.name)
def test_base64_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
