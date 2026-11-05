"""Observable GNU dd stream parity; the benchmark cases never create fixture trees."""

import subprocess
from pathlib import Path

import pytest

from benchmark_tools.execution import run_candidate
from benchmark_tools.test_support import (
    BENCH_COMMAND_TIMEOUT_SEC,
    assert_result_matches_reference,
    bench_dll_path,
    coreutils_binary_path,
    evaluation_target_root,
    parity_env,
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])
PROJECT = ROOT / "bench" / "utils" / "dd"
pytestmark = pytest.mark.integration


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    """Consume artifacts prepared by the supported build/layout gate."""
    candidate = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "dd_bench.dll")
    assert candidate.is_file(), "build the candidate with make -C bench/utils/dd build"
    reference = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "dd")
    assert reference.is_file(), "build the pinned GNU reference with make build-coreutils"
    return reference, candidate


def assert_parity(
    executables: tuple[Path, Path], args: list[str], input_data: bytes = b""
) -> tuple[bytes, bytes, int]:
    reference, candidate = executables
    expected = run_coreutils_utility(reference, "dd", args, PROJECT, input_data=input_data)
    actual = run_bench_utility(candidate, args, PROJECT, input_data=input_data)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    return expected


# Suppress transfer statistics while retaining every binary byte in a plain copy.
def test_status_none_copy(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/dd/misc.sh
    payload = bytes(range(256)) + b"final\x00\xff"
    assert assert_parity(executables, ["status=none"], payload) == (payload, b"", 0)


# Honor GNU informational options regardless of surrounding operand positions.
@pytest.mark.parametrize("option", ["--help", "--version"])
@pytest.mark.parametrize("surrounding", ["before", "after", "both"])
def test_informational_option_position(
    executables: tuple[Path, Path], option: str, surrounding: str
) -> None:
    # upstream: coreutils/tests/help/help-version-getopt.sh
    args = (["BEFORE"] if surrounding in {"before", "both"} else []) + [option]
    if surrounding in {"after", "both"}:
        args.append("AFTER")
    assert assert_parity(executables, args)[2] == 0


# Change only ASCII case, including already converted input and high bytes.
@pytest.mark.parametrize("conversion", ["lcase", "ucase"])
@pytest.mark.parametrize(
    "input_data", [b"abcdefghijklmnopqrstuvwxyz\n", b"ABCDEFGHIJKLMNOPQRSTUVWXYZ\n"]
)
def test_case_conversion(
    executables: tuple[Path, Path], conversion: str, input_data: bytes
) -> None:
    # upstream: coreutils/tests/dd/conv-case.sh
    assert_parity(executables, ["status=none", f"conv={conversion}"], input_data)


# Make bs override even later ibs/obs settings before padding the final input block.
def test_bs_overrides_ibs_obs(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/dd/misc.sh
    assert assert_parity(
        executables, ["status=none", "bs=3", "ibs=10", "obs=10", "conv=sync"], b"x\n"
    ) == (b"x\n\0", b"", 0)


# Count bytes before globally swapping adjacent pairs across odd block boundaries.
@pytest.mark.parametrize("count_args", [["count=14B"], ["count=14", "iflag=count_bytes"]])
def test_byte_count_swab(executables: tuple[Path, Path], count_args: list[str]) -> None:
    # upstream: coreutils/tests/dd/bytes.sh
    assert assert_parity(
        executables,
        ["status=none", "ibs=3", "obs=5", "iflag=fullblock", "conv=swab", *count_args],
        b"0123456789abcdefghijklm\n",
    ) == (b"1032547698badc", b"", 0)


# Accumulate an entire input record while preserving the final short block.
def test_fullblock_stream(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/dd/misc.sh
    assert assert_parity(executables, ["status=none", "bs=4", "iflag=fullblock"], b"a\nb\n") == (
        b"a\nb\n",
        b"",
        0,
    )


# Reject the malformed recursive integer operands listed by GNU's byte-count test.
@pytest.mark.parametrize("value", ["B", "B1", "Bx1", "KBB", "BB", "KBb", "KBx", "x1", "1x", "1xx1"])
def test_invalid_integer(executables: tuple[Path, Path], value: str) -> None:
    # upstream: coreutils/tests/dd/bytes.sh
    assert assert_parity(executables, ["status=none", f"count={value}"])[2] == 1


# Keep the ambiguous zero multiplier warning even when status suppresses statistics.
def test_zero_multiplier_warning(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/dd/misc.sh
    result = assert_parity(executables, ["status=none", "count=0x1"])
    assert result[0] == b"" and result[2] == 0
    assert result[1] == b"dd: warning: '0x' is a zero multiplier; use '00x' if that is intended\n"


# Retain overflow caused by a recognized unit even when later suffix text is bad.
def test_overflow_before_invalid_suffix(executables: tuple[Path, Path]) -> None:
    # upstream: none - GNU dd parse_integer/xstrtoumax overflow precedence.
    assert assert_parity(executables, ["status=none", "count=9223372036854775808bad"])[2] == 1


# Let a zero multiplier cancel the overflow result before classifying its suffix.
def test_zero_cancels_suffix_overflow(executables: tuple[Path, Path]) -> None:
    # upstream: none - GNU dd parse_integer recursive zero-multiplier behavior.
    result = assert_parity(
        executables, ["status=none", "count=0x9223372036854775808bad"], b"must remain unread"
    )
    assert result == (
        b"",
        b"dd: warning: '0x' is a zero multiplier; use '00x' if that is intended\n",
        0,
    )


# Preserve the distinct direct, full-buffer and final-buffer write diagnostics.
@pytest.mark.parametrize(
    ("operands", "payload"),
    [
        (["bs=3", "iflag=fullblock"], b"ABCDE\x00\xffremaining"),
        (["bs=3", "iflag=fullblock", "conv=lcase,swab"], b"ABCDE\x00\xffremaining"),
        (["bs=64", "iflag=fullblock", "conv=lcase,swab"], b"ABCDE\x00\xffremaining"),
        (["bs=3", "iflag=fullblock", "conv=lcase,swab"], b"ABC"),
    ],
    ids=["direct", "buffered-full", "buffered-final", "swab-carry-fills-final-block"],
)
def test_full_output(executables: tuple[Path, Path], operands: list[str], payload: bytes) -> None:
    # upstream: none - Native error boundary required by docs/implementation-notes.md.
    reference, candidate = executables
    args = ["status=none", *operands]
    with Path("/dev/full").open("wb") as full:
        expected = subprocess.run(
            ["dd", *args],
            executable=str(reference),
            cwd=PROJECT,
            input=payload,
            stdout=full,
            stderr=subprocess.PIPE,
            env=parity_env(),
            timeout=BENCH_COMMAND_TIMEOUT_SEC,
            check=False,
        )
        actual = run_candidate(
            candidate,
            args,
            cwd=PROJECT,
            input=payload,
            stdout=full,
            stderr=subprocess.PIPE,
            env=parity_env(),
            timeout=BENCH_COMMAND_TIMEOUT_SEC,
            check=False,
        )
    assert expected.returncode == actual.returncode == 1
    assert expected.stderr == actual.stderr


# Verify every task-local module needed for the direct RunCore specification.
@pytest.mark.dafny_verify
@pytest.mark.parametrize("filename", ["Impl/DdCore.dfy", "Proof/DdProof.dfy", "Impl/Dd.dfy"])
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks the proof surface independently of GNU parity.
    run_dafny_verify(PROJECT / filename)
