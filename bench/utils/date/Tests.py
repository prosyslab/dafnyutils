"""Strict GNU date comparisons and separate Dafny proof checks."""

import subprocess
from pathlib import Path

import pytest

from benchmark_tools.execution import run_candidate
from benchmark_tools.test_support import (
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
UTILITY = "date"
PROJECT = ROOT / "bench" / "utils" / UTILITY


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    """Use candidate and GNU artifacts prepared by the supported build targets."""
    candidate = bench_dll_path(ROOT, ROOT / "_build/bench/date_bench.dll")
    reference = coreutils_binary_path(ROOT, ROOT / "_build/coreutils/src/date")
    assert candidate.is_file(), "Build date first with make -C bench/utils/date build"
    assert reference.is_file(), "Prepare GNU coreutils first with make build-coreutils"
    return reference, candidate


def assert_parity(executables: tuple[Path, Path], args: list[str]) -> tuple[bytes, bytes, int]:
    """Compare unmodified streams and exit status at one stable source timestamp."""
    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, args, ROOT)
    actual = run_bench_utility(candidate, args, ROOT)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)
    return expected


# Select the existing file's modification timestamp through every required spelling and format.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        ["--reference=bench/utils/date/benchmark.yaml", "+%s"],
        ["-u", "--reference=bench/utils/date/benchmark.yaml", "+%Y-%m-%d"],
        ["-r", "bench/utils/date/benchmark.yaml", "+%H:%M:%S"],
        ["--reference=bench/utils/date/benchmark.yaml", "+%s.%N"],
        ["--reference=bench/utils/date"],
    ],
)
def test_reference_time(executables: tuple[Path, Path], args: list[str]) -> None:
    # upstream: coreutils/tests/date/reference.sh
    # Port the modification-time-only selection and directory-reference scenarios.
    assert_parity(executables, args)


# Reproduce the C-locale directive groups from the named upstream date table rows.
@pytest.mark.integration
@pytest.mark.parametrize(
    "format",
    [
        "%% %a %A %b %B",
        "%d_%D_%e_%h_%H",
        "%I_%j_%k_%l_%m",
        "%M_%n_%p_%r",
        "%s_%S_%t_%T",
        "%U_%V_%w_%W",
        "%x_%X_%y_%Y",
        "%z",
        "%c",
        "%q",
        "%G %g %V",
    ],
)
def test_upstream_directives(executables: tuple[Path, Path], format: str) -> None:
    # upstream: coreutils/tests/date/date.pl
    # Port rows 1, 3, 4, 5, 6, 7, 8, 9 and q-1 using the same d1 timestamp.
    assert_parity(executables, ["-d", "1997-01-19 08:17:48 +0", "+" + format])


# Preserve Gregorian leap and century boundaries, negative epochs, and extended years.
@pytest.mark.integration
@pytest.mark.parametrize(
    "date",
    [
        "@-1",
        "@-0.000000001",
        "@0",
        "@951782400.123456789",
        "@-2203977600",
        "@-62198755200",
        "@-62167219200",
        "@253402300800",
        "@-86400",
        "@86400",
    ],
)
def test_calendar_boundaries(executables: tuple[Path, Path], date: str) -> None:
    # upstream: coreutils/tests/date/date.pl
    # Adapt leap-1, date2sec-1, before-epoch and year formatting scenarios to exact epochs.
    assert_parity(executables, ["--date=" + date, "+%s.%N|%Y-%m-%d %H:%M:%S|%C|%y|%F|%j"])


# Keep GNU's negative zero century and positive short-year magnitude observable.
@pytest.mark.integration
def test_negative_year_century(executables: tuple[Path, Path]) -> None:
    # upstream: none - Regression derived from gnulib strftime.c negative_year/DO_YEARISH.
    assert assert_parity(executables, ["-d", "@-62198755200", "+%C|%y|%Y|%F"]) == (
        b"-0|01|-001|-001-01-01\n",
        b"",
        0,
    )


# Preserve the exact negative-year locale date that first failed the generated campaign.
@pytest.mark.integration
def test_negative_locale_date_regression(executables: tuple[Path, Path]) -> None:
    # upstream: none - Preserves fuzzer seed 1 iteration 264 and GNU strftime.c's libc %x fallback.
    assert assert_parity(
        executables,
        [
            "-d",
            "@-3187056888438.630696753",
            "+%V|%b|%b|%x|%p|%P",
        ],
    ) == (b"10|Mar|Mar|03/09/76|AM|am\n", b"", 0)


# C-locale composites preserve libc's modulo short year and unpadded signed full year.
@pytest.mark.integration
@pytest.mark.parametrize(
    "date", ["@-62198755200", "@-62924601600", "@-62167219200", "@-62135596800", "@-30641760000"]
)
def test_locale_composite_years(executables: tuple[Path, Path], date: str) -> None:
    # upstream: coreutils/tests/date/date.pl
    # Extend rows 2/8's C-locale %c/%x scenarios to negative and small years.
    assert_parity(executables, ["--date=" + date, "+%D|%x|%y|%c|%Y|%r|%X"])


# ISO week numbering follows the Thursday year across December and January.
@pytest.mark.integration
@pytest.mark.parametrize(
    "date", ["2015-12-31 UTC", "2016-01-01 UTC", "2017-01-01 UTC", "2019-12-30 UTC"]
)
def test_iso_week_boundaries(executables: tuple[Path, Path], date: str) -> None:
    # upstream: coreutils/tests/date/date.pl
    # Adapt V92-1, V92-2 and V92-3's ISO-week boundary relation.
    assert_parity(executables, ["--date=" + date, "+%Y %G %g %V %U %W %u %w"])


# RFC and ISO shortcuts select the same fixed UTC format and nanosecond precision as GNU.
@pytest.mark.integration
@pytest.mark.parametrize(
    "option",
    [
        "-I",
        "-Ihours",
        "-Iminutes",
        "-Iseconds",
        "-Ins",
        "--iso-8601=date",
        "-R",
        "--rfc-822",
        "--rfc-2822",
        "--rfc-email",
        "--rfc-3339=date",
        "--rfc-3339=seconds",
        "--rfc-3339=ns",
    ],
)
def test_format_shortcuts(executables: tuple[Path, Path], option: str) -> None:
    # upstream: coreutils/tests/date/date.pl
    # Port rfc822-1 and the ISO/RFC precision cases with an explicit epoch input.
    assert_parity(executables, ["--date=@853661868.123456789", option])


# Doubled percent sequences remain literal instead of triggering date and time conversion.
@pytest.mark.integration
@pytest.mark.parametrize("codes", ["HIklMNpPrRsSTXzZ", "aAbBcCdDeFgGhjmuUVwWxyY"])
def test_percent_percent(executables: tuple[Path, Path], codes: str) -> None:
    # upstream: coreutils/tests/date/percent-percent.sh
    # Port the C-locale time and date conversion groups using a deterministic date.
    assert_parity(executables, ["--date=@0", "+" + "".join("%%" + code for code in codes)])


# Report missing/inaccessible reference forms and source-selection errors without losing stderr.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        ["--reference"],
        ["--reference="],
        ["--reference=bench/utils/date/missing"],
        ["--reference=bench/utils/date/benchmark.yaml/child"],
        ["--date=@0", "--reference=bench/utils/date/benchmark.yaml"],
        ["--date=invalid-date", "+%s"],
        ["--date=@0", "not-a-format"],
        ["--date=@0", "+%s", "extra"],
        ["--date=@0", "-I", "+%s"],
        ["--iso-8601=bad"],
        ["--iso-8601="],
        ["--rfc-3339="],
        ["--rfc-3339=hours"],
        ["--bogus"],
        ["-uQ"],
        ["-ud"],
        ["--utc=yes"],
        ["--help", "--bogus"],
        ["--r"],
    ],
)
def test_diagnostics(executables: tuple[Path, Path], args: list[str]) -> None:
    # upstream: coreutils/tests/date/reference.sh
    # Port missing reference, mutually exclusive source, and GNU getopt error scenarios.
    assert_parity(executables, args)


# Native localtime overflow is diagnosed even when the requested format is epoch seconds.
@pytest.mark.integration
@pytest.mark.parametrize("date", ["@9223372036854775807", "@-9223372036854775808"])
def test_time_out_of_range(executables: tuple[Path, Path], date: str) -> None:
    # upstream: coreutils/tests/date/date.pl
    # Adapt huge/out-of-range time scenarios to signed time_t endpoints.
    assert_parity(executables, ["--date=" + date, "+%s"])


# The complete GNU informational output is compared as raw bytes.
@pytest.mark.integration
@pytest.mark.parametrize("option", ["--help", "--version"])
def test_information(executables: tuple[Path, Path], option: str) -> None:
    # upstream: coreutils/tests/misc/help-version.sh
    # Port the utility's help/version interface.
    assert_parity(executables, [option])


# A failed stdout write reports the native errno and returns the GNU failure status.
@pytest.mark.integration
def test_full_stdout(executables: tuple[Path, Path]) -> None:
    # upstream: coreutils/tests/misc/write-errors.sh
    # Port the /dev/full output-failure scenario with a deterministic source.
    reference, candidate = executables
    args = ["--date=@0", "+%s"]
    with Path("/dev/full").open("wb") as full:
        expected = subprocess.run(
            ["date", *args],
            executable=reference,
            cwd=ROOT,
            env=parity_env(),
            stdout=full,
            stderr=subprocess.PIPE,
            check=False,
            timeout=60,
        )
        actual = run_candidate(
            candidate,
            args,
            cwd=ROOT,
            env=parity_env(),
            stdout=full,
            stderr=subprocess.PIPE,
            check=False,
            timeout=60,
        )
    assert expected.returncode == actual.returncode == 1
    assert expected.stderr == actual.stderr


# Check the direct entry contract and every task-owned executable/proof helper.
@pytest.mark.integration
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename",
    [
        "Impl/DateCore.dfy",
        "Proof/DateProof.dfy",
        "Impl/Date.dfy",
        "Proof/DateCalendar.dfy",
        "Proof/DateFormat.dfy",
        "Spec/DateModel.dfy",
        "Spec/DateSpec.dfy",
        "Spec/DateSchema.dfy",
    ],
)
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks the Dafny proof surface, independently of GNU execution.
    run_dafny_verify(PROJECT / filename)
