"""Check printf parity for the verified literal, escape, and string-format subset."""

import fcntl
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
    parity_env,
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])

BENCH_PRINTF_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "printf_bench.dll")
COREUTILS_PRINTF = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "printf")
PRINTF_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "printf" / "Spec/PrintfSchema.dfy",
    ROOT / "bench" / "utils" / "printf" / "Impl/PrintfCore.dfy",
    ROOT / "bench" / "utils" / "printf" / "Proof/PrintfProof.dfy",
    ROOT / "bench" / "utils" / "printf" / "Impl/Printf.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_printf_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_PRINTF_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "printf") > BENCH_PRINTF_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "printf")
        if not COREUTILS_PRINTF.exists():
            build_coreutils_utility(ROOT, "printf")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


def run_bench_printf(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_PRINTF_DLL, args, cwd, env=parity_env())


def run_system_printf(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_PRINTF, "printf", args, cwd, env=parity_env())


def verify_printf_module(target: Path) -> None:
    run_dafny_verify(target)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    assert_result_matches_reference(ref_result, bench_result)


@pytest.mark.parametrize(
    "args",
    [
        ["hello"],
        ["line\\nnext\\tindent\\\\slash"],
        ["octal:\\0101\\0042"],
    ],
)
def test_literal_and_escape_formats_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/printf/printf.sh
    # upstream: coreutils/tests/printf/printf-cov.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printf(args, cwd)
        bench = run_bench_printf(args, cwd)
        assert_same_result(ref, bench)


# Every FORMAT escape class must match pinned GNU bytes and status exactly.
@pytest.mark.parametrize(
    "args",
    [
        [r"\a\b\e\f\n\r\t\v\\\""],
        [r"before\q\z\"after"],
        ["ends with \\"],
        [r"\0|\07|\077|\0101|\1234|\400|\777"],
        [r"\x4|\x41f|\xFF|\x00"],
        [r"\u0041|\u00E9|\u007F|\U0001F600|\U00110000"],
        [r"%s\x21", "left", "right"],
    ],
)
def test_format_escape_matrix_matches_coreutils(args: list[str]) -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_same_result(run_system_printf(args, cwd), run_bench_printf(args, cwd))


# Cancellation and malformed escapes retain GNU's emitted prefix and exit behavior.
@pytest.mark.parametrize(
    "args",
    [
        [r"prefix\cignored%s", "argument"],
        [r"%s:prefix\cignored", "first", "second"],
        [r"prefix\x"],
        [r"prefix\xQ"],
        [r"prefix\u123"],
        [r"prefix\U0011000Z"],
        [r"prefix\uD800"],
        [r"prefix\U0000Dabc"],
        [r"%s:prefix\xQ", "first", "second"],
    ],
)
def test_format_escape_termination_matches_coreutils(args: list[str]) -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_same_result(run_system_printf(args, cwd), run_bench_printf(args, cwd))


# Reproduce the saved escaping-audit printf failures on the current executable.
@pytest.mark.parametrize(
    "format_text",
    ["ijb-/c_44mg/g\\fkt97c/_kwg7f3qnoa", "sl\\h/19du7p", "f\\ffgwytu/t{74"],
)
def test_saved_format_escape_failures_match_coreutils(format_text: str) -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_same_result(
            run_system_printf([format_text], cwd), run_bench_printf([format_text], cwd)
        )


def test_literal_format_ignores_extra_arguments_with_warning() -> None:
    # upstream: coreutils/tests/printf/printf.sh
    # upstream: coreutils/tests/printf/printf-cov.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printf(["hello", "ignored"], cwd)
        bench = run_bench_printf(["hello", "ignored"], cwd)
        assert_result_matches_reference(ref, bench, stderr_mode="presence")


# Excess argument warnings use GNU's C-locale quotation of the unused operand.
@pytest.mark.parametrize("operand", ["apost'rophe", "tab\tname", "a\\b", "é"])
def test_excess_argument_locale_quoting_matches_coreutils(operand: str) -> None:
    # upstream: coreutils/tests/printf/printf.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        assert_same_result(
            run_system_printf(["literal", operand], cwd),
            run_bench_printf(["literal", operand], cwd),
        )


@pytest.mark.parametrize(
    "args",
    [
        ["%s:%s\\n", "left", "right"],
        ["<%s><%s>", "one"],
        ["%s,", "a", "b", "c"],
        ["%%:%s", "value"],
    ],
)
def test_string_directives_and_repetition_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/printf/printf.sh
    # upstream: coreutils/tests/printf/printf-cov.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printf(args, cwd)
        bench = run_bench_printf(args, cwd)
        assert_same_result(ref, bench)


def test_missing_format_operand_matches_coreutils() -> None:
    # upstream: coreutils/tests/printf/printf.sh
    # upstream: coreutils/tests/printf/printf-cov.pl
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printf([], cwd)
        bench = run_bench_printf([], cwd)
        assert_same_result(ref, bench)


# Informational modes match GNU output byte for byte.
@pytest.mark.parametrize("args", (["--help"], ["--version"]))
def test_help_and_version_exit_successfully(args: list[str]) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printf(args, cwd)
        bench = run_bench_printf(args, cwd)
        assert_result_matches_reference(ref, bench)


# Informational tokens with additional arguments are literal formats with exact excess warnings.
@pytest.mark.parametrize(
    "args",
    [
        ["--help", "--version"],
        ["--version", "--version"],
        ["--help", "--help"],
        ["--help", "--"],
        ["--", "--help"],
        ["--bogus", "x"],
    ],
)
def test_requested_message_excess_argument_warning_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_printf(args, cwd)
        bench = run_bench_printf(args, cwd)
        assert_result_matches_reference(ref, bench, ignore_stderr_when_exit_nonzero=False)


def test_deferred_printf_regressions_placeholder() -> None:
    # Not ported yet: the benchmarked printf intentionally covers only the
    # literal, escape, and `%s` subset, so numeric, indexed, multibyte, shell-
    # quoted, and stat-format surfaces remain outside the modeled behavior.
    # upstream: coreutils/tests/printf/printf-hex.sh
    # upstream: coreutils/tests/printf/printf-indexed.sh
    # upstream: coreutils/tests/printf/printf-mb.sh
    # upstream: coreutils/tests/printf/printf-surprise.sh
    # upstream: coreutils/tests/printf/printf-quote.sh
    # upstream: coreutils/tests/stat/stat-printf.pl
    pytest.skip("covers only the verified literal-and-string printf subset")


# Verify the argument schema and the implementation's proof obligations.
@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", PRINTF_VERIFY_TARGETS, ids=lambda path: path.name)
def test_printf_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    verify_printf_module(target)
