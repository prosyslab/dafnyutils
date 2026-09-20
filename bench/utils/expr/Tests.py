"""Check expr argv expression parity against GNU coreutils and verify proof surface."""

import fcntl
import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest

from tools.bench.bench_test_support import (
    BENCH_COMMAND_TIMEOUT_SEC,
    assert_requested_message_behavior,
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

BENCH_EXPR_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "expr_bench.dll")
COREUTILS_EXPR = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / "expr")
EXPR_VERIFY_TARGETS = [
    ROOT / "bench" / "utils" / "expr" / "ExprSpec.dfy",
    ROOT / "bench" / "utils" / "expr" / "ExprCore.dfy",
    ROOT / "bench" / "utils" / "expr" / "ExprProof.dfy",
    ROOT / "bench" / "utils" / "expr" / "Expr.dfy",
]


def system_gnu_expr() -> Path | None:
    candidate = shutil.which("expr")
    if candidate is None:
        return None
    completed = subprocess.run(
        [candidate, "--version"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        env=parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    if "GNU coreutils" not in completed.stdout:
        return None
    return Path(candidate)


@pytest.fixture(scope="session", autouse=True)
def build_expr_once(request: pytest.FixtureRequest) -> None:
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
            not BENCH_EXPR_DLL.exists()
            or latest_bench_utility_source_mtime(ROOT, "expr") > BENCH_EXPR_DLL.stat().st_mtime
        ):
            build_bench_utility(ROOT, "expr")
        if not COREUTILS_EXPR.exists() and (ROOT / "coreutils" / "bootstrap").exists():
            build_coreutils_utility(ROOT, "expr")
        fcntl.flock(lock_file, fcntl.LOCK_UN)


@pytest.fixture(scope="session")
def reference_expr() -> Path:
    if COREUTILS_EXPR.exists():
        return COREUTILS_EXPR
    fallback = system_gnu_expr()
    if fallback is None:
        pytest.skip("GNU expr reference binary is unavailable")
    return fallback


def run_bench_expr(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_bench_utility(BENCH_EXPR_DLL, args, cwd, env=parity_env())


def run_system_expr(binary: Path, args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(binary, "expr", args, cwd, env=parity_env())


def assert_expr_parity(args: list[str], reference: Path) -> None:
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        ref = run_system_expr(reference, args, cwd)
        bench = run_bench_expr(args, cwd)
        assert_result_matches_reference(ref, bench)


@pytest.mark.parametrize(
    "args",
    [
        ["1", "+", "2"],
        ["7", "-", "9"],
        ["5", "*", "3"],
        ["7", "/", "2"],
        ["7", "%", "3"],
        ["-5", "/", "2"],
        ["-5", "%", "2"],
        ["(", "1", "+", "2", ")", "*", "3"],
        ["1", "+", "2", "*", "3"],
    ],
)
def test_arithmetic_and_precedence_match_coreutils(args: list[str], reference_expr: Path) -> None:
    # upstream: coreutils/tests/expr/expr.pl
    assert_expr_parity(args, reference_expr)


@pytest.mark.parametrize(
    "args",
    [
        ["0", "|", "fallback"],
        ["00", "|", "fallback"],
        ["word", "|", "fallback"],
        ["word", "&", "other"],
        ["word", "&", "0"],
        ["", "|", "fallback"],
        ["", "&", "fallback"],
    ],
)
def test_boolean_expression_groups_match_coreutils(args: list[str], reference_expr: Path) -> None:
    # upstream: coreutils/tests/expr/expr.pl
    assert_expr_parity(args, reference_expr)


@pytest.mark.parametrize(
    "args",
    [
        ["10", ">", "2"],
        ["10", "<", "2"],
        ["a", "<", "b"],
        ["b", ">=", "b"],
        ["+0", "=", "0"],
        ["00", "=", "0"],
        ["1", "<", "2", "<", "3"],
    ],
)
def test_numeric_and_lexical_comparisons_match_coreutils(
    args: list[str], reference_expr: Path
) -> None:
    # upstream: coreutils/tests/expr/expr.pl
    assert_expr_parity(args, reference_expr)


@pytest.mark.parametrize(
    "args",
    [
        ["length", "abc"],
        ["length", ""],
        ["length", "abc", "+", "2"],
        ["substr", "abcdef", "2", "3"],
        ["substr", "abc", "x", "2"],
        ["substr", "abc", "0", "2"],
        ["index", "abc", "cb"],
        ["index", "abc", "z"],
    ],
)
def test_string_functions_match_coreutils(args: list[str], reference_expr: Path) -> None:
    # upstream: coreutils/tests/expr/expr.pl
    assert_expr_parity(args, reference_expr)


# Quoted literal tokens preserve their text, including UTF-8 output bytes.
@pytest.mark.parametrize(
    "args",
    [
        ["--", "1", "+", "2"],
        ["--", "--help"],
        ["+", "--help"],
        ["+", "|"],
        ["+", "é"],
        ["length", "*"],
    ],
)
def test_double_dash_and_quoted_tokens_match_coreutils(
    args: list[str], reference_expr: Path
) -> None:
    # upstream: coreutils/tests/expr/expr.pl
    assert_expr_parity(args, reference_expr)


@pytest.mark.parametrize(
    "args",
    [
        [],
        ["1", "+"],
        ["1", "+", "a"],
        ["1", "/", "0"],
        ["1", "+", "2", "3"],
        ["(", "1", "+", "2"],
    ],
)
def test_error_status_and_stdout_match_coreutils(args: list[str], reference_expr: Path) -> None:
    # upstream: coreutils/tests/expr/expr.pl
    assert_expr_parity(args, reference_expr)


def test_help_and_version_exit_successfully(reference_expr: Path) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    with tempfile.TemporaryDirectory() as tmp_dir:
        cwd = Path(tmp_dir)
        for args in (["--help"], ["--version"]):
            ref = run_system_expr(reference_expr, args, cwd)
            bench = run_bench_expr(args, cwd)
            assert_requested_message_behavior(ref, bench)


def test_deferred_expr_multibyte_placeholder() -> None:
    # Not ported yet: this needs locale-provisioned multibyte fixtures and
    # locale-aware expectations beyond the current C-locale parity harness.
    # upstream: coreutils/tests/expr/expr-multibyte.pl
    pytest.skip("requires multibyte locale fixtures in the parity runner")


@pytest.mark.dafny_verify
@pytest.mark.parametrize("target", EXPR_VERIFY_TARGETS, ids=lambda path: path.name)
def test_expr_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface rather than an upstream runtime script.
    run_dafny_verify(target)
