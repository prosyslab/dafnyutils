"""Check pathchk parity against GNU coreutils and verify its Dafny proof surface."""

import subprocess
from pathlib import Path

import pytest

from tools.execution import run_candidate
from tools.test_support import (
    BENCH_COMMAND_TIMEOUT_SEC,
    assert_result_matches_reference,
    bench_dll_path,
    build_bench_utility,
    build_coreutils_utility,
    coreutils_binary_path,
    evaluation_target_root,
    parity_env,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])
UTILITY = "pathchk"
LINUX_ARG_BYTES = 128 * 1024 - 1
PROJECT = ROOT / "bench" / "utils" / UTILITY
BENCH_PATHCHK_DLL = bench_dll_path(ROOT, ROOT / "_build" / "bench" / "pathchk_bench.dll")
COREUTILS_PATHCHK = coreutils_binary_path(ROOT, ROOT / "_build" / "coreutils" / "src" / UTILITY)
PATHCHK_VERIFY_TARGETS = [
    PROJECT / "Spec/PathchkSchema.dfy",
    PROJECT / "Spec/PathchkSpec.dfy",
    PROJECT / "Impl/PathchkCore.dfy",
    PROJECT / "Proof/PathchkProof.dfy",
    PROJECT / "Impl/Pathchk.dfy",
]


@pytest.fixture(scope="session", autouse=True)
def build_pathchk_once(request: pytest.FixtureRequest) -> None:
    """Build runtime artifacts once; proof-only selections need no executable."""
    if request.session.items and all(
        item.get_closest_marker("dafny_verify") for item in request.session.items
    ):
        return
    build_bench_utility(ROOT, UTILITY)
    build_coreutils_utility(ROOT, UTILITY)


def run_bench_pathchk(
    args: list[str], cwd: Path, *, timeout: int = BENCH_COMMAND_TIMEOUT_SEC
) -> tuple[bytes, bytes, int]:
    completed = run_candidate(
        BENCH_PATHCHK_DLL,
        args,
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=parity_env(),
        timeout=timeout,
    )
    return completed.stdout, completed.stderr, completed.returncode


def run_system_pathchk(args: list[str], cwd: Path) -> tuple[bytes, bytes, int]:
    return run_coreutils_utility(COREUTILS_PATHCHK, UTILITY, args, cwd)


def assert_same_result(
    ref_result: tuple[bytes, bytes, int],
    bench_result: tuple[bytes, bytes, int],
) -> None:
    assert_result_matches_reference(ref_result, bench_result, ignore_stderr_when_exit_nonzero=False)


def verify_pathchk_module(target: Path) -> None:
    run_dafny_verify(target)


# Help and version requests must reproduce the pinned GNU output exactly.
@pytest.mark.integration
@pytest.mark.parametrize("args", [["--help"], ["--version"]], ids=["help", "version"])
def test_help_and_version_match_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/help/help-version.sh
    # case: pathchk --help and --version.
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# Help/version requests and parse errors must honor their command-line order.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        ["--help", "--version"],
        ["--version", "--help"],
        ["--help", "--bad"],
        ["--bad", "--help"],
        ["--version", "-x"],
    ],
)
def test_help_version_precedence_matches_coreutils(args: list[str]) -> None:
    # upstream: none - Source-derived help/version and parse-error ordering.
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# Every supported invocation without a name must report the missing operand.
@pytest.mark.integration
@pytest.mark.parametrize("args", [[], ["-p"], ["--portability"]])
def test_missing_operand_matches_coreutils(args: list[str]) -> None:
    # upstream: none - Source-derived missing-operand diagnostics.
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# Portable names and separators must pass without requiring filesystem objects.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        ["-p", "foo/bar.txt"],
        ["--portability", "foo/bar.txt"],
        ["-p", "foo/-bar"],
        ["-p", "///"],
        ["-p", ".", "..", "a//b/"],
        ["-p", "-"],
        ["--po", "foo"],
    ],
)
def test_portable_name_matrix_matches_coreutils(args: list[str]) -> None:
    # upstream: none - Source-derived portable-name and option forms.
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# Extra portability must reject a leading hyphen with either bundled flag order.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [["-pP", "foo/-bar"], ["-Pp", "foo/-bar"], ["--portability", "--", "-"]],
)
def test_leading_hyphen_matches_coreutils(args: list[str]) -> None:
    # upstream: coreutils/tests/misc/pathchk.sh
    # case: -p -P x/-; adapted to equivalent supported flag forms.
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# An empty name must fail even though no filesystem lookup is performed.
@pytest.mark.integration
def test_empty_name_matches_coreutils() -> None:
    # upstream: coreutils/tests/misc/pathchk.sh
    # case: -p with an empty operand must fail.
    args = ["-p", ""]
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# Byte-length boundaries must distinguish portable names from excessive components or paths.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        ["-p", "a" * 14],
        ["-p", "a" * 15],
        ["-p", "a/" * 127 + "a"],
        ["-p", "a/" * 128],
        ["-p", "a" * 15 + "/" + "b" * 16],
        ["-p", "a" * 256],
    ],
)
def test_length_boundaries_match_coreutils(args: list[str]) -> None:
    # upstream: none - Source-derived path/component byte boundaries.
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# Combined violations must report the error selected by GNU's precedence.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        ["-p", "a" * 256 + "@"],
        ["-p", "a" * 15 + "/bad@"],
        ["--portability", "foo/-bad@"],
    ],
)
def test_error_precedence_matches_coreutils(args: list[str]) -> None:
    # upstream: none - Source-derived ordering of combined violations.
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# A failed name must not stop later names or reorder their diagnostics.
@pytest.mark.integration
def test_multiple_operands_match_coreutils() -> None:
    # upstream: none - Source-derived continued checking after invalid names.
    args = ["-p", "good", "bad@", "", "also_good"]
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# Non-portable names must preserve GNU's byte and path quoting in C locale.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        ["-p", "a b"],
        ["-p", "a'b"],
        ["-p", 'a"b'],
        ["-p", "a\\b"],
        ["-p", "a\nb"],
        ["-p", "a\tb"],
        ["-p", "é"],
        ["-p", "한글"],
        ["-p", "😀"],
    ],
)
def test_nonportable_character_quoting_matches_coreutils(args: list[str]) -> None:
    # upstream: none - Source-derived C-locale byte and pathname quoting.
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# Option parsing must stop at the first operand.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [["-p", "foo", "--help"], ["--portability", "foo", "-p"], ["-p", "--help", "foo"]],
)
def test_option_operand_order_matches_coreutils(args: list[str]) -> None:
    # upstream: none - Source-derived stop-at-first-operand parsing.
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# Invalid short options and long-option values must reproduce GNU diagnostics.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [["-pPx"], ["-pé"], ["--po=x"], ["--he=x"], ["--ver=x"], ["--=x"], ["--unknown"]],
)
def test_parse_errors_match_coreutils(args: list[str]) -> None:
    # upstream: none - Source-derived GNU option-error diagnostics.
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT))


# A failing stdout must report the help-write error and return failure.
@pytest.mark.integration
def test_help_write_failure_matches_coreutils() -> None:
    # upstream: none - Covers close_stdout failure through /dev/full.
    with open("/dev/full", "wb") as sink:
        reference = subprocess.run(
            [UTILITY, "--help"],
            executable=str(COREUTILS_PATHCHK),
            cwd=ROOT,
            env=parity_env(),
            stdout=sink,
            stderr=subprocess.PIPE,
            check=False,
            timeout=BENCH_COMMAND_TIMEOUT_SEC,
        )
        candidate = run_candidate(
            BENCH_PATHCHK_DLL,
            ["--help"],
            cwd=ROOT,
            env=parity_env(),
            stdout=sink,
            stderr=subprocess.PIPE,
            text=False,
            check=False,
            timeout=BENCH_COMMAND_TIMEOUT_SEC,
        )
    assert (reference.stderr, reference.returncode) == (candidate.stderr, candidate.returncode)
    assert reference.returncode == 1


# Long names must preserve diagnostics without exceeding the ordinary process budget.
@pytest.mark.integration
@pytest.mark.parametrize(
    "path_arg",
    [
        pytest.param("a" * 100000, id="plain"),
        pytest.param("/" * 100000, id="separators"),
        pytest.param("a" * 99999 + "'", id="double-quote-shortcut"),
        pytest.param("é" * 50000, id="utf8-bytes"),
        pytest.param("a'\n" * 33333 + "a", id="mixed-shell-and-ansi-quotes"),
    ],
)
def test_long_name_diagnostics_match_coreutils(path_arg: str) -> None:
    # upstream: none - Reproduces long-name timeout across GNU quoting branches.
    args = ["-p", path_arg]
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT, timeout=10))


# Long option errors must retain the complete token within the process budget.
@pytest.mark.integration
@pytest.mark.parametrize(
    "args",
    [
        pytest.param(["-" + "p" * (LINUX_ARG_BYTES - 2) + "x"], id="unknown-short-option"),
        pytest.param(["--" + "x" * (LINUX_ARG_BYTES - 2)], id="unknown-long-option"),
        pytest.param(
            ["-" + "p" * (LINUX_ARG_BYTES - 1), "--" + "x" * (LINUX_ARG_BYTES - 2)],
            id="bundled-prefix-before-error",
        ),
    ],
)
def test_long_parse_errors_match_coreutils(args: list[str]) -> None:
    # upstream: none - Reproduces the long-token parse-error timeout.
    assert_same_result(run_system_pathchk(args, ROOT), run_bench_pathchk(args, ROOT, timeout=10))


# Each selected module must verify independently, including the final entry contract.
@pytest.mark.dafny_verify
@pytest.mark.integration
@pytest.mark.parametrize("target", PATHCHK_VERIFY_TARGETS, ids=lambda path: path.name)
def test_pathchk_verified_surface_targets(target: Path) -> None:
    # upstream: none - Verifies the Dafny proof surface, not GNU runtime behavior.
    verify_pathchk_module(target)
