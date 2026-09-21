"""GNU parity cases for {{TASK_ID}}."""

from pathlib import Path

import pytest

from tools.bench.bench_test_support import (
    assert_result_matches_reference,
    bench_dll_path,
    build_bench_utility,
    build_coreutils_utility,
    coreutils_binary_path,
    evaluation_target_root,
    run_bench_utility,
    run_coreutils_utility,
    run_dafny_verify,
)

ROOT = evaluation_target_root(Path(__file__).resolve().parents[3])
UTILITY = "{{TASK_ID}}"
PROJECT = ROOT / "bench" / "utils" / UTILITY


@pytest.fixture(scope="session")
def executables() -> tuple[Path, Path]:
    """Build the two targets only for runtime cases; local Make targets use -n0."""
    build_bench_utility(ROOT, UTILITY)
    build_coreutils_utility(ROOT, UTILITY)
    return (
        coreutils_binary_path(ROOT, ROOT / "_build/coreutils/src" / UTILITY),
        bench_dll_path(ROOT, ROOT / "_build/bench" / f"{UTILITY}_bench.dll"),
    )


def assert_parity(
    executables: tuple[Path, Path],
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
) -> None:
    """Compare a read-only scenario, including stderr on error exits."""
    reference, candidate = executables
    expected = run_coreutils_utility(reference, UTILITY, args, cwd, input_data=input_data)
    actual = run_bench_utility(candidate, args, cwd, input_data=input_data)
    assert_result_matches_reference(expected, actual, ignore_stderr_when_exit_nonzero=False)


# Replace this failure with one agreed GNU scenario using executables and assert_parity.
def test_gnu_parity() -> None:
    # TODO: add the upstream source path inside the completed test body.
    pytest.fail("TODO: add a representative {{TASK_ID}} GNU parity case")


# Check each proof module as well as the entry contract required by make check.
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename", ["{{CLASS_NAME}}Core.dfy", "{{CLASS_NAME}}Proof.dfy", "{{CLASS_NAME}}.dfy"]
)
def test_verify_module(filename: str) -> None:
    # upstream: none - Checks the Dafny proof surface, not GNU runtime behavior.
    run_dafny_verify(PROJECT / filename)
