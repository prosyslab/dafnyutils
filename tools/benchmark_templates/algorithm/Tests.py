"""Raw command-line cases for {{TASK_ID}}."""

from pathlib import Path

import pytest

from benchmark_tools.test_support import (
    bench_dll_path,
    build_bench_utility,
    evaluation_target_root,
    run_bench_utility,
    run_dafny_verify,
)
from benchmarks.definition import BenchmarkDefinition
from benchmarks.runtime_cases import RuntimeCase, assert_runtime_observation, load_runtime_cases

SOURCE = Path(__file__).resolve().parent
ROOT = evaluation_target_root(SOURCE.parents[2])
UTILITY = "{{TASK_ID}}"
PROJECT = ROOT / SOURCE.relative_to(SOURCE.parents[2])
DEFINITION = BenchmarkDefinition.from_yaml_file(SOURCE / "benchmark.yaml")


@pytest.fixture(scope="session")
def candidate() -> Path:
    build_bench_utility(ROOT, UTILITY)
    return bench_dll_path(ROOT, ROOT / "_build/bench" / f"{UTILITY}_bench.dll")


# Every original positive input reaches the executable through standard input.
@pytest.mark.parametrize("case", load_runtime_cases(SOURCE / "cases.json"))
def test_runtime_case(candidate: Path, case: RuntimeCase) -> None:
    actual = run_bench_utility(candidate, [], ROOT, input_data=case.input.encode("utf-8"))
    assert_runtime_observation(case, actual, DEFINITION.evaluation.output_contract)


# Empty standard input must produce a diagnostic rather than an unproved answer.
def test_invalid_input(candidate: Path) -> None:
    stdout, stderr, exit_code = run_bench_utility(candidate, [], ROOT)
    assert stdout == b""
    assert stderr
    assert exit_code == 2


# Unsupported command arguments must fail before the solver executes.
def test_invalid_argument(candidate: Path) -> None:
    stdout, stderr, exit_code = run_bench_utility(candidate, ["--unknown"], ROOT, input_data=b"1\n")
    assert stdout == b""
    assert stderr
    assert exit_code == 2


# Local proof checks preserve the complete implementation and proof surface.
@pytest.mark.dafny_verify
@pytest.mark.parametrize(
    "filename", ["{{CLASS_NAME}}Core.dfy", "{{CLASS_NAME}}Proof.dfy", "{{CLASS_NAME}}.dfy"]
)
def test_verify_module(filename: str) -> None:
    run_dafny_verify(PROJECT / filename)
