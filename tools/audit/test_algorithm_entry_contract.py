"""Audit the configured algorithm implementation/spec entry boundary."""

from pathlib import Path

import pytest

from entry_contract import DafnyEntry, analyze_entry_contract
from tests.evaluation.evaluation_test_support import benchmark_utility_configs
from tools.bench.bench_test_support import evaluation_target_root

ROOT = evaluation_target_root(Path(__file__).resolve().parents[2])
ALGORITHMS = [
    utility for utility in benchmark_utility_configs() if utility.name.startswith("algorithm-")
]


# Every algorithm contract derives precondition and postcondition roots from RunCore.
@pytest.mark.parametrize("utility", ALGORITHMS, ids=lambda utility: utility.name)
def test_algorithm_run_core_directly_names_configured_spec(utility: object) -> None:
    profile = utility.task_profile
    execution_path = f"{utility.utility_dir}/{profile.execution_entry.source_path}"
    analysis = analyze_entry_contract(
        ROOT,
        ROOT / utility.utility_dir,
        DafnyEntry(execution_path, profile.execution_entry.symbol),
    )

    execution = analysis.execution
    expected = tuple(
        sorted(
            set(execution.direct_precondition_callees) | set(execution.direct_postcondition_callees)
        )
    )
    assert tuple(entry.symbol for entry in analysis.manifest.spec_entries) == expected


# Algorithm specifications must remain independent from their implementation core.
@pytest.mark.parametrize("utility", ALGORITHMS, ids=lambda utility: utility.name)
def test_algorithm_specification_does_not_depend_on_core(utility: object) -> None:
    profile = utility.task_profile
    execution_path = f"{utility.utility_dir}/{profile.execution_entry.source_path}"
    analysis = analyze_entry_contract(
        ROOT,
        ROOT / utility.utility_dir,
        DafnyEntry(execution_path, profile.execution_entry.symbol),
    )

    core_path = f"{utility.utility_dir}/Core.dfy"
    specification_paths = {
        definition.source_path for definition in analysis.manifest.spec_definitions
    }
    assert core_path not in specification_paths
