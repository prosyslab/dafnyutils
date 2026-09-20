"""Audit the configured coreutils implementation/spec entry boundary."""

from pathlib import Path

import pytest

from benchmarks.profiles import (
    ResolvedBenchmark,
    coreutils_dafny_analysis_support_paths,
)
from entry_contract import DafnyEntry, analyze_entry_contract
from tests.evaluation.evaluation_test_support import benchmark_utility_configs
from tools.bench.bench_test_support import evaluation_target_root

ROOT = evaluation_target_root(Path(__file__).resolve().parents[2])
COREUTILS = [
    utility for utility in benchmark_utility_configs() if not utility.name.startswith("algorithm-")
]


# Every coreutils contract must derive all specification roots from its configured RunCore.
@pytest.mark.parametrize("utility", COREUTILS, ids=lambda utility: utility.name)
def test_coreutils_run_core_directly_names_configured_spec(
    utility: ResolvedBenchmark,
) -> None:
    profile = utility.task_profile
    execution_path = f"{utility.utility_dir}/{profile.execution_entry.source_path}"
    analysis = analyze_entry_contract(
        ROOT,
        ROOT / utility.utility_dir,
        DafnyEntry(execution_path, profile.execution_entry.symbol),
        support_source_paths=coreutils_dafny_analysis_support_paths(
            utility.name,
            ROOT,
        ),
    )

    execution = analysis.execution
    expected = tuple(
        sorted(
            set(execution.direct_precondition_callees) | set(execution.direct_postcondition_callees)
        )
    )
    assert tuple(entry.symbol for entry in analysis.manifest.spec_entries) == expected
