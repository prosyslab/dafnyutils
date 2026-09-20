"""Analyze Dafny entry points and derive the mandatory final specification obligation."""

from __future__ import annotations

from pathlib import Path
from typing import Any

from benchmarks.paths import REPO_ROOT
from benchmarks.profiles import (
    ResolvedBenchmark,
    coreutils_dafny_analysis_support_paths,
    is_algorithm_utility,
    utility_paths,
)
from entry_contract import DafnyEntry, EntryContractAnalysis, analyze_entry_contract


def dafny_analysis_support_paths(
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
    *,
    repository_root: Path | None = None,
) -> tuple[Path, ...]:
    """Return the complete support boundary used by task contract analysis."""
    repository_root = REPO_ROOT if repository_root is None else repository_root
    paths = utility_paths(utility_cfg, utility_name)
    return dafny_analysis_support_paths_for_entry(
        utility_name,
        support_source_paths=(
            paths["cli"],
            paths["schema"],
        ),
        repository_root=repository_root,
    )


def dafny_analysis_support_paths_for_entry(
    utility_name: str,
    *,
    support_source_paths: tuple[str, ...] = (),
    repository_root: Path | None = None,
) -> tuple[Path, ...]:
    """Resolve the support boundary from profile entry data."""
    repository_root = REPO_ROOT if repository_root is None else repository_root
    extra_paths = (
        ()
        if is_algorithm_utility(utility_name)
        else (*(repository_root / path for path in support_source_paths),)
    )
    return tuple(
        sorted(
            {
                *coreutils_dafny_analysis_support_paths(utility_name, repository_root),
                *extra_paths,
            }
        )
    )


def analyze_task_entry_contract(
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
    *,
    repository_root: Path | None = None,
) -> EntryContractAnalysis:
    """Analyze one task entry using the same support boundary as workspace generation."""
    repository_root = REPO_ROOT if repository_root is None else repository_root
    paths = utility_paths(utility_cfg, utility_name)
    execution = utility_cfg.task_profile.execution_entry
    return analyze_entry_contract(
        repository_root,
        repository_root / paths["utility_dir"],
        DafnyEntry(
            f"{paths['utility_dir']}/{execution.source_path}",
            execution.symbol,
        ),
        dafny_analysis_support_paths(
            utility_cfg,
            utility_name,
            repository_root=repository_root,
        ),
    )


def validate_final_specification_obligation(analysis: EntryContractAnalysis) -> None:
    principal_specs = tuple(
        entry.symbol for entry in analysis.manifest.spec_entries if entry.symbol.endswith(".Spec")
    )
    if len(principal_specs) != 1:
        raise ValueError(
            "task profile must identify exactly one principal specification entry named *.Spec"
        )
    principal_spec = principal_specs[0]
    if principal_spec not in analysis.execution.direct_postcondition_callees:
        raise ValueError(
            "RunCore must directly name the principal specification in a postcondition: "
            f"{principal_spec}"
        )


def dafny_entry_contract(
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
    *,
    analysis: EntryContractAnalysis | None = None,
) -> dict[str, Any]:
    paths = utility_paths(utility_cfg, utility_name)
    contract_analysis = analysis or analyze_task_entry_contract(utility_cfg, utility_name)
    manifest = contract_analysis.manifest
    return {
        "utility_dir": paths["utility_dir"],
        "execution_entry": manifest.execution_entry.model_dump(mode="json"),
        "spec_entries": [entry.model_dump(mode="json") for entry in manifest.spec_entries],
        "spec_definitions": [
            definition.model_dump(mode="json") for definition in manifest.spec_definitions
        ],
    }
