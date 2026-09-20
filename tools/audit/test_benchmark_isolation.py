from __future__ import annotations

from pathlib import Path

import pytest

from analysis.client import (
    definition_analysis_infos_from_paths,
    definition_analysis_infos_from_stdin,
)
from benchmarks.profiles import utility_paths
from tests.evaluation.evaluation_test_support import benchmark_utility_configs

ROOT = Path(__file__).resolve().parents[2]
UTILITIES = benchmark_utility_configs()


def _utility_id(utility: object) -> str:
    return str(getattr(utility, "name"))


# Direct Dafny includes stay inside the benchmark item or the shared core.
@pytest.mark.parametrize("utility", UTILITIES, ids=_utility_id)
def test_benchmark_item_dafny_includes_stay_isolated(utility: object) -> None:
    name = _utility_id(utility)
    utility_dir = (ROOT / utility_paths(utility, name)["utility_dir"]).resolve()
    core_dir = (ROOT / "bench/core").resolve()
    violations: list[str] = []
    sources = tuple(utility_dir.rglob("*.dfy"))
    definitions = definition_analysis_infos_from_paths(sources, spans_only=True)
    analyzed_sources = {Path(definition.source_path).resolve() for definition in definitions}
    missing_sources = set(sources) - analyzed_sources
    missing_source_includes: set[tuple[Path, Path]] = set()
    for source in sorted(missing_sources):
        source_definitions = definition_analysis_infos_from_stdin(
            source.read_text(encoding="utf-8")
            + "\nmodule BenchmarkIsolationAuditSentinel {\n"
            + "  predicate Marker() { true }\n"
            + "}\n",
            source_dir=source.parent,
            spans_only=True,
        )
        missing_source_includes.update(
            (source, Path(include.target_path).resolve())
            for definition in source_definitions
            for include in definition.local_includes
        )
    includes = {
        (Path(include.source_path).resolve(), Path(include.target_path).resolve())
        for definition in definitions
        for include in definition.local_includes
    } | missing_source_includes

    for source, target in sorted(includes):
        if not source.is_relative_to(utility_dir):
            continue
        if not target.is_relative_to(utility_dir) and not target.is_relative_to(core_dir):
            violations.append(f"{source.relative_to(ROOT)} includes {target.relative_to(ROOT)}")

    assert not violations, "\n".join(violations)
