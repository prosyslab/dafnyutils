from __future__ import annotations

from pathlib import Path

from benchmarks.paths import REPO_ROOT
from benchmarks.profiles import ResolvedBenchmark, benchmark_projects


def utility_config(utility_name: str) -> ResolvedBenchmark:
    return ResolvedBenchmark.for_task(utility_name)


def benchmark_utility_names(repository_root: Path = REPO_ROOT) -> tuple[str, ...]:
    return tuple(project.name for project in benchmark_projects(repository_root))


def benchmark_utility_configs() -> tuple[ResolvedBenchmark, ...]:
    return tuple(utility_config(name) for name in benchmark_utility_names())
