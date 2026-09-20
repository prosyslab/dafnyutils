"""Prepare implementation tasks and their isolated editable workspaces."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from benchmarks.paths import REPO_ROOT
from benchmarks.profiles import ResolvedBenchmark
from benchmarks.repository import BenchmarkRepository
from benchmarks.validation import load_validated_benchmark
from evaluation.task.preparation import TaskInputLayout, materialize_task_inputs
from evaluation.task.workspace import (
    TaskWorkspaceSpec,
    materialize_workspace_layout,
    task_workspace_spec,
)


@dataclass(frozen=True)
class PreparedCandidateTask:
    task_id: str
    run_directory: Path
    workspace: Path
    input_layout: TaskInputLayout
    workspace_spec: TaskWorkspaceSpec
    configuration: ResolvedBenchmark


def prepare_task(
    task_id: str,
    workspace: Path,
) -> PreparedCandidateTask:
    """Materialize a validated public task and its isolated editable workspace."""
    repository = BenchmarkRepository.open(REPO_ROOT)
    validated = load_validated_benchmark(repository, task_id)
    utility = validated.configuration
    run_directory = workspace.resolve()
    run_directory.mkdir(parents=True, exist_ok=True)
    if (run_directory / "task").exists() or (run_directory / "sandbox").exists():
        raise FileExistsError(f"task workspace already exists: {run_directory}")
    layout = materialize_task_inputs(
        run_dir=run_directory,
        utility_cfg=utility,
        utility_name=task_id,
        validated_profile=validated.profile,
    )
    spec = task_workspace_spec(
        utility_cfg=utility,
        utility_name=task_id,
        task=layout.prepared_task.profile,
        prepared_task=layout.prepared_task,
    )
    roots = materialize_workspace_layout(
        run_dir=run_directory,
        task_input_layout=layout,
        task_spec=spec,
    )
    return PreparedCandidateTask(
        task_id, run_directory, roots.workspace_root, layout, spec, utility
    )
