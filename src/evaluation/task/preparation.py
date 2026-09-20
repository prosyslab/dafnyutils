"""Materialize generated task resources and retain source snapshots for later freshness checks."""

from __future__ import annotations

import shutil
from dataclasses import dataclass
from pathlib import Path

from benchmarks.generated_profile import GeneratedTaskProfile
from benchmarks.paths import REPO_ROOT
from benchmarks.profiles import ResolvedBenchmark, utility_paths
from benchmarks.task import TaskProfile
from entry_contract import (
    EntryContractAnalysis,
    EntryContractSourceSnapshot,
    entry_contract_source_snapshot,
)
from runtime.filesystem import remove_entry

TASK_FILENAME = "task.json"


@dataclass(frozen=True)
class TaskInputLayout:
    task_dir: Path
    task_path: Path
    visible_artifacts: dict[str, Path]
    prepared_task: "PreparedTask"


@dataclass(frozen=True)
class PreparedTask:
    """Immutable task inputs and the baseline contract analysis that produced them."""

    validated_profile: GeneratedTaskProfile
    source_snapshot: EntryContractSourceSnapshot

    def validate_source_identity(self, *, repository_root: Path | None = None) -> None:
        """Reject use after any baseline source consumed by the analysis changes."""
        repository_root = REPO_ROOT if repository_root is None else repository_root
        current = entry_contract_source_snapshot(
            repository_root,
            repository_root / self.profile.dafny.utility_root,
            self.entry_analysis.manifest,
            additional_sources=self.entry_analysis.analysis_sources,
        )
        if current != self.source_snapshot:
            raise ValueError("prepared task source snapshot changed")

    @property
    def profile(self) -> TaskProfile:
        return self.validated_profile.profile

    @property
    def entry_analysis(self) -> EntryContractAnalysis:
        return self.validated_profile.entry_analysis


def prepare_task(
    *,
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
    validated_profile: GeneratedTaskProfile,
) -> PreparedTask:
    utility_root = Path(utility_paths(utility_cfg, utility_name)["utility_dir"])
    validated = validated_profile
    if validated.profile.task_id != utility_name:
        raise ValueError("generated task profile id does not match workspace utility")
    if Path(validated.profile.dafny.utility_root) != utility_root:
        raise ValueError("generated task profile root does not match workspace utility")
    source_snapshot = entry_contract_source_snapshot(
        REPO_ROOT,
        REPO_ROOT / utility_root,
        validated.entry_analysis.manifest,
        additional_sources=validated.entry_analysis.analysis_sources,
    )

    return PreparedTask(
        validated_profile=validated,
        source_snapshot=source_snapshot,
    )


def materialize_task_inputs(
    *,
    run_dir: Path,
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
    validated_profile: GeneratedTaskProfile,
) -> TaskInputLayout:
    prepared_task = prepare_task(
        utility_cfg=utility_cfg,
        utility_name=utility_name,
        validated_profile=validated_profile,
    )
    task_dir = run_dir / "task"
    remove_entry(task_dir)
    task_dir.mkdir(parents=True, exist_ok=False)
    task_path = task_dir / TASK_FILENAME
    visible_artifacts = _copy_task_resources(
        task=prepared_task.profile,
        repository_root=REPO_ROOT,
        task_dir=task_dir,
    )
    prepared_task.profile.to_json_file(task_path)
    return TaskInputLayout(
        task_dir=task_dir,
        task_path=task_path,
        visible_artifacts=visible_artifacts,
        prepared_task=prepared_task,
    )


def _copy_task_resources(
    *,
    task: TaskProfile,
    repository_root: Path,
    task_dir: Path,
) -> dict[str, Path]:
    copied: dict[str, Path] = {}
    for resource in task.resources:
        source = repository_root / resource.path
        target = task_dir / resource.path
        if target == task_dir / TASK_FILENAME:
            raise ValueError("task resource path collides with task.json")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
        copied[resource.resource_id] = target
    return copied
