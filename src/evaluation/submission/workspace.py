"""Restore trusted release inputs and overlay accepted archive files per task."""

import hashlib
import shutil
from dataclasses import replace
from pathlib import Path

from benchmarks.paths import REPO_ROOT
from evaluation.enums import CandidateOutputEntryType
from evaluation.models import (
    CandidateOutputCaptureResultModel,
    CandidateOutputRecordModel,
    CandidateOutputsCapturedEventModel,
)
from evaluation.outputs import overlay_candidate_outputs
from evaluation.runtime import append_jsonl, iso, utc_now
from evaluation.submission.archive import ReceivedSubmission
from evaluation.task.preparation import TaskInputLayout
from evaluation.task.release import PreparedReleaseTask, TaskReleaseManifest, released_task
from evaluation.task.workspace import (
    TaskWorkspaceSpec,
    WorkspaceRoots,
    _materialize_workspace_roots,
    workspace_roots,
)
from runtime.filesystem import copy_entry, remove_entry


def prepare_submission_workspace(
    *,
    manifest: TaskReleaseManifest,
    task_id: str,
    release_directory: Path,
    run_directory: Path,
    received: ReceivedSubmission | None,
    error: str | None,
) -> tuple[
    PreparedReleaseTask, CandidateOutputCaptureResultModel, list[CandidateOutputRecordModel]
]:
    target = evaluator_target_root(run_directory)
    shutil.copytree(release_directory / "workspace", target)
    # Reconstruct metadata before overlaying untrusted candidates.
    task = released_task(manifest, task_id, run_directory, target)
    records: list[CandidateOutputRecordModel] = []
    root = manifest.tasks[task_id].task_root
    if received is not None:
        for name in received.files:
            if not Path(name).is_relative_to(root) or name in manifest.fixed_files:
                continue
            source = received.workspace / name
            destination = target / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
            payload = source.read_bytes()
            records.append(
                CandidateOutputRecordModel(
                    path=name,
                    source=str(source),
                    captured=True,
                    entry_type=CandidateOutputEntryType.FILE,
                    stored_at=str(destination),
                    changed_from_baseline=hashlib.sha256(payload).hexdigest()
                    != manifest.files.get(name),
                    sha256=hashlib.sha256(payload).hexdigest(),
                    bytes=len(payload),
                )
            )
    restore_evaluator_owned_test(target, task.workspace_spec.utility_dir)
    capture = CandidateOutputCaptureResultModel(
        attempted=received is not None,
        copied=received is not None,
        captured_paths=[record.path for record in records],
        error=error,
    )
    task = replace(
        task,
        workspace_spec=replace(
            task.workspace_spec, sync_paths=tuple(Path(record.path) for record in records)
        ),
    )
    (run_directory / "evaluation").mkdir(parents=True, exist_ok=True)
    append_jsonl(
        run_directory / "evaluation/events.jsonl",
        CandidateOutputsCapturedEventModel(
            run_id=run_directory.name,
            captured_at=iso(utc_now()),
            count=len(records),
            outputs=records,
        ),
    )
    return task, capture, records


def evaluator_target_root(run_dir: Path) -> Path:
    return workspace_roots(run_dir).sandbox_root / "evaluator_target"


def prepare_evaluator_target(
    *,
    run_dir: Path,
    task_input_layout: TaskInputLayout,
    task_spec: TaskWorkspaceSpec,
    candidate_output_root: Path,
    candidate_output_records: list[CandidateOutputRecordModel],
) -> Path:
    base_roots = workspace_roots(run_dir)
    target_root = evaluator_target_root(run_dir)
    roots = WorkspaceRoots(
        sandbox_root=base_roots.sandbox_root,
        workspace_root=target_root,
        task_root=target_root / "task",
        run_root=base_roots.run_root,
        oracle_target_root=target_root,
        candidate_output_root=base_roots.candidate_output_root,
    )
    _materialize_workspace_roots(
        roots=roots,
        task_input_layout=task_input_layout,
        task_spec=task_spec,
        reset_sandbox=False,
    )
    overlay_candidate_outputs(
        candidate_output_root=candidate_output_root,
        evaluator_checkout_root=target_root,
        records=candidate_output_records,
    )
    restore_evaluator_owned_test(target_root, task_spec.utility_dir)
    return target_root


def restore_evaluator_owned_test(target_root: Path, utility_dir: Path) -> None:
    """Restore a trusted utility test only in the evaluator's private target."""
    # Tests are evaluator-owned even though the candidate may edit the utility directory.
    test_source = REPO_ROOT / utility_dir / "Tests.dfy"
    if test_source.is_file():
        trusted_test = target_root / utility_dir / "Tests.dfy"
        trusted_test.parent.mkdir(parents=True, exist_ok=True)
        remove_entry(trusted_test)
        copy_entry(test_source, trusted_test)
