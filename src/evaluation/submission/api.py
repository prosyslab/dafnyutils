"""Public acceptance and evaluation of candidate submissions.

The benchmark accepts public task identifiers and filesystem submissions. Harness
selection, authentication, retries, and experiment reports belong to its caller.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from enum import StrEnum
from pathlib import Path

from pydantic import Field

from evaluation.models import (
    CandidateOutputCaptureResultModel,
    CandidateOutputRecordModel,
    CheckPlanEntryModel,
    CommandResultModel,
    EvaluationResultsModel,
    ScoresModel,
    StrictModel,
)
from evaluation.submission.archive import (
    ArchiveProvenance,
    ReceivedSubmission,
    SubmissionError,
    receive_submission,
)
from evaluation.submission.oracles import EvaluationPlan
from evaluation.submission.runner import evaluation_plans, run_evaluations
from evaluation.submission.sandbox import (
    EvaluatorUnavailableError,
    SandboxContext,
    evaluator_scope,
)
from evaluation.submission.scoring import build_scores_model
from evaluation.submission.workspace import (
    evaluator_target_root,
    prepare_submission_workspace,
)
from evaluation.task.api import PreparedCandidateTask
from evaluation.task.release import PreparedReleaseTask, load_release
from runtime.json_io import write_json


@dataclass(frozen=True)
class CandidateEvaluationOptions:
    environment: dict[str, str] = field(default_factory=dict)
    evaluator_image: str = "dafnyutils-evaluation:latest"
    evaluator: SandboxContext | None = None
    fail_fast: bool = False
    keep_sandbox: bool = False
    blocked_reason: str | None = None
    unavailable_checks: dict[str, str] = field(default_factory=dict)


class CandidateEvaluationSchemaVersion(StrEnum):
    V2 = "benchmark.candidate-evaluation.v2"


class CandidateEvaluationResult(StrictModel):
    schema_version: CandidateEvaluationSchemaVersion = CandidateEvaluationSchemaVersion.V2
    task_id: str
    events_path: str
    evaluator_target_directory: str
    planned_checks: list[CheckPlanEntryModel]
    candidate_capture: CandidateOutputCaptureResultModel
    candidate_outputs: list[CandidateOutputRecordModel]
    executions: list[CommandResultModel]
    evaluations: EvaluationResultsModel
    scores: ScoresModel
    notes: list[str] = Field(default_factory=list)


def candidate_check_plan(
    task: PreparedCandidateTask | PreparedReleaseTask,
) -> list[CheckPlanEntryModel]:
    """Return the benchmark-owned mandatory command plan for reporting only."""
    return [
        CheckPlanEntryModel(
            evaluation=plan.name,
            name=command.name,
            command=command.command,
            cwd=str(command.cwd),
        )
        for plan in _evaluation_plans(task, {})
        for command in plan.commands
    ]


def _evaluation_plans(
    task: PreparedCandidateTask | PreparedReleaseTask,
    unavailable_checks: dict[str, str],
) -> tuple[EvaluationPlan, ...]:
    return evaluation_plans(
        task.configuration,
        unavailable_checks,
        public_task_id=task.task_id if isinstance(task, PreparedReleaseTask) else None,
    )


def _evaluate_captured(
    task: PreparedCandidateTask | PreparedReleaseTask,
    options: CandidateEvaluationOptions,
    capture: CandidateOutputCaptureResultModel,
    records: list[CandidateOutputRecordModel],
    evaluator: SandboxContext | None,
) -> CandidateEvaluationResult:
    run = run_evaluations(
        run_directory=task.run_directory,
        plans=_evaluation_plans(task, options.unavailable_checks),
        environment=options.environment,
        evaluator=evaluator,
        blocked_reason=options.blocked_reason or capture.error,
        fail_fast=options.fail_fast,
        keep_sandbox=options.keep_sandbox,
    )
    executions = run.executions
    result = CandidateEvaluationResult(
        task_id=task.task_id,
        events_path=str(task.run_directory / "evaluation/events.jsonl"),
        evaluator_target_directory=str(evaluator_target_root(task.run_directory)),
        planned_checks=candidate_check_plan(task),
        candidate_capture=capture,
        candidate_outputs=records,
        executions=executions,
        evaluations=run.evaluations,
        scores=build_scores_model(
            evaluations=run.evaluations,
            total_commands=len(executions),
            passed_commands=sum(command.passed for command in executions),
        ),
        notes=[
            *run.notes,
            *(
                [options.blocked_reason]
                if options.blocked_reason and options.blocked_reason != capture.error
                else []
            ),
            *([capture.error] if capture.error else []),
            *(f"{name}: {reason}" for name, reason in options.unavailable_checks.items()),
        ],
    )
    write_json(task.run_directory / "evaluation.json", result.model_dump(mode="json"))
    return result


class SubmissionEvaluationSchemaVersion(StrEnum):
    V2 = "benchmark.submission-evaluation.v2"


class SubmissionEvaluationResult(StrictModel):
    schema_version: SubmissionEvaluationSchemaVersion = SubmissionEvaluationSchemaVersion.V2
    task_ids: tuple[str, ...]
    archive_sha256: str | None
    archive_bytes: int | None
    archive_path: str | None
    release_id: str
    tasks: dict[str, CandidateEvaluationResult]
    error: str | None = None


def evaluate_submission(
    archive: Path,
    *,
    release_directory: Path,
    run_directory: Path,
    options: CandidateEvaluationOptions | None = None,
) -> SubmissionEvaluationResult:
    """Independently evaluate the exact archive using server-owned public inputs.

    The caller supplies neither a candidate directory nor a prepared task. Each
    task gets a fresh target and an evaluator container with the existing mandatory
    benchmark checks. Extra candidate files remain in their released task root.
    """
    if run_directory.exists():
        raise FileExistsError(f"evaluation run already exists: {run_directory}")
    manifest = load_release(release_directory)
    options = options or CandidateEvaluationOptions()
    received = None
    error = None
    try:
        received = receive_submission(archive, manifest=manifest, run_directory=run_directory)
    except (SubmissionError, OSError) as exc:
        error = f"submission rejected: {exc}"
        if options.blocked_reason:
            error = f"{options.blocked_reason}; {error}"
        options = replace(options, blocked_reason=error)
    archive_path = run_directory / "submission.tar.gz"
    archive_sha256, archive_bytes = _archive_provenance(
        received, run_directory / "archive-provenance.json"
    )
    results: dict[str, CandidateEvaluationResult] = {}
    for task_id in manifest.task_ids:
        task_run = run_directory / "tasks" / task_id
        task, capture, records = prepare_submission_workspace(
            manifest=manifest,
            task_id=task_id,
            release_directory=release_directory,
            run_directory=task_run,
            received=received,
            error=error,
        )
        if options.blocked_reason:
            results[task_id] = _evaluate_captured(task, options, capture, records, None)
        elif options.evaluator is not None:
            results[task_id] = _evaluate_captured(
                task, options, capture, records, options.evaluator
            )
        else:
            result, infrastructure_error = _evaluate_in_new_sandbox(
                task, options, capture, records, evaluator_target_root(task_run)
            )
            results[task_id] = result
            error = error or infrastructure_error
    result = SubmissionEvaluationResult(
        task_ids=manifest.task_ids,
        archive_sha256=archive_sha256,
        archive_bytes=archive_bytes,
        archive_path=str(archive_path) if archive_sha256 is not None else None,
        release_id=manifest.release_id,
        tasks=results,
        error=error,
    )
    write_json(run_directory / "submission-evaluation.json", result.model_dump(mode="json"))
    return result


def _evaluate_in_new_sandbox(
    task: PreparedReleaseTask,
    options: CandidateEvaluationOptions,
    capture: CandidateOutputCaptureResultModel,
    records: list[CandidateOutputRecordModel],
    target: Path,
) -> tuple[CandidateEvaluationResult, str | None]:
    try:
        with evaluator_scope(
            run_directory=task.run_directory,
            env=options.environment,
            evaluator_target_dir=target,
            evaluator_image=options.evaluator_image,
        ) as evaluator:
            return _evaluate_captured(task, options, capture, records, evaluator), None
    except EvaluatorUnavailableError as exc:
        error = f"evaluator unavailable: {exc}"
        blocked_options = replace(options, blocked_reason=error)
        result = _evaluate_captured(task, blocked_options, capture, records, None)
        return result, error


def _archive_provenance(
    received: ReceivedSubmission | None, metadata: Path
) -> tuple[str | None, int | None]:
    if received is not None:
        return received.archive_sha256, received.archive_bytes
    if metadata.is_file():
        provenance = ArchiveProvenance.from_json_file(metadata)
        return provenance.archive_sha256, provenance.archive_bytes
    return None, None
