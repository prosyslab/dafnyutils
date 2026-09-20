"""Public task preparation and archive evaluation without agent configuration."""

import json
import tarfile
from pathlib import Path

import pytest

import benchmarks.generated_profile as generated_profile
import evaluation.submission.command_execution as command_execution
import evaluation.task.api as task_api
from benchmarks.checks import EvaluationName
from benchmarks.task import TaskProfile
from evaluation.enums import CheckStatus
from evaluation.submission.api import (
    CandidateEvaluationOptions,
    CandidateEvaluationResult,
    CandidateEvaluationSchemaVersion,
    candidate_check_plan,
    evaluate_submission,
)
from evaluation.submission.sandbox import SandboxContext
from evaluation.task.api import prepare_task
from evaluation.task.release import PreparedRelease, prepare_release, publish_release


def _archive_candidate(candidate: PreparedRelease, path: Path) -> Path:
    with tarfile.open(path, "w:gz") as archive:
        for root in candidate.manifest.task_roots:
            archive.add(candidate.workspace / root, arcname=root)
    return path


# Preparing an algorithm analyzes its sources once and hides evaluator-only cases.
def test_prepare_task_materializes_public_algorithm_workspace(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    analyses = []
    analyze = generated_profile.analyze_task_entry_contract

    def record_analysis(*args, **kwargs):
        result = analyze(*args, **kwargs)
        analyses.append(result)
        return result

    monkeypatch.setattr(generated_profile, "analyze_task_entry_contract", record_analysis)
    task = prepare_task("algorithm-1", tmp_path / "candidate")

    public_task = TaskProfile.from_json_file(task.input_layout.task_path)
    assert public_task.task_id == "algorithm-1"
    assert len(analyses) == 1
    assert task.input_layout.prepared_task.entry_analysis is analyses[0]
    assert task.workspace.is_dir()
    assert not (task.workspace / "bench/algorithm/1/cases.json").exists()
    assert all((task.workspace / path).exists() for path in public_task.workspace.editable_paths)


# Editing a supplied specification blocks archive evaluation before any oracle command runs.
def test_submission_blocks_modified_public_specification(tmp_path: Path) -> None:
    release = tmp_path / "release"
    publish_release(("algorithm-1",), release)
    candidate = prepare_release(release, tmp_path / "candidate")
    protected = candidate.workspace / "bench/algorithm/1/Spec.dfy"
    protected.chmod(0o644)
    protected.write_text(protected.read_text(encoding="utf-8") + "\n// changed\n", encoding="utf-8")
    archive = _archive_candidate(candidate, tmp_path / "submission.tar.gz")

    result = evaluate_submission(
        archive,
        release_directory=release,
        run_directory=tmp_path / "run",
        options=CandidateEvaluationOptions(evaluator=SandboxContext((), "test", "test-evaluator")),
    ).tasks["algorithm-1"]

    assert result.candidate_capture.error is not None
    assert not result.scores.overall_passed
    assert result.evaluations.layout.status is CheckStatus.BLOCKED
    assert result.executions == []
    saved = CandidateEvaluationResult.model_validate_json(
        (tmp_path / "run/tasks/algorithm-1/evaluation.json").read_text(encoding="utf-8")
    )
    assert saved == result


# A successful process without verifier evidence still fails verification.
def test_submission_requires_verifier_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    release = tmp_path / "release"
    publish_release(("algorithm-1",), release)
    candidate = prepare_release(release, tmp_path / "candidate")
    archive = _archive_candidate(candidate, tmp_path / "submission.tar.gz")
    transported_commands = []
    agent_events = candidate.workspace / "events.jsonl"
    agent_events.write_text('{"event":"command_started","sequence_id":1}\n', encoding="utf-8")

    def successful_transport(command, **kwargs):
        transported_commands.append(command)
        return False, 0, b"", b""

    monkeypatch.setattr(command_execution, "run_command_capture_bytes", successful_transport)
    result = evaluate_submission(
        archive,
        release_directory=release,
        run_directory=tmp_path / "run",
        options=CandidateEvaluationOptions(evaluator=SandboxContext((), "test", "fake")),
    ).tasks["algorithm-1"]

    assert result.evaluations.layout.status is CheckStatus.PASSED
    assert result.evaluations.testcase.status is CheckStatus.PASSED
    assert result.evaluations.fuzzing.status is CheckStatus.NOT_APPLICABLE
    assert result.evaluations.verification.status is CheckStatus.FAILED
    assert result.evaluations.verification.failed_checks == ["dafny_verify"]
    assert not result.scores.overall_passed
    assert result.scores.fuzzing_passed is None
    plan = candidate_check_plan(candidate.tasks["algorithm-1"])
    assert len(result.executions) == len(transported_commands) == len(plan)
    assert {command.name for command in result.executions} == {command.name for command in plan}
    assert Path(result.events_path) != agent_events
    assert agent_events.read_text(encoding="utf-8") == (
        '{"event":"command_started","sequence_id":1}\n'
    )
    evaluation_events = [
        json.loads(line)
        for line in Path(result.events_path).read_text(encoding="utf-8").splitlines()
    ]
    starts = [event for event in evaluation_events if event["event"] == "command_started"]
    assert [event["sequence_id"] for event in starts] == list(range(1, len(starts) + 1))
    assert [event["evaluation"] for event in starts] == [
        "layout",
        "layout",
        "testcase",
        "verification",
    ]


# Valid verifier evidence makes every applicable algorithm evaluation pass and persist.
def test_submission_persists_four_evaluation_results(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    release = tmp_path / "release"
    publish_release(("algorithm-1",), release)
    candidate = prepare_release(release, tmp_path / "candidate")
    archive = _archive_candidate(candidate, tmp_path / "submission.tar.gz")

    def successful_transport(command, **kwargs):
        if "eval_support/algorithm-1/verify.sh" in command:
            return (
                False,
                0,
                b"DAFNY_VERIFICATION_OUTCOME=verified phase=verify\n"
                b"DAFNY_VERIFICATION_RESULT total=1 failed=0\n",
                b"",
            )
        return False, 0, b"", b""

    monkeypatch.setattr(command_execution, "run_command_capture_bytes", successful_transport)
    result = evaluate_submission(
        archive,
        release_directory=release,
        run_directory=tmp_path / "run",
        options=CandidateEvaluationOptions(evaluator=SandboxContext((), "test", "fake")),
    ).tasks["algorithm-1"]

    assert result.schema_version is CandidateEvaluationSchemaVersion.V2
    assert result.scores.overall_passed
    assert result.scores.layout_passed
    assert result.scores.testcase_passed
    assert result.scores.fuzzing_passed is None
    assert result.scores.verification_passed
    assert result.evaluations.fuzzing.status is CheckStatus.NOT_APPLICABLE
    assert [check.evaluation for check in result.planned_checks] == [
        EvaluationName.LAYOUT,
        EvaluationName.LAYOUT,
        EvaluationName.TESTCASE,
        EvaluationName.VERIFICATION,
    ]
    saved = CandidateEvaluationResult.model_validate_json(
        (tmp_path / "run/tasks/algorithm-1/evaluation.json").read_text(encoding="utf-8")
    )
    assert saved == result


# Fail-fast stops after the first failed layout process and blocks later evaluations.
def test_submission_fail_fast_blocks_remaining_evaluations(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    release = tmp_path / "release"
    publish_release(("algorithm-1",), release)
    candidate = prepare_release(release, tmp_path / "candidate")
    archive = _archive_candidate(candidate, tmp_path / "submission.tar.gz")
    invoked: list[str] = []

    def failed_layout(command, **kwargs):
        invoked.append(command)
        return False, 1, b"", b"layout failed"

    monkeypatch.setattr(command_execution, "run_command_capture_bytes", failed_layout)
    result = evaluate_submission(
        archive,
        release_directory=release,
        run_directory=tmp_path / "run",
        options=CandidateEvaluationOptions(
            evaluator=SandboxContext((), "test", "fake"),
            fail_fast=True,
        ),
    ).tasks["algorithm-1"]

    assert len(invoked) == 1
    assert [command.name for command in result.executions] == ["impl_layout"]
    assert result.evaluations.layout.status is CheckStatus.FAILED
    assert result.evaluations.testcase.status is CheckStatus.BLOCKED
    assert result.evaluations.verification.status is CheckStatus.BLOCKED
    assert not result.scores.overall_passed


# Unavailable mandatory checks stay required and block scoring instead of disappearing.
def test_submission_blocks_unavailable_mandatory_checks(tmp_path: Path) -> None:
    release = tmp_path / "release"
    publish_release(("algorithm-1",), release)
    candidate = prepare_release(release, tmp_path / "candidate")
    archive = _archive_candidate(candidate, tmp_path / "submission.tar.gz")
    required = {command.name for command in candidate_check_plan(candidate.tasks["algorithm-1"])}

    result = evaluate_submission(
        archive,
        release_directory=release,
        run_directory=tmp_path / "run",
        options=CandidateEvaluationOptions(
            evaluator=SandboxContext((), "test", "unused-transport"),
            unavailable_checks={name: "controlled unavailable tool" for name in required},
        ),
    ).tasks["algorithm-1"]

    assert result.executions == []
    assert not result.scores.overall_passed
    assert result.evaluations.layout.status is CheckStatus.BLOCKED
    assert result.evaluations.verification.status is CheckStatus.BLOCKED
    assert {command.name for command in result.planned_checks} == required


# An unregistered task cannot be prepared without a benchmark definition.
def test_prepare_task_rejects_unregistered_definition(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repository = tmp_path / "repository"
    (repository / "bench").mkdir(parents=True)
    monkeypatch.setattr(task_api, "REPO_ROOT", repository)

    with pytest.raises(ValueError, match="algorithm-1"):
        prepare_task("algorithm-1", tmp_path / "candidate")

    assert not (tmp_path / "candidate").exists()
