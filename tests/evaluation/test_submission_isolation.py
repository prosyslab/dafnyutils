"""Archive evaluation outlives the candidate directory and candidate task objects."""

import hashlib
import shutil
import tarfile
from pathlib import Path

import pytest

import evaluation.submission.command_execution as command_execution
import evaluation.submission.runner as evaluation_runner
import evaluation.submission.sandbox as evaluator_sandbox
from evaluation.enums import CheckStatus
from evaluation.submission.api import CandidateEvaluationOptions, evaluate_submission
from evaluation.submission.sandbox import SandboxContext
from evaluation.task.release import prepare_release, publish_release


# Evaluation reconstructs candidate additions after deleting the entire original workspace.
def test_archive_evaluation_survives_candidate_deletion(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    release = tmp_path / "release"
    manifest = publish_release(("algorithm-1",), release)
    candidate = prepare_release(release, tmp_path / "candidate")
    helper = candidate.workspace / "bench/algorithm/1/helpers/Arithmetic.dfy"
    helper.parent.mkdir()
    helper.write_text("module Arithmetic {}", encoding="utf-8")
    archive = tmp_path / "submission.tar.gz"
    with tarfile.open(archive, "w:gz") as output:
        for task_root in manifest.task_roots:
            output.add(candidate.workspace / task_root, arcname=task_root)
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    shutil.rmtree(candidate.workspace)
    del candidate
    monkeypatch.setattr(
        command_execution, "run_command_capture_bytes", lambda *args, **kwargs: (False, 0, b"", b"")
    )
    result = evaluate_submission(
        archive,
        release_directory=release,
        run_directory=tmp_path / "evaluation",
        options=CandidateEvaluationOptions(evaluator=SandboxContext((), "test", "fake")),
    )
    assert result.error is None
    assert result.archive_sha256 == digest
    target = Path(result.tasks["algorithm-1"].evaluator_target_directory)
    assert (
        target / "bench/algorithm/1/helpers/Arithmetic.dfy"
    ).read_text() == "module Arithmetic {}"
    assert result.tasks["algorithm-1"].evaluations.verification.status is CheckStatus.FAILED
    assert not result.tasks["algorithm-1"].scores.overall_passed
    assert len(result.tasks["algorithm-1"].executions) == len(
        result.tasks["algorithm-1"].planned_checks
    )


# A failed host fuzzer leaves an auditable blocked result and triggers exact container cleanup.
def test_archive_fuzzer_failure_cleans_up_its_owned_container(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    release = tmp_path / "release"
    manifest = publish_release(("cat",), release)
    archive = tmp_path / "submission.tar.gz"
    with tarfile.open(archive, "w:gz") as output:
        for task_root in manifest.task_roots:
            output.add(release / "workspace" / task_root, arcname=task_root)
    cleanup: list[str] = []

    def controlled_capture(**kwargs):
        if "tools/coreutils_fuzzer/run.py" in kwargs["command"]:
            assert kwargs["env"]["FUZZ_REPRO_DIR"] == str(
                (tmp_path / "evaluation/tasks/cat/evaluation/fuzzer-repros").resolve()
            )
            return False, 2, b"", b"FUZZER_OUTCOME=fuzzer_infrastructure_failure\n"
        return False, 0, b"", b""

    monkeypatch.setattr(command_execution, "run_command_capture_bytes", controlled_capture)
    monkeypatch.setattr(
        evaluation_runner,
        "cleanup_fuzzer_container",
        lambda name, environment: cleanup.append(name),
    )
    result = evaluate_submission(
        archive,
        release_directory=release,
        run_directory=tmp_path / "evaluation",
        options=CandidateEvaluationOptions(evaluator=SandboxContext((), "test", "fake")),
    )

    task = result.tasks["cat"]
    assert task.evaluations.fuzzing.status is CheckStatus.BLOCKED
    assert [execution.name for execution in task.executions][-1] == "fuzzer"
    assert len(cleanup) == 1
    assert cleanup[0].startswith("dafnyutils-fuzzer-")


# Hidden utility tests return only in the evaluator target after a public archive is accepted.
def test_archive_evaluator_restores_trusted_utility_test(tmp_path: Path) -> None:
    release = tmp_path / "release"
    manifest = publish_release(("cat",), release)
    test_path = Path("bench/utils/cat/Tests.dfy")
    assert test_path.as_posix() not in manifest.files
    archive = tmp_path / "submission.tar.gz"
    with tarfile.open(archive, "w:gz") as output:
        for task_root in manifest.task_roots:
            output.add(release / "workspace" / task_root, arcname=task_root)

    result = evaluate_submission(
        archive,
        release_directory=release,
        run_directory=tmp_path / "evaluation",
        options=CandidateEvaluationOptions(blocked_reason="materialization-only check"),
    )

    target = Path(result.tasks["cat"].evaluator_target_directory)
    assert (target / test_path).is_file()
    assert not (release / "workspace" / test_path).exists()


# An interrupted host fuzzer still releases the one container owned by its run.
def test_archive_fuzzer_interruption_cleans_up_container(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    release = tmp_path / "release"
    manifest = publish_release(("cat",), release)
    archive = tmp_path / "submission.tar.gz"
    with tarfile.open(archive, "w:gz") as output:
        for task_root in manifest.task_roots:
            output.add(release / "workspace" / task_root, arcname=task_root)
    cleanup: list[str] = []

    def interrupted_capture(**kwargs):
        if "tools/coreutils_fuzzer/run.py" in kwargs["command"]:
            raise RuntimeError("host runner interrupted")
        return False, 0, b"", b""

    monkeypatch.setattr(command_execution, "run_command_capture_bytes", interrupted_capture)
    monkeypatch.setattr(
        evaluation_runner,
        "cleanup_fuzzer_container",
        lambda name, environment: cleanup.append(name),
    )
    with pytest.raises(RuntimeError, match="host runner interrupted"):
        evaluate_submission(
            archive,
            release_directory=release,
            run_directory=tmp_path / "evaluation",
            options=CandidateEvaluationOptions(evaluator=SandboxContext((), "test", "fake")),
        )

    assert len(cleanup) == 1
    assert cleanup[0].startswith("dafnyutils-fuzzer-")


# Missing submissions produce auditable blocked mandatory checks without starting Docker.
def test_missing_archive_reports_blocked_evaluation(tmp_path: Path) -> None:
    release = tmp_path / "release"
    publish_release(("algorithm-1",), release)
    result = evaluate_submission(
        tmp_path / "missing.tar.gz",
        release_directory=release,
        run_directory=tmp_path / "evaluation",
    )
    assert result.error and "regular archive" in result.error
    assert result.archive_sha256 is None
    assert result.tasks["algorithm-1"].executions == []
    assert result.tasks["algorithm-1"].candidate_capture.error == result.error
    assert result.tasks["algorithm-1"].evaluations.layout.status is CheckStatus.BLOCKED


# A corrupt archive retains its exact provenance while all task scores remain blocked.
def test_invalid_archive_retains_hash_and_blocked_result(tmp_path: Path) -> None:
    release = tmp_path / "release"
    publish_release(("algorithm-1",), release)
    archive = tmp_path / "submission.tar.gz"
    archive.write_bytes(b"invalid gzip")
    result = evaluate_submission(
        archive, release_directory=release, run_directory=tmp_path / "evaluation"
    )
    assert result.error and "invalid gzip" in result.error
    assert result.archive_sha256 == hashlib.sha256(archive.read_bytes()).hexdigest()
    assert not result.tasks["algorithm-1"].scores.overall_passed
    assert result.tasks["algorithm-1"].executions == []


# Missing Docker after archive acceptance preserves provenance and blocks every mandatory check.
def test_unavailable_docker_reports_blocked_evaluation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    release = tmp_path / "release"
    manifest = publish_release(("algorithm-1",), release)
    archive = tmp_path / "submission.tar.gz"
    with tarfile.open(archive, "w:gz") as output:
        output.add(release / "workspace" / manifest.task_roots[0], arcname=manifest.task_roots[0])
    monkeypatch.setattr(evaluator_sandbox, "docker_runtime_available", lambda: False)
    result = evaluate_submission(
        archive, release_directory=release, run_directory=tmp_path / "evaluation"
    )
    assert result.error and "Docker is unavailable" in result.error
    assert result.archive_sha256 == hashlib.sha256(archive.read_bytes()).hexdigest()
    task = result.tasks["algorithm-1"]
    assert task.candidate_capture.copied
    assert task.executions == []
    assert task.evaluations.layout.status is CheckStatus.BLOCKED
    assert task.evaluations.verification.status is CheckStatus.BLOCKED
    assert not task.scores.overall_passed
    assert (tmp_path / "evaluation/submission-evaluation.json").is_file()


# A single multi-task archive yields independent mandatory-check records for every task.
def test_multi_task_archive_preserves_per_task_results(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    release = tmp_path / "release"
    manifest = publish_release(("algorithm-1", "algorithm-4"), release)
    archive = tmp_path / "submission.tar.gz"
    with tarfile.open(archive, "w:gz") as output:
        for root in manifest.task_roots:
            output.add(release / "workspace" / root, arcname=root)
    monkeypatch.setattr(
        command_execution,
        "run_command_capture_bytes",
        lambda *args, **kwargs: (False, 0, b"", b""),
    )
    result = evaluate_submission(
        archive,
        release_directory=release,
        run_directory=tmp_path / "evaluation",
        options=CandidateEvaluationOptions(evaluator=SandboxContext((), "test", "fake")),
    )
    assert result.task_ids == manifest.task_ids
    assert tuple(result.tasks) == manifest.task_ids
    for task_id, task in result.tasks.items():
        assert task.task_id == task_id
        assert len(task.executions) == len(task.planned_checks)
        assert task.evaluations.verification.status is CheckStatus.FAILED
        assert not task.scores.overall_passed
