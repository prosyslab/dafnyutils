"""Typed outcomes from standalone fuzzer evidence."""

import os
from pathlib import Path

from benchmarks.checks import OracleExecutionLocation
from evaluation.enums import CheckStatus
from evaluation.models import FuzzerOutcome
from evaluation.submission.oracles import (
    CheckCommand,
    FuzzingEvaluation,
    VerificationEvaluation,
)
from evaluation.submission.oracles import (
    TestcaseEvaluation as CaseEvaluation,
)
from evaluation.submission.output_adapters import parse_fuzzer_outcome
from evaluation.submission.runner import execute_evaluation
from evaluation.submission.session import EvaluationSession


# Missing time observations remain incomplete coverage in the typed command report.
def test_incomplete_time_coverage_marker_is_preserved() -> None:
    evidence = parse_fuzzer_outcome(
        name="fuzzer",
        stdout_bytes=b"",
        stderr_bytes=b"FUZZER_OUTCOME=incomplete_coverage\ntime evidence is incomplete\n",
        timed_out=False,
        exit_code=2,
    )

    assert evidence.outcome == FuzzerOutcome.INCOMPLETE_COVERAGE
    assert evidence.model_fields()["fuzzer_outcome"] == FuzzerOutcome.INCOMPLETE_COVERAGE


# Namespace setup evidence stays typed infrastructure rather than an inferred build failure.
def test_namespace_failure_marker_is_preserved() -> None:
    evidence = parse_fuzzer_outcome(
        name="fuzzer",
        stdout_bytes=b"",
        stderr_bytes=(
            b"FUZZER_OUTCOME=fuzzer_infrastructure_failure\n"
            b"Docker container startup failed: permission denied\n"
        ),
        timed_out=False,
        exit_code=2,
    )
    assert evidence.outcome == FuzzerOutcome.INFRASTRUCTURE_FAILURE
    assert evidence.model_fields()["fuzzer_outcome"] == FuzzerOutcome.INFRASTRUCTURE_FAILURE


# Ordinary marked build errors continue to classify as failures rather than infrastructure blockers.
def test_build_failure_marker_remains_build_failure() -> None:
    evidence = parse_fuzzer_outcome(
        name="fuzzer",
        stdout_bytes=b"",
        stderr_bytes=b"FUZZER_OUTCOME=fuzzer_build_failure\nCargo build failed\n",
        timed_out=False,
        exit_code=2,
    )
    assert evidence.outcome == FuzzerOutcome.BUILD_FAILURE


# An unmarked nonzero fuzzer invocation retains the existing conservative build-error fallback.
def test_unmarked_fuzzer_failure_keeps_existing_fallback() -> None:
    evidence = parse_fuzzer_outcome(
        name="fuzzer",
        stdout_bytes=b"",
        stderr_bytes=b"Cargo invocation failed\n",
        timed_out=False,
        exit_code=2,
    )
    assert evidence.outcome == FuzzerOutcome.BUILD_FAILURE


# Real fuzzer infrastructure evidence blocks the later verification process.
def test_logged_fuzzer_infrastructure_failure_blocks_remaining_checks(tmp_path: Path) -> None:
    session = EvaluationSession(tmp_path)
    marker = "FUZZER_OUTCOME=fuzzer_infrastructure_failure"
    plan = FuzzingEvaluation(
        ("fuzzer",),
        (
            CheckCommand(
                "fuzzer",
                f"printf '%s\\n' '{marker}' >&2\nexit 2",
                tmp_path,
                OracleExecutionLocation.TRUSTED_HOST,
            ),
        ),
        None,
    )
    report, blocked = execute_evaluation(
        plan=plan,
        session=session,
        env=dict(os.environ),
        blocked_reason=None,
        fail_fast=False,
    )
    assert report.status == CheckStatus.BLOCKED
    assert blocked is not None and "fuzzer infrastructure failure" in blocked
    assert len(session.executions) == 1
    assert session.executions[0].fuzzer_outcome == FuzzerOutcome.INFRASTRUCTURE_FAILURE
    assert session.executions[0].exit_code == 2
    verification = VerificationEvaluation(
        ("dafny_verify",),
        (
            CheckCommand(
                "dafny_verify",
                "touch unexpected-proof-execution",
                tmp_path,
                OracleExecutionLocation.EVALUATOR_CONTAINER,
            ),
        ),
        None,
    )
    verification_report, _ = execute_evaluation(
        plan=verification,
        session=session,
        env=dict(os.environ),
        blocked_reason=blocked,
        fail_fast=False,
    )
    assert verification_report.status == CheckStatus.BLOCKED
    assert not (tmp_path / "unexpected-proof-execution").exists()
    assert len(session.executions) == 1


# A real Cargo/build failure still fails fuzzing with candidate-failure semantics.
def test_logged_build_failure_remains_failed_fuzzing(tmp_path: Path) -> None:
    session = EvaluationSession(tmp_path)
    command = CheckCommand(
        "fuzzer",
        "printf '%s\\n' 'FUZZER_OUTCOME=fuzzer_build_failure' >&2\nexit 2",
        tmp_path,
        OracleExecutionLocation.TRUSTED_HOST,
    )
    plan = FuzzingEvaluation(("fuzzer",), (command,), None)
    report, blocked = execute_evaluation(
        plan=plan,
        session=session,
        env=dict(os.environ),
        blocked_reason=None,
        fail_fast=False,
    )
    assert report.status == CheckStatus.FAILED
    assert report.failed_checks == ["fuzzer"]
    assert blocked is None
    assert session.executions[0].fuzzer_outcome == FuzzerOutcome.BUILD_FAILURE


# A testcase failure remains failed when later fuzzing infrastructure becomes unavailable.
def test_prior_candidate_failure_remains_failed_with_later_infrastructure(tmp_path: Path) -> None:
    session = EvaluationSession(tmp_path)
    testcase = CaseEvaluation(
        ("implementation_tests",),
        (
            CheckCommand(
                "implementation_tests",
                "exit 1",
                tmp_path,
                OracleExecutionLocation.EVALUATOR_CONTAINER,
            ),
        ),
        None,
    )
    testcase_report, blocked = execute_evaluation(
        plan=testcase,
        session=session,
        env=dict(os.environ),
        blocked_reason=None,
        fail_fast=False,
    )
    fuzzing = FuzzingEvaluation(
        ("fuzzer",),
        (
            CheckCommand(
                "fuzzer",
                "printf '%s\\n' 'FUZZER_OUTCOME=fuzzer_infrastructure_failure' >&2\nexit 2",
                tmp_path,
                OracleExecutionLocation.TRUSTED_HOST,
            ),
        ),
        None,
    )
    fuzzing_report, blocked = execute_evaluation(
        plan=fuzzing,
        session=session,
        env=dict(os.environ),
        blocked_reason=blocked,
        fail_fast=False,
    )
    assert testcase_report.status == CheckStatus.FAILED
    assert testcase_report.failed_checks == ["implementation_tests"]
    assert fuzzing_report.status == CheckStatus.BLOCKED
    assert blocked == fuzzing_report.blocked_reason
    assert blocked is not None and "fuzzer infrastructure failure" in blocked
    assert len(session.executions) == 2
    assert session.executions[0].exit_code == 1
    assert session.executions[1].fuzzer_outcome == FuzzerOutcome.INFRASTRUCTURE_FAILURE
