"""Build reports from parsed command evidence for the four evaluations."""

from __future__ import annotations

from evaluation.enums import CheckStatus
from evaluation.models import (
    CheckReportModel,
    CommandResultModel,
    EvaluationResultsModel,
    FuzzerOutcome,
    ScoresModel,
)
from evaluation.submission.oracles import EvaluationPlan


def build_check_report(
    *,
    plan: EvaluationPlan,
    executions: list[CommandResultModel],
    blocked_reason: str | None = None,
) -> CheckReportModel:
    if not plan.required_checks:
        return CheckReportModel(
            applicable=False,
            status=CheckStatus.NOT_APPLICABLE,
            required_checks=[],
            passed_checks=[],
            failed_checks=[],
        )

    completed = [
        result
        for result in executions
        if result.check_failure_observed
        or (
            result.infrastructure_failure_reason is None
            and result.fuzzer_outcome is not FuzzerOutcome.INFRASTRUCTURE_FAILURE
        )
    ]
    passed = [result.name for result in completed if result.passed]
    failed = [result.name for result in completed if not result.passed]
    if failed:
        status = CheckStatus.FAILED
    elif blocked_reason or plan.blocked_reason or len(passed) != len(plan.required_checks):
        status = CheckStatus.BLOCKED
    else:
        status = CheckStatus.PASSED
    reason = blocked_reason or plan.blocked_reason
    if status is CheckStatus.BLOCKED and reason is None:
        reason = "evaluation did not execute the required checks"
    return CheckReportModel(
        applicable=True,
        status=status,
        required_checks=list(plan.required_checks),
        passed_checks=passed,
        failed_checks=failed,
        blocked_reason=reason,
    )


def build_scores_model(
    *,
    evaluations: EvaluationResultsModel,
    total_commands: int,
    passed_commands: int,
) -> ScoresModel:
    layout = evaluations.layout.status is CheckStatus.PASSED
    testcase = evaluations.testcase.status is CheckStatus.PASSED
    fuzzing = (
        evaluations.fuzzing.status is CheckStatus.PASSED if evaluations.fuzzing.applicable else None
    )
    verification = evaluations.verification.status is CheckStatus.PASSED
    return ScoresModel(
        overall_passed=layout and testcase and fuzzing is not False and verification,
        layout_passed=layout,
        testcase_passed=testcase,
        fuzzing_passed=fuzzing,
        verification_passed=verification,
        total_commands=total_commands,
        passed_commands=passed_commands,
    )
