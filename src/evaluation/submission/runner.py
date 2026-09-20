"""Run layout, testcase, fuzzing, and verification checks in order."""

from dataclasses import dataclass
from pathlib import Path

from benchmarks.checks import OracleExecutionLocation
from benchmarks.paths import REPO_ROOT
from benchmarks.profiles import ResolvedBenchmark
from evaluation.models import (
    CheckReportModel,
    CommandResultModel,
    EvaluationResultsModel,
    FuzzerOutcome,
)
from evaluation.submission.oracle_environment import (
    configure_container_oracle_environment,
    configure_host_oracle_environment,
    containerized_evaluation,
)
from evaluation.submission.oracles import (
    EvaluationPlan,
    build_evaluations,
    derived_oracle_commands,
)
from evaluation.submission.sandbox import (
    SandboxContext,
    cleanup_evaluator_after_timeout,
    cleanup_fuzzer_container,
)
from evaluation.submission.scoring import build_check_report
from evaluation.submission.session import EvaluationSession
from evaluation.submission.workspace import evaluator_target_root


def evaluation_plans(
    configuration: ResolvedBenchmark,
    unavailable_checks: dict[str, str],
    *,
    public_task_id: str | None = None,
) -> tuple[EvaluationPlan, ...]:
    commands = derived_oracle_commands(configuration)
    if public_task_id is not None:
        commands = {
            name: command.replace("eval_support/", f"eval_support/{public_task_id}/")
            for name, command in commands.items()
        }
    for name, reason in unavailable_checks.items():
        if not reason.strip():
            raise ValueError(f"unavailable check requires a reason: {name}")
        commands.pop(name, None)
    return build_evaluations(
        utility_cfg=configuration,
        checkout_root=REPO_ROOT,
        oracle_commands=commands,
    )


def execute_evaluation(
    *,
    plan: EvaluationPlan,
    session: EvaluationSession,
    env: dict[str, str],
    host_env: dict[str, str] | None = None,
    evaluator_container_available: bool = False,
    blocked_reason: str | None,
    fail_fast: bool,
) -> tuple[CheckReportModel, str | None]:
    if not plan.required_checks:
        return build_check_report(plan=plan, executions=[]), blocked_reason

    effective_block = blocked_reason or plan.blocked_reason
    if effective_block is not None:
        return (
            build_check_report(plan=plan, executions=[], blocked_reason=effective_block),
            blocked_reason,
        )

    executions: list[CommandResultModel] = []
    next_block_reason = blocked_reason
    current_block_reason: str | None = None
    for command in plan.commands:
        result = session.run_logged(
            evaluation=plan.name,
            name=command.name,
            command=command.command,
            env=host_env
            if command.location is OracleExecutionLocation.TRUSTED_HOST and host_env is not None
            else env,
            timeout_sec=None,  # Checkers own limits; do not cap aggregate Dafny verification.
            cwd=command.cwd,
            infrastructure_report_containerized=(
                evaluator_container_available
                and command.location is OracleExecutionLocation.EVALUATOR_CONTAINER
            ),
        )
        executions.append(result)
        if result.infrastructure_failure_reason is not None:
            current_block_reason = (
                "candidate execution infrastructure failure: "
                + result.infrastructure_failure_reason
            )
        elif result.fuzzer_outcome is FuzzerOutcome.INFRASTRUCTURE_FAILURE:
            current_block_reason = (
                f"fuzzer infrastructure failure stopped {plan.name} check '{command.name}'"
            )
        if current_block_reason is not None:
            next_block_reason = current_block_reason
            session.note(current_block_reason)
            break
        if result.timed_out:
            session.note(f"timeout stopped remaining {plan.name} checks after '{command.name}'")
            break
        if fail_fast and not result.passed:
            next_block_reason = f"fail-fast stopped after {plan.name} check '{command.name}'"
            session.note(next_block_reason)
            break

    return (
        build_check_report(
            plan=plan,
            executions=executions,
            blocked_reason=current_block_reason,
        ),
        next_block_reason,
    )


@dataclass(frozen=True)
class EvaluationRun:
    executions: list[CommandResultModel]
    evaluations: EvaluationResultsModel
    notes: list[str]


def run_evaluations(
    *,
    run_directory: Path,
    plans: tuple[EvaluationPlan, ...],
    environment: dict[str, str],
    evaluator: SandboxContext | None,
    blocked_reason: str | None,
    fail_fast: bool,
    keep_sandbox: bool,
) -> EvaluationRun:
    session = EvaluationSession(run_directory)
    env = dict(environment)
    configure_container_oracle_environment(env)
    host_env = dict(environment)
    configure_host_oracle_environment(host_env, evaluator_target_root(run_directory))
    host_env["FUZZ_REPRO_DIR"] = str((run_directory / "evaluation/fuzzer-repros").resolve())
    blocked = blocked_reason
    reports: dict[str, CheckReportModel] = {}
    for plan in plans:
        execution_start = len(session.executions)
        was_unblocked = blocked is None and plan.blocked_reason is None
        try:
            reports[plan.name.value], blocked = execute_evaluation(
                plan=containerized_evaluation(plan, evaluator),
                session=session,
                env=env,
                host_env=host_env,
                evaluator_container_available=evaluator is not None,
                blocked_reason=blocked,
                fail_fast=fail_fast,
            )
        finally:
            if was_unblocked and any(
                command.location is OracleExecutionLocation.TRUSTED_HOST
                for command in plan.commands
            ):
                cleanup_fuzzer_container(host_env["FUZZ_CONTAINER_NAME"], host_env)
        if (
            evaluator is not None
            and not keep_sandbox
            and any(command.timed_out for command in session.executions[execution_start:])
        ):
            cleanup_evaluator_after_timeout(evaluator, environment)
    return EvaluationRun(
        session.executions,
        EvaluationResultsModel.model_validate(reports),
        session.notes,
    )
