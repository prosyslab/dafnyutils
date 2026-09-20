"""Build the four benchmark-owned evaluations from required oracle commands."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import ClassVar

from benchmarks.checks import (
    EvaluationName,
    OracleExecutionLocation,
    location_for_check,
    required_checks_for_evaluation,
)
from benchmarks.profiles import (
    ResolvedBenchmark,
    _algorithm_id,
    is_algorithm_utility,
    required_checks_for_task,
    utility_paths,
)
from evaluation.environment import EVAL_BENCH_BUILD_SCRIPT_ENV, EVAL_BENCH_DLL_ENV
from evaluation.runtime import DAFNY_VERIFY_DOTNET_HEAP_LIMIT
from standard_library import DAFNY_STANDARD_LIBRARY_OPTION


@dataclass(frozen=True)
class CheckCommand:
    name: str
    command: str
    cwd: Path
    location: OracleExecutionLocation


@dataclass(frozen=True)
class LayoutEvaluation:
    required_checks: tuple[str, ...]
    commands: tuple[CheckCommand, ...]
    blocked_reason: str | None
    name: ClassVar[EvaluationName] = EvaluationName.LAYOUT


@dataclass(frozen=True)
class TestcaseEvaluation:
    required_checks: tuple[str, ...]
    commands: tuple[CheckCommand, ...]
    blocked_reason: str | None
    name: ClassVar[EvaluationName] = EvaluationName.TESTCASE


@dataclass(frozen=True)
class FuzzingEvaluation:
    required_checks: tuple[str, ...]
    commands: tuple[CheckCommand, ...]
    blocked_reason: str | None
    name: ClassVar[EvaluationName] = EvaluationName.FUZZING


@dataclass(frozen=True)
class VerificationEvaluation:
    required_checks: tuple[str, ...]
    commands: tuple[CheckCommand, ...]
    blocked_reason: str | None
    name: ClassVar[EvaluationName] = EvaluationName.VERIFICATION


EvaluationPlan = LayoutEvaluation | TestcaseEvaluation | FuzzingEvaluation | VerificationEvaluation


def configured_oracle_commands(oracle_commands: dict[str, str]) -> dict[str, str]:
    empty = sorted(name for name, command in oracle_commands.items() if not command.strip())
    if empty:
        raise ValueError("oracle commands must not be empty: " + ", ".join(empty))
    return dict(oracle_commands)


def _selection(
    *,
    name: EvaluationName,
    required: tuple[str, ...],
    oracle_commands: dict[str, str],
    checkout_root: Path,
) -> tuple[tuple[str, ...], tuple[CheckCommand, ...], str | None]:
    names = required_checks_for_evaluation(required, name)
    missing = tuple(check for check in names if check not in oracle_commands)
    commands = tuple(
        CheckCommand(check, oracle_commands[check], checkout_root, location_for_check(check))
        for check in names
        if check in oracle_commands
    )
    reason = (
        "missing oracle commands for required checks: " + ", ".join(missing) if missing else None
    )
    return names, commands, reason


def build_evaluations(
    *,
    utility_cfg: ResolvedBenchmark,
    checkout_root: Path,
    oracle_commands: dict[str, str] | None = None,
) -> tuple[LayoutEvaluation, TestcaseEvaluation, FuzzingEvaluation, VerificationEvaluation]:
    commands = configured_oracle_commands(
        derived_oracle_commands(utility_cfg) if oracle_commands is None else oracle_commands
    )
    required = required_checks_for_task(utility_cfg)
    return (
        LayoutEvaluation(
            *_selection(
                name=EvaluationName.LAYOUT,
                required=required,
                oracle_commands=commands,
                checkout_root=checkout_root,
            )
        ),
        TestcaseEvaluation(
            *_selection(
                name=EvaluationName.TESTCASE,
                required=required,
                oracle_commands=commands,
                checkout_root=checkout_root,
            )
        ),
        FuzzingEvaluation(
            *_selection(
                name=EvaluationName.FUZZING,
                required=required,
                oracle_commands=commands,
                checkout_root=checkout_root,
            )
        ),
        VerificationEvaluation(
            *_selection(
                name=EvaluationName.VERIFICATION,
                required=required,
                oracle_commands=commands,
                checkout_root=checkout_root,
            )
        ),
    )


def derived_oracle_commands(
    utility_cfg: ResolvedBenchmark,
) -> dict[str, str]:
    utility_name = utility_cfg.name
    paths = utility_paths(utility_cfg, utility_name)
    if is_algorithm_utility(utility_name):
        return _algorithm_oracle_commands(utility_name, paths)
    return _coreutils_oracle_commands(
        utility_name,
        paths,
    )


def _coreutils_oracle_commands(
    utility_name: str,
    paths: dict[str, str],
) -> dict[str, str]:
    verified_filter = "dafny_verify"
    bench_test = f'"${{EVAL_REPO_ROOT:-.}}/bench/utils/{utility_name}/Tests.py"'
    bench_dll = f"_build/bench/{utility_name}_bench.dll"
    return {
        "impl_layout": "./eval_support/build.sh",
        "implementation_tests": (
            f"{EVAL_BENCH_BUILD_SCRIPT_ENV}=eval_support/build.sh "
            f"{EVAL_BENCH_DLL_ENV}={bench_dll} "
            f'make -C "${{EVAL_REPO_ROOT:-.}}/bench/utils/{utility_name}" test'
        ),
        "fuzzer": (
            f'python3 "${{EVAL_REPO_ROOT:-.}}/tools/coreutils_fuzzer/run.py" fuzz {utility_name}'
        ),
        "spec_shape": (
            f'{_oracle_dafny_env()} "${{DAFNY_BENCHMARK:-dafny-benchmark}}" verify '
            f'"${{EVAL_TARGET_ROOT:-.}}/{paths["spec"]}" {_oracle_dafny_options()}'
        ),
        "spec_consistency": f"pytest -q -n0 {bench_test} -m '{verified_filter}'",
        "proof_layout": "./eval_support/check_proof_layout.sh",
        "dafny_verify": "./eval_support/verify.sh",
    }


def _algorithm_oracle_commands(
    utility_name: str,
    paths: dict[str, str],
) -> dict[str, str]:
    algorithm_id = _algorithm_id(utility_name)
    return {
        "spec_shape": (
            f'{_oracle_dafny_env()} "${{DAFNY_BENCHMARK:-dafny-benchmark}}" verify '
            f"{_target_oracle_path(paths['spec'])} "
            f"{DAFNY_STANDARD_LIBRARY_OPTION}"
        ),
        "spec_consistency": (
            f'{_oracle_dafny_env()} "${{DAFNY_BENCHMARK:-dafny-benchmark}}" verify '
            f"{_target_oracle_path(paths['spec'])} "
            f"{DAFNY_STANDARD_LIBRARY_OPTION}"
        ),
        "impl_layout": "./eval_support/build.sh",
        "implementation_tests": (
            f"{EVAL_BENCH_BUILD_SCRIPT_ENV}=eval_support/build.sh "
            f"{EVAL_BENCH_DLL_ENV}=_build/bench/{utility_name}_bench.dll "
            f"ALGORITHM_BENCH_ID={algorithm_id} pytest -q -n0 "
            '"${EVAL_REPO_ROOT:-.}/tools/bench/test_bench_algorithm.py"'
        ),
        "proof_layout": "./eval_support/check_proof_layout.sh",
        "dafny_verify": "./eval_support/verify.sh",
    }


def _oracle_dafny_env() -> str:
    limit = DAFNY_VERIFY_DOTNET_HEAP_LIMIT
    return (
        "TMPDIR=/tmp "
        f'DOTNET_GCHeapHardLimit="${{DOTNET_GCHeapHardLimit:-{limit}}}" '
        'COMPlus_GCHeapHardLimit="${COMPlus_GCHeapHardLimit:-'
        f'${{DOTNET_GCHeapHardLimit:-{limit}}}}}"'
    )


def _oracle_dafny_options() -> str:
    return f"--allow-external-contracts --dont-verify-dependencies {DAFNY_STANDARD_LIBRARY_OPTION}"


def _target_oracle_path(path: str) -> str:
    return f'"${{EVAL_TARGET_ROOT:-.}}/{path}"'
