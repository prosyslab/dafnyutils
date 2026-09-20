"""Configure trusted oracle paths and environments for host and container evaluation."""

from __future__ import annotations

import hashlib
import os
from dataclasses import replace
from pathlib import Path

from benchmarks.checks import OracleExecutionLocation
from benchmarks.paths import REPO_ROOT
from evaluation.environment import (
    EVAL_COREUTILS_BIN_ENV,
    EVAL_REPO_ROOT_ENV,
    EVAL_TARGET_ROOT_ENV,
    EVAL_WORKSPACE_DIR_ENV,
)
from evaluation.submission.container_mounts import build_docker_compose_check_command
from evaluation.submission.oracles import EvaluationPlan
from evaluation.submission.sandbox import SandboxContext


def configure_host_oracle_environment(env: dict[str, str], oracle_target_root: Path) -> None:
    oracle_target_root = oracle_target_root.resolve()
    for key in ("PYTHONPATH", "NUGET_PACKAGES", "RestoreSources"):
        env.pop(key, None)
    for key in (
        "PATH",
        "HOME",
        "TMPDIR",
        "XDG_RUNTIME_DIR",
        "RUSTUP_HOME",
        "CARGO_HOME",
        "CARGO_TARGET_DIR",
    ):
        if key in os.environ:
            env[key] = os.environ[key]
        else:
            env.pop(key, None)
    for key in (
        "DOCKER_HOST",
        "DOCKER_CONTEXT",
        "DOCKER_CONFIG",
        "DOCKER_CERT_PATH",
        "DOCKER_TLS_VERIFY",
        "CARGO_NET_OFFLINE",
    ):
        if key in os.environ:
            env.setdefault(key, os.environ[key])
    env["DAFNYUTILS_REPO_ROOT"] = str(REPO_ROOT)
    env[EVAL_REPO_ROOT_ENV] = str(REPO_ROOT)
    env[EVAL_TARGET_ROOT_ENV] = str(oracle_target_root)
    env[EVAL_WORKSPACE_DIR_ENV] = str(oracle_target_root)
    env["REF_BIN_TEMPLATE"] = str(REPO_ROOT / "_build/coreutils/src/{util}")
    env["DUT_BIN_TEMPLATE"] = str(oracle_target_root / "_build/bench/{util}_bench.dll")
    env["FUZZ_CONTAINER_NAME"] = fuzzer_container_name(oracle_target_root)


def fuzzer_container_name(oracle_target_root: Path) -> str:
    digest = hashlib.sha256(str(oracle_target_root.resolve()).encode("utf-8")).hexdigest()[:12]
    return f"dafnyutils-fuzzer-{digest}"


def configure_container_oracle_environment(env: dict[str, str]) -> None:
    env["DAFNYUTILS_REPO_ROOT"] = "/repo"
    env[EVAL_REPO_ROOT_ENV] = "/repo"
    env[EVAL_TARGET_ROOT_ENV] = "/target"
    env[EVAL_WORKSPACE_DIR_ENV] = "/target"
    env.pop("PYTHONPATH", None)
    coreutils_bin = env.get(EVAL_COREUTILS_BIN_ENV)
    if coreutils_bin:
        try:
            rel_path = Path(coreutils_bin).resolve().relative_to(REPO_ROOT)
        except ValueError:
            pass
        else:
            env[EVAL_COREUTILS_BIN_ENV] = str(Path("/repo") / rel_path)
    env["REF_BIN_TEMPLATE"] = "/repo/_build/coreutils/src/{util}"
    env["DUT_BIN_TEMPLATE"] = "_build/bench/{util}_bench.dll"


def containerized_evaluation(
    plan: EvaluationPlan,
    sandbox_context: SandboxContext | None,
) -> EvaluationPlan:
    if sandbox_context is None:
        return plan
    return replace(
        plan,
        commands=tuple(
            replace(
                command,
                command=_containerized_command(command.command, sandbox_context),
                cwd=REPO_ROOT,
            )
            if command.location is OracleExecutionLocation.EVALUATOR_CONTAINER
            else command
            for command in plan.commands
        ),
    )


def _containerized_command(command: str, sandbox_context: SandboxContext) -> str:
    return build_docker_compose_check_command(
        compose_files=sandbox_context.compose_files,
        service="evaluator",
        command=command,
        project_name=sandbox_context.compose_project_name,
        container_name=sandbox_context.evaluator_container_name,
    )
