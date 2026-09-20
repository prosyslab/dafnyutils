"""Manage evaluator Docker lifetimes, cleanup, and candidate-visible oracle guards."""

from __future__ import annotations

import hashlib
import os
import re
import shutil
import subprocess
import tempfile
from collections.abc import Mapping
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Generator

from benchmarks.paths import REPO_ROOT
from evaluation.environment import EVAL_COREUTILS_BIN_ENV
from evaluation.submission.container_mounts import (
    DEFAULT_EVALUATOR_IMAGE,
    OracleExecutableBlock,
    build_evaluator_container_workspace_plan,
    write_evaluator_compose_override,
)

EVALUATION_COMPOSE_FILE = REPO_ROOT / "docker-compose.evaluation.yml"
_ORACLE_ISOLATION_ENTRYPOINT_SCRIPT = Path(__file__).with_name("oracle_isolation_entrypoint.sh")
_DOCKER_PROJECT_NAME = "dafnyutils-eval"
_EVALUATOR_CONTAINER_LABEL = "dafnyutils.evaluator.run"
_EVALUATOR_RUNTIME_ENV_KEYS = (
    "DOTNET_GCHeapHardLimit",
    "COMPlus_GCHeapHardLimit",
    "SEED",
    "ITERATIONS",
    "FUZZ_PROCESS_TIMEOUT_SECONDS",
    "NUGET_PACKAGES",
    "RestoreSources",
    "RUSTUP_HOME",
    "CARGO_HOME",
    "CARGO_NET_OFFLINE",
)
_DOCKER_COMMAND_ENV_KEYS = (
    "PATH",
    "HOME",
    "DOCKER_CERT_PATH",
    "DOCKER_CONFIG",
    "DOCKER_CONTEXT",
    "DOCKER_HOST",
    "DOCKER_TLS_VERIFY",
    "TMPDIR",
    "XDG_RUNTIME_DIR",
)


@dataclass(frozen=True)
class SandboxContext:
    """Evaluator-facing subset of an externally managed candidate sandbox."""

    compose_files: tuple[Path, ...]
    compose_project_name: str
    evaluator_container_name: str


class EvaluatorUnavailableError(RuntimeError):
    """The required evaluator container runtime is unavailable."""


def docker_runtime_available() -> bool:
    if shutil.which("docker") is None:
        return False
    try:
        completed = subprocess.run(
            ["docker", "compose", "version"],
            cwd=REPO_ROOT,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired):
        return False
    return completed.returncode == 0


def evaluator_environment(env: Mapping[str, str]) -> dict[str, str]:
    evaluator_env = {key: env[key] for key in _EVALUATOR_RUNTIME_ENV_KEYS if key in env}
    if EVAL_COREUTILS_BIN_ENV in env:
        evaluator_env[EVAL_COREUTILS_BIN_ENV] = _container_repo_path(env[EVAL_COREUTILS_BIN_ENV])
    return evaluator_env


def _docker_command_environment(env: Mapping[str, str]) -> dict[str, str]:
    return {key: env[key] for key in _DOCKER_COMMAND_ENV_KEYS if key in env}


@contextmanager
def evaluator_scope(
    *,
    run_directory: Path,
    evaluator_target_dir: Path,
    artifact_directory: Path | None = None,
    evaluator_image: str = DEFAULT_EVALUATOR_IMAGE,
    env: Mapping[str, str] | None = None,
) -> Generator[SandboxContext, None, None]:
    """Create an evaluator-only, no-network sandbox for a prepared target."""
    if not docker_runtime_available():
        raise EvaluatorUnavailableError(
            "docker compose sandbox is required for evaluation, but Docker is unavailable"
        )
    run_directory = run_directory.resolve()
    run_root = run_directory / "sandbox" / "run"
    artifact_root = (artifact_directory or run_directory / "artifacts").resolve()
    artifact_root.mkdir(parents=True, exist_ok=True)
    control_dir = Path(
        tempfile.mkdtemp(prefix=f".{run_directory.name}-evaluator-", dir=run_directory.parent)
    )
    source_env = dict(os.environ if env is None else env)
    container_name = f"dafnyutils-evaluator-{_short_path_hash(run_directory)}"
    try:
        evaluator_plan = build_evaluator_container_workspace_plan(
            evaluator_target_root=evaluator_target_dir,
            run_root=run_root,
            artifact_directory=artifact_root,
        )
        override = control_dir / "docker-compose.override.yml"
        write_evaluator_compose_override(
            path=override,
            evaluator_plan=evaluator_plan,
            evaluator_environment=evaluator_environment(source_env),
            evaluator_container_name=container_name,
            evaluator_image=evaluator_image,
            container_labels={_EVALUATOR_CONTAINER_LABEL: container_name},
        )
        compose_files = (EVALUATION_COMPOSE_FILE, override)
        yield SandboxContext(
            compose_files=compose_files,
            compose_project_name=_docker_project_name(),
            evaluator_container_name=container_name,
        )
    finally:
        _cleanup_evaluator_container(container_name, source_env)
        shutil.rmtree(control_dir, ignore_errors=True)


def _cleanup_evaluator_container(container_name: str, env: Mapping[str, str]) -> None:
    try:
        subprocess.run(
            ["docker", "rm", "--force", container_name],
            cwd=REPO_ROOT,
            env=_docker_command_environment(env),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired):
        pass


def cleanup_evaluator_after_timeout(
    context: SandboxContext,
    environment: Mapping[str, str],
) -> None:
    """Remove a named evaluator left behind when its host command timed out."""
    _cleanup_evaluator_container(context.evaluator_container_name, environment)


def cleanup_fuzzer_container(container_name: str, environment: Mapping[str, str]) -> None:
    """Remove only the disposable fuzzer container owned by this evaluation run."""
    try:
        subprocess.run(
            ["docker", "rm", "--force", container_name],
            cwd=REPO_ROOT,
            env=_docker_command_environment(environment),
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired):
        pass


def _short_path_hash(path: Path) -> str:
    return hashlib.sha256(str(path.resolve()).encode("utf-8")).hexdigest()[:12]


def seed_workspace_isolation_tools(run_root: Path) -> None:
    """Install the benchmark-owned oracle guard for a candidate sandbox."""
    tool_dir = run_root / "tools"
    tool_dir.mkdir(parents=True, exist_ok=True)
    oracle_entrypoint = tool_dir / "oracle-isolation-entrypoint"
    oracle_entrypoint.write_text(
        _ORACLE_ISOLATION_ENTRYPOINT_SCRIPT.read_text(encoding="utf-8"),
        encoding="utf-8",
    )
    oracle_entrypoint.chmod(0o755)


def prepare_oracle_executable_block(
    *,
    control_dir: Path,
    task_domain: str | None,
    utility_name: str,
) -> OracleExecutableBlock | None:
    """Create the benchmark-owned bind mount that hides a coreutils oracle."""
    if task_domain == "algorithm":
        return None
    if task_domain is not None:
        raise ValueError(f"unsupported task domain for oracle isolation: {task_domain}")
    if re.fullmatch(r"[a-z0-9][a-z0-9-]*", utility_name) is None:
        raise ValueError(f"invalid coreutils oracle executable name: {utility_name}")
    block_dir = control_dir / "oracle-executable-block"
    block_dir.mkdir(mode=0o700)
    source = block_dir / utility_name
    source.touch(mode=0o000)
    source.chmod(0o000)
    return OracleExecutableBlock(utility_name=utility_name, source=source)


def _container_repo_path(raw_path: str) -> str:
    try:
        rel_path = Path(raw_path).resolve().relative_to(REPO_ROOT)
    except ValueError:
        return raw_path
    return str(Path("/repo") / rel_path)


def _docker_project_name() -> str:
    return _DOCKER_PROJECT_NAME
