"""Describe evaluator bind mounts and render Compose overrides and check commands."""

from __future__ import annotations

import json
import os
import shlex
import subprocess
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Literal, cast

import yaml

from benchmarks.paths import REPO_ROOT
from evaluation.enums import MountMode
from evaluation.submission.infrastructure import CANDIDATE_INFRASTRUCTURE_REPORT_ENV

CONTAINER_RUN_ROOT = "/run"
CONTAINER_ARTIFACT_DIR = "/run/agent_artifacts"
CONTAINER_TOOLS_DIR = "/run/tools"
DEFAULT_EVALUATOR_IMAGE = "dafnyutils-evaluation:latest"
CONTAINER_ORACLE_ISOLATION_ENTRYPOINT = f"{CONTAINER_TOOLS_DIR}/oracle-isolation-entrypoint"
BLOCKED_COREUTIL_ENV = "EVAL_BLOCKED_COREUTIL"


@dataclass(frozen=True)
class ContainerMount:
    source: Path
    target: str
    mode: MountMode
    kind: Literal["bind"] = "bind"

    @property
    def read_only(self) -> bool:
        return self.mode == MountMode.READ_ONLY

    def as_compose_volume(self) -> dict[str, object]:
        return {
            "type": self.kind,
            "source": str(_docker_bind_source_path(self.source)),
            "target": self.target,
            "read_only": self.read_only,
        }

    def as_json(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "source": str(self.source),
            "target": self.target,
            "mode": self.mode,
        }


@dataclass(frozen=True)
class ContainerWorkspacePlan:
    """A neutral mount plan identified by its Compose service name."""

    service: str
    mounts: tuple[ContainerMount, ...]
    working_dir: str
    environment: dict[str, str]

    def as_json(self) -> dict[str, object]:
        return {
            "service": self.service,
            "working_dir": self.working_dir,
            "environment": dict(sorted(self.environment.items())),
            "mounts": [mount.as_json() for mount in self.mounts],
        }


@dataclass(frozen=True)
class OracleExecutableBlock:
    """Task-specific system executable hidden from a candidate container."""

    utility_name: str
    source: Path

    @property
    def target(self) -> str:
        return f"/usr/bin/{self.utility_name}"


def add_oracle_executable_block(
    mounts: list[ContainerMount],
    environment: dict[str, str],
    oracle_block: OracleExecutableBlock | None,
) -> None:
    """Apply the benchmark-owned oracle block to a candidate mount plan."""
    if oracle_block is None:
        return
    mounts.append(ContainerMount(oracle_block.source, oracle_block.target, MountMode.READ_ONLY))
    environment[BLOCKED_COREUTIL_ENV] = oracle_block.utility_name


def build_evaluator_container_workspace_plan(
    *,
    evaluator_target_root: Path,
    run_root: Path,
    artifact_directory: Path,
) -> ContainerWorkspacePlan:
    """Build the fixed evaluator-only view of a captured candidate result."""
    run_root.mkdir(parents=True, exist_ok=True)
    evaluator_target_root.mkdir(parents=True, exist_ok=True)
    return ContainerWorkspacePlan(
        service="evaluator",
        mounts=_dedupe_mounts(
            (
                ContainerMount(REPO_ROOT, "/repo", MountMode.READ_ONLY),
                ContainerMount(evaluator_target_root, "/target", MountMode.READ_WRITE),
                ContainerMount(run_root, CONTAINER_RUN_ROOT, MountMode.READ_WRITE),
                ContainerMount(artifact_directory, CONTAINER_ARTIFACT_DIR, MountMode.READ_WRITE),
            )
        ),
        working_dir="/target",
        environment={},
    )


def write_mount_manifest(path: Path, plans: tuple[ContainerWorkspacePlan, ...]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = {"container_workspace_plans": [plan.as_json() for plan in plans]}
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_evaluator_compose_override(
    *,
    path: Path,
    evaluator_plan: ContainerWorkspacePlan,
    evaluator_environment: dict[str, str],
    evaluator_container_name: str,
    evaluator_image: str = DEFAULT_EVALUATOR_IMAGE,
    container_labels: dict[str, str] | None = None,
) -> None:
    """Write only the evaluator service fields needed for one isolated run."""
    if not evaluator_image.strip():
        raise ValueError("evaluator image must not be empty")
    path.parent.mkdir(parents=True, exist_ok=True)
    service: dict[str, object] = {
        "image": evaluator_image,
        "container_name": evaluator_container_name,
        "working_dir": evaluator_plan.working_dir,
        "user": "evaluator",
        "command": ["sleep", "infinity"],
        "environment": {**evaluator_environment, **evaluator_plan.environment},
        "labels": container_labels or {},
        "volumes": [mount.as_compose_volume() for mount in evaluator_plan.mounts],
    }
    path.write_text(_compose_yaml({"evaluator": service}), encoding="utf-8")


def build_docker_compose_check_command(
    *,
    compose_files: tuple[Path, ...],
    service: str,
    command: str,
    project_name: str | None = None,
    container_name: str | None = None,
) -> str:
    """Invoke the packaged evaluator check script with quoted arguments."""
    if container_name is None:
        raise ValueError("evaluator checks require a container name")
    return shlex.join(
        (
            "bash",
            str(Path(__file__).with_name("compose_check.sh")),
            container_name,
            project_name or "",
            service,
            command,
            CANDIDATE_INFRASTRUCTURE_REPORT_ENV,
            *(str(compose_file) for compose_file in compose_files),
        )
    )


def _dedupe_mounts(mounts: tuple[ContainerMount, ...]) -> tuple[ContainerMount, ...]:
    seen: dict[str, ContainerMount] = {}
    ordered: list[ContainerMount] = []
    for mount in mounts:
        if not mount.target.startswith("/"):
            raise ValueError(f"container mount target must be absolute: {mount.target}")
        existing = seen.get(mount.target)
        if existing is not None:
            if existing != mount:
                raise ValueError(f"conflicting container mount target: {mount.target}")
            continue
        seen[mount.target] = mount
        ordered.append(mount)
    return tuple(ordered)


def _docker_bind_source_path(path: Path) -> Path:
    resolved = path.resolve()
    for local_root, docker_root in _docker_bind_mount_mappings():
        try:
            rel_path = resolved.relative_to(local_root)
        except ValueError:
            continue
        return docker_root / rel_path
    return path


def _compose_yaml(services: dict[str, dict[str, object]]) -> str:
    normalized_services: dict[str, dict[str, object]] = {}
    for service_name, service in services.items():
        normalized_service = dict(service)
        for key in ("environment", "labels"):
            mapping = normalized_service.get(key)
            if key == "labels" and not mapping:
                normalized_service.pop(key, None)
            elif isinstance(mapping, dict):
                normalized_service[key] = dict(sorted(mapping.items()))
        normalized_services[service_name] = normalized_service
    return cast(
        str,
        yaml.safe_dump(
            {"services": normalized_services},
            sort_keys=False,
            default_flow_style=False,
        ),
    )


@lru_cache(maxsize=1)
def _docker_bind_mount_mappings() -> tuple[tuple[Path, Path], ...]:
    container_id = os.environ.get("HOSTNAME", "").strip()
    if not container_id:
        return ()
    try:
        completed = subprocess.run(
            ["docker", "inspect", container_id, "--format", "{{json .Mounts}}"],
            check=False,
            capture_output=True,
            text=True,
            timeout=5,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ()
    if completed.returncode != 0:
        return ()
    try:
        mounts = json.loads(completed.stdout)
    except json.JSONDecodeError:
        return ()
    if not isinstance(mounts, list):
        return ()
    mappings: list[tuple[Path, Path]] = []
    for mount in mounts:
        if not isinstance(mount, dict):
            continue
        source = mount.get("Source")
        destination = mount.get("Destination")
        if not isinstance(source, str) or not isinstance(destination, str):
            continue
        if not source.startswith("/") or not destination.startswith("/"):
            continue
        mappings.append((Path(destination).resolve(), Path(source)))
    return tuple(sorted(mappings, key=lambda item: len(item[0].parts), reverse=True))
