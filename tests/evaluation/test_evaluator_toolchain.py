from __future__ import annotations

import inspect
from pathlib import Path

import pytest
import yaml

import evaluation.submission.sandbox as sandbox
from evaluation.submission.container_mounts import (
    DEFAULT_EVALUATOR_IMAGE,
    ContainerWorkspacePlan,
    write_evaluator_compose_override,
)


def _workspace_plan() -> ContainerWorkspacePlan:
    return ContainerWorkspacePlan(
        service="evaluator",
        mounts=(),
        working_dir="/workspace",
        environment={},
    )


# The evaluator-owned override must bind the selected immutable evaluator image.
def test_compose_override_writes_explicit_evaluator_image(tmp_path: Path) -> None:
    override_path = tmp_path / "docker-compose.override.yml"

    write_evaluator_compose_override(
        path=override_path,
        evaluator_plan=_workspace_plan(),
        evaluator_environment={},
        evaluator_container_name="evaluator-test",
        evaluator_image="evaluator@sha256:def",
    )

    services = yaml.safe_load(override_path.read_text(encoding="utf-8"))["services"]
    assert services["evaluator"]["image"] == "evaluator@sha256:def"
    assert set(services) == {"evaluator"}
    assert "labels" not in services["evaluator"]


# YAML-looking environment and label strings must remain strings after serialization.
def test_compose_override_preserves_yaml_scalar_strings(tmp_path: Path) -> None:
    override_path = tmp_path / "docker-compose.override.yml"
    environment = {
        "BOOLISH": "true",
        "NUMBERISH": "123",
        "NULLISH": "null",
        "COMMENTISH": "# not a comment",
    }
    labels = {"com.example.value": "key: value"}

    write_evaluator_compose_override(
        path=override_path,
        evaluator_plan=_workspace_plan(),
        evaluator_environment=environment,
        evaluator_container_name="evaluator-test",
        container_labels=labels,
    )

    service = yaml.safe_load(override_path.read_text(encoding="utf-8"))["services"]["evaluator"]
    assert service["environment"] == environment
    assert service["labels"] == labels


# Generic evaluator callers retain the documented mutable default until they pass an image.
def test_evaluator_override_retains_default_evaluator_image() -> None:
    parameter = inspect.signature(write_evaluator_compose_override).parameters["evaluator_image"]
    assert parameter.default == DEFAULT_EVALUATOR_IMAGE


# Standalone evaluation must compose only the no-network evaluator and clean its control state.
def test_evaluator_scope_builds_neutral_context_and_cleans_up(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    cleanup_calls: list[str] = []
    monkeypatch.setattr(sandbox, "docker_runtime_available", lambda: True)
    monkeypatch.setattr(
        sandbox,
        "_cleanup_evaluator_container",
        lambda name, _env: cleanup_calls.append(name),
    )
    run_directory = tmp_path / "run"
    run_directory.mkdir()
    target = tmp_path / "target"

    with sandbox.evaluator_scope(
        run_directory=run_directory,
        evaluator_target_dir=target,
        env={"SEED": "7"},
    ) as context:
        override = context.compose_files[-1]
        payload = yaml.safe_load(override.read_text(encoding="utf-8"))
        assert set(payload["services"]) == {"evaluator"}
        assert context.compose_files[0] == sandbox.EVALUATION_COMPOSE_FILE

    assert cleanup_calls == [context.evaluator_container_name]
    assert not override.exists()
