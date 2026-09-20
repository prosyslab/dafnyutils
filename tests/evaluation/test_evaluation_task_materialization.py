"""Run-local task input materialization tests."""

from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest

import benchmarks.contracts as task_contract
import evaluation.task.preparation as task_materialization
import evaluation.task.workspace as benchmark_workspace
from benchmarks.generated_profile import generate_task_profile
from benchmarks.paths import REPO_ROOT
from benchmarks.profiles import ResolvedBenchmark
from benchmarks.repository import BenchmarkRepository
from benchmarks.task import TaskProfile
from entry_contract import analyze_entry_contract as shared_analyze_entry_contract
from evaluation.task.workspace import task_workspace_spec
from tests.evaluation.evaluation_test_support import utility_config


def _utility_cfg(utility_name: str) -> ResolvedBenchmark:
    return utility_config(utility_name)


def _generated_profile(utility_name: str, repository_root: Path = REPO_ROOT):
    repository = BenchmarkRepository.open(repository_root)
    return generate_task_profile(
        repository.load_definition(utility_name),
        repository_root=repository_root,
        configuration=_utility_cfg(utility_name),
    )


# A real cat profile becomes one JSON task plus copied natural and formal resources.
def test_materialize_task_inputs_writes_structured_task_bundle(tmp_path: Path) -> None:
    layout = task_materialization.materialize_task_inputs(
        run_dir=tmp_path / "run",
        utility_cfg=_utility_cfg("cat"),
        utility_name="cat",
        validated_profile=_generated_profile("cat"),
    )

    task = TaskProfile.from_json_file(layout.task_path)
    assert layout.task_dir == tmp_path / "run" / "task"
    assert layout.task_path == layout.task_dir / "task.json"
    assert task.task_id == "cat"
    assert {definition.source_path for definition in task.dafny.spec_definitions} <= {
        resource.path
        for resource in task.resources
        if resource.kind.value == "formal-specification"
    }
    assert layout.visible_artifacts["natural-spec"].read_text(encoding="utf-8") == (
        REPO_ROOT / "bench/utils/cat/cat.md"
    ).read_text(encoding="utf-8")
    assert all(path.is_file() for path in layout.visible_artifacts.values())


# A real algorithm task copies its immutable natural, formal, and support resources exactly.
def test_materialize_task_inputs_copies_algorithm_specifications(tmp_path: Path) -> None:
    layout = task_materialization.materialize_task_inputs(
        run_dir=tmp_path / "run",
        utility_cfg=_utility_cfg("algorithm-75"),
        utility_name="algorithm-75",
        validated_profile=_generated_profile("algorithm-75"),
    )

    assert (
        layout.visible_artifacts["formal-001"].read_bytes()
        == (REPO_ROOT / "bench/algorithm/75/Spec.dfy").read_bytes()
    )
    assert (
        layout.visible_artifacts["natural-spec"].read_bytes()
        == (REPO_ROOT / "bench/algorithm/75/algorithm-75.md").read_bytes()
    )
    assert (
        layout.visible_artifacts["functional-core"].read_bytes()
        == (REPO_ROOT / "bench/core/Functional.dfy").read_bytes()
    )


# A prepared task reuses its baseline contract analysis for workspace planning.
def test_prepared_task_reuses_contract_analysis(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    analysis_calls = 0
    original_analyze = shared_analyze_entry_contract

    def count_analysis(*args: object, **kwargs: object):  # noqa: ANN001
        nonlocal analysis_calls
        analysis_calls += 1
        return original_analyze(*args, **kwargs)

    monkeypatch.setattr(task_contract, "analyze_entry_contract", count_analysis)
    utility = _utility_cfg("cat")
    layout = task_materialization.materialize_task_inputs(
        run_dir=tmp_path / "run",
        utility_cfg=utility,
        utility_name="cat",
        validated_profile=_generated_profile("cat"),
    )
    task = TaskProfile.from_json_file(layout.task_path)

    task_spec = task_workspace_spec(
        utility_cfg=utility,
        utility_name="cat",
        task=task,
        prepared_task=layout.prepared_task,
    )

    assert analysis_calls == 1
    assert Path("bench/utils/cat/CatQuoteSpec.dfy") in task_spec.read_only_paths


# A prepared task rejects source edits before workspace generation can slice stale spans.
def test_prepared_task_rejects_source_edit_before_workspace_generation(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    repository_root = tmp_path / "repository"
    shutil.copytree(REPO_ROOT / "bench", repository_root / "bench")
    monkeypatch.setattr(task_materialization, "REPO_ROOT", repository_root)
    monkeypatch.setattr(task_contract, "REPO_ROOT", repository_root)
    monkeypatch.setattr(benchmark_workspace, "REPO_ROOT", repository_root)
    utility = _utility_cfg("cat")
    layout = task_materialization.materialize_task_inputs(
        run_dir=tmp_path / "run",
        utility_cfg=utility,
        utility_name="cat",
        validated_profile=_generated_profile("cat", repository_root),
    )
    source = repository_root / "bench/utils/cat/Cat.dfy"
    source.write_text("// source edit\n" + source.read_text(encoding="utf-8"), encoding="utf-8")

    with pytest.raises(ValueError, match="prepared task source snapshot changed"):
        task_workspace_spec(
            utility_cfg=utility,
            utility_name="cat",
            prepared_task=layout.prepared_task,
        )


# An external task JSON cannot omit a source required by its formal specification closure.
def test_task_profile_rejects_missing_formal_resource() -> None:
    profile = _generated_profile("algorithm-1").profile
    payload = profile.model_dump(mode="json")
    required_path = profile.dafny.spec_definitions[0].source_path
    payload["resources"] = [
        resource for resource in payload["resources"] if resource["path"] != required_path
    ]

    with pytest.raises(ValueError, match="every specification definition source"):
        TaskProfile.model_validate_json(json.dumps(payload))
