"""Workspace tests for the fixed implementation-and-proof evaluation surface."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

import evaluation.task.workspace as benchmark_workspace
from benchmarks.generated_profile import generate_task_profile
from benchmarks.paths import REPO_ROOT
from benchmarks.profiles import (
    FUNCTIONAL_CORE_SOURCE,
    ResolvedBenchmark,
)
from benchmarks.repository import BenchmarkRepository
from benchmarks.task import TaskProfile
from evaluation.outputs import (
    copy_candidate_outputs,
)
from evaluation.submission.workspace import prepare_evaluator_target
from evaluation.task.preparation import materialize_task_inputs
from evaluation.task.workspace import (
    materialize_workspace_layout,
    refresh_workspace_support_files,
    task_workspace_spec,
)
from tests.evaluation.evaluation_test_support import utility_config

SYSTEM_SUPPORT_MODELS = (
    "SecurityModel",
    "WorldLookupProof",
    "WorldInsertProof",
    "WorldRemoveProof",
    "WorldRenameProof",
    "WorldFileSystemProof",
)


def _utility_cfg(utility_name: str) -> ResolvedBenchmark:
    return utility_config(utility_name)


def _task_spec(utility_name: str):
    return task_workspace_spec(
        utility_cfg=_utility_cfg(utility_name),
        utility_name=utility_name,
    )


def _task_inputs(tmp_path: Path, utility_name: str):
    repository = BenchmarkRepository.open(REPO_ROOT)
    return materialize_task_inputs(
        run_dir=tmp_path / "run",
        utility_cfg=_utility_cfg(utility_name),
        utility_name=utility_name,
        validated_profile=generate_task_profile(
            repository.load_definition(utility_name), repository_root=REPO_ROOT
        ),
    )


# A coreutils workspace must protect formal inputs and receive its complete support surface.
def test_workspace_uses_generic_entry_contract_support(tmp_path: Path) -> None:
    utility_name = "cat"
    task_inputs = _task_inputs(tmp_path, utility_name)
    task = TaskProfile.from_json_file(task_inputs.task_path)
    task_spec = task_workspace_spec(
        utility_cfg=_utility_cfg(utility_name),
        utility_name=utility_name,
        task=task,
    )
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=task_inputs,
        task_spec=task_spec,
    )

    support_root = roots.workspace_root / "eval_support"
    formal_paths = {
        Path(resource.path)
        for resource in task.resources
        if resource.kind.value == "formal-specification"
    }
    assert formal_paths.issubset(set(task_spec.read_only_paths))
    functional_core_path = Path(FUNCTIONAL_CORE_SOURCE)
    assert functional_core_path in set(task_spec.copied_paths)
    assert Path("bench/core/DafnyStandardLibrary.md") not in set(task_spec.copied_paths)
    assert not any(
        Path("dafny/Source/DafnyStandardLibraries") in path.parents
        for path in task_spec.copied_paths
    )
    project_config = (
        roots.workspace_root / _utility_cfg(utility_name).utility_dir / "dfyconfig.toml"
    )
    build_text = (support_root / "build.sh").read_text(encoding="utf-8")
    check_text = (support_root / "check_proof_layout.sh").read_text(encoding="utf-8")
    verify_text = (support_root / "verify.sh").read_text(encoding="utf-8")
    verifier_text = (REPO_ROOT / "src/verification.py").read_text(encoding="utf-8")
    assert (support_root / "entry_contract.json").is_file()
    assert not (support_root / "entry_contract.py").exists()
    assert not (support_root / "verification.py").exists()
    assert not (support_root / "analysis").exists()
    assert '"${DAFNY_BENCHMARK:-dafny-benchmark}" build' in build_text
    assert "PYTHONPATH" not in build_text + check_text + verify_text
    assert (
        project_config.read_bytes()
        == (REPO_ROOT / _utility_cfg(utility_name).utility_dir / "dfyconfig.toml").read_bytes()
    )
    assert project_config.stat().st_mode & 0o222 == 0
    assert (roots.workspace_root / functional_core_path).is_file()
    for name in ("Tests.dfy", "Tests.py", "Makefile"):
        hidden = Path(f"bench/utils/{utility_name}/{name}")
        assert hidden in task_spec.hidden_paths
        assert not (roots.workspace_root / hidden).exists()
    for model_name in SYSTEM_SUPPORT_MODELS:
        relative = Path(f"bench/core/{model_name}.dfy")
        assert (roots.workspace_root / relative).read_bytes() == (REPO_ROOT / relative).read_bytes()
        assert relative in task_spec.read_only_paths
    assert not (support_root / "impl_layout_self_check.py").exists()
    assert not (support_root / "proof_layout_self_check.py").exists()
    assert "entry_contract check" in build_text
    assert (
        build_text.index('workspace_root="${EVAL_WORKSPACE_DIR:-$PWD}"')
        < build_text.index('cd "$workspace_root"')
        < build_text.index("entry_contract check")
    )
    assert "entry_contract check" in check_text
    assert "python3 -m verification" in verify_text
    assert '--workspace-root "$workspace_root"' in verify_text
    assert f"--utility-root {_utility_cfg(utility_name).utility_dir}" in verify_text
    assert '--manifest "$script_dir/entry_contract.json"' in verify_text
    assert "find " not in verify_text
    assert "while IFS=" not in verify_text
    support_text = build_text + check_text + verify_text + verifier_text
    assert "--allow-axioms" not in support_text
    assert "--allow-warnings" not in support_text
    assert "--allow-external-contracts" in verifier_text
    assert "--verify-included-files" in verifier_text
    assert "--profile" not in build_text + check_text + verify_text
    assert str(project_config.relative_to(roots.workspace_root)) in build_text
    assert "--target:cs" not in build_text
    assert "--no-verify" not in build_text
    assert roots.task_root == roots.sandbox_root / "task"
    assert (roots.task_root / "task.json").read_text(
        encoding="utf-8"
    ) == task_inputs.task_path.read_text(encoding="utf-8")


# Touch candidate materialization excludes the evaluator-owned parser source and binary.
def test_touch_workspace_does_not_expose_trusted_time_parser(tmp_path: Path) -> None:
    task_inputs = _task_inputs(tmp_path, "touch")
    task = TaskProfile.from_json_file(task_inputs.task_path)
    task_spec = task_workspace_spec(
        utility_cfg=_utility_cfg("touch"),
        utility_name="touch",
        task=task,
    )
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=task_inputs,
        task_spec=task_spec,
    )
    private_paths = (
        Path("bench/core/TouchTimeParser.c"),
        Path("_build/bench/touch_time_parser"),
    )

    for private_path in private_paths:
        assert private_path not in task_spec.copied_paths
        assert not (roots.workspace_root / private_path).exists()
        assert all(resource.path != private_path.as_posix() for resource in task.resources)
    build_text = (roots.workspace_root / "eval_support/build.sh").read_text(encoding="utf-8")
    assert "TouchTimeParser.c" not in build_text
    assert "touch_time_parser" not in build_text


# Changing a copied system model is rejected through the immutable support baseline.
@pytest.mark.parametrize("model_name", SYSTEM_SUPPORT_MODELS)
def test_modified_system_support_is_rejected_during_capture(
    tmp_path: Path, model_name: str
) -> None:
    task_spec = _task_spec("cat")
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=_task_inputs(tmp_path, "cat"),
        task_spec=task_spec,
    )
    relative = Path(f"bench/core/{model_name}.dfy")
    model = roots.workspace_root / relative
    model.write_text(f"module {model_name} {{}}\n", encoding="utf-8")

    result, records = copy_candidate_outputs(
        workspace_root=roots.workspace_root,
        candidate_output_root=roots.candidate_output_root,
        task_spec=task_spec,
    )

    assert result.error == f"read-only path changed in sandbox workspace: {relative}"
    record = next(record for record in records if record.path == relative.as_posix())
    assert record.changed_from_baseline is True
    assert record.captured is False
    assert record.error == result.error


# Chmod's split specification workspace must retain every include without exposing implementations.
def test_materialized_chmod_split_specification_passes_layout_check(tmp_path: Path) -> None:
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=_task_inputs(tmp_path, "chmod"),
        task_spec=_task_spec("chmod"),
    )
    utility = roots.workspace_root / "bench/utils/chmod"

    for name in (
        "ChmodRecursiveCore.dfy",
        "ChmodRecursiveLeafRuntime.dfy",
        "ChmodRecursiveRuntime.dfy",
    ):
        assert (utility / name).is_file()
    assert "RunRecursiveCore" not in (utility / "ChmodRecursiveRuntime.dfy").read_text(
        encoding="utf-8"
    )

    completed = subprocess.run(
        ["bash", "eval_support/check_proof_layout.sh"],
        cwd=roots.workspace_root,
        text=True,
        capture_output=True,
        check=False,
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr


# An algorithm workspace must seed its formal inputs and accept the trusted candidate tree.
def test_materialized_algorithm_accepts_the_trusted_candidate_tree(tmp_path: Path) -> None:
    task_spec = _task_spec("algorithm-75")
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=_task_inputs(tmp_path, "algorithm-75"),
        task_spec=task_spec,
    )
    utility_dir = Path("bench/algorithm/75")
    assert task_spec.editable_paths == (utility_dir,)
    assert task_spec.sync_paths == (utility_dir,)
    assert task_spec.required_output_paths == (utility_dir,)
    assert (roots.workspace_root / utility_dir / "Spec.dfy").is_file()
    assert not (roots.workspace_root / utility_dir / "cases.json").exists()
    assert not (roots.workspace_root / "task" / "formal_spec.dfy").exists()
    assert not (roots.workspace_root / "eval_support" / "dafny_by_method_layout.py").exists()
    for name in ("Algorithm75.dfy", "Core.dfy", "Proof.dfy"):
        shutil.copy2(REPO_ROOT / utility_dir / name, roots.workspace_root / utility_dir / name)

    completed = subprocess.run(
        ["bash", "eval_support/check_proof_layout.sh"],
        cwd=roots.workspace_root,
        text=True,
        capture_output=True,
        check=False,
    )

    assert completed.returncode == 0, completed.stderr


# Retry refreshes support scripts without erasing files on the candidate synchronization path.
def test_refresh_preserves_candidate_run_core_body(tmp_path: Path) -> None:
    task_inputs = _task_inputs(tmp_path, "algorithm-75")
    task_spec = _task_spec("algorithm-75")
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=task_inputs,
        task_spec=task_spec,
    )
    wrapper = roots.workspace_root / "bench/algorithm/75/Algorithm75.dfy"
    wrapper.write_text("// candidate implementation\n", encoding="utf-8")
    build_script = roots.workspace_root / "eval_support/build.sh"
    build_script.write_text("# stale support\n", encoding="utf-8")

    refresh_workspace_support_files(
        workspace_root=roots.workspace_root,
        task_input_layout=task_inputs,
        task_spec=task_spec,
    )

    assert wrapper.read_text(encoding="utf-8") == "// candidate implementation\n"
    assert build_script.read_text(encoding="utf-8") != "# stale support\n"


# The evaluator restores its own Dafny tests after overlaying candidate source files.
def test_evaluator_target_is_fresh_workspace_with_only_candidate_outputs(
    tmp_path: Path,
) -> None:
    task_spec = _task_spec("cat")
    task_inputs = _task_inputs(tmp_path, "cat")
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=task_inputs,
        task_spec=task_spec,
    )
    candidate_text = "module CatCore { method Candidate() {} }\n"
    (roots.workspace_root / "bench" / "utils" / "cat" / "CatCore.dfy").write_text(
        candidate_text,
        encoding="utf-8",
    )
    injected_test = roots.workspace_root / "tests" / "bench" / "test_bench_cat.py"
    injected_test.parent.mkdir(parents=True)
    injected_test.write_text("def test_fake(): assert True\n", encoding="utf-8")
    _capture_result, records = copy_candidate_outputs(
        workspace_root=roots.workspace_root,
        candidate_output_root=roots.candidate_output_root,
        task_spec=task_spec,
    )

    evaluator_target = prepare_evaluator_target(
        run_dir=tmp_path / "run",
        task_input_layout=task_inputs,
        task_spec=task_spec,
        candidate_output_root=roots.candidate_output_root,
        candidate_output_records=records,
    )

    assert (evaluator_target / "bench" / "utils" / "cat" / "CatCore.dfy").read_text(
        encoding="utf-8"
    ) == candidate_text
    assert not (evaluator_target / "tests" / "bench" / "test_bench_cat.py").exists()
    assert (evaluator_target / "bench" / "utils" / "cat" / "CatSchema.dfy").exists()
    assert (evaluator_target / "bench/utils/cat/Tests.dfy").read_bytes() == (
        REPO_ROOT / "bench/utils/cat/Tests.dfy"
    ).read_bytes()
    assert not (evaluator_target / "bench/utils/cat/Tests.py").exists()


# Candidate-created evaluator test paths fail output capture before they can be overlaid.
def test_candidate_cannot_capture_evaluator_only_utility_tests(tmp_path: Path) -> None:
    task_spec = _task_spec("cat")
    task_inputs = _task_inputs(tmp_path, "cat")
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=task_inputs,
        task_spec=task_spec,
    )
    injected = roots.workspace_root / "bench/utils/cat/Tests.dfy"
    injected.write_text("module FakeTests {}\n", encoding="utf-8")

    result, records = copy_candidate_outputs(
        workspace_root=roots.workspace_root,
        candidate_output_root=roots.candidate_output_root,
        task_spec=task_spec,
    )

    assert result.error is not None and "evaluator-only path" in result.error
    assert not any(record.captured for record in records)
    assert not (roots.candidate_output_root / "bench/utils/cat/Tests.dfy").exists()


def _populate_true_proof_workspace(workspace_root: Path) -> None:
    for source_name in ("TrueProof.dfy", "True.dfy", "TrueCore.dfy", "TrueCli.dfy"):
        target = workspace_root / "bench" / "utils" / "true" / source_name
        target.write_text(
            (REPO_ROOT / "bench" / "utils" / "true" / source_name).read_text(encoding="utf-8"),
            encoding="utf-8",
        )


# A fresh RunCore scaffold should build and report its unproved body as verification failure.
def test_proof_workspace_classifies_initial_body_failure(tmp_path: Path) -> None:
    task_spec = _task_spec("true")
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=_task_inputs(tmp_path, "true"),
        task_spec=task_spec,
    )

    verification = subprocess.run(
        ["bash", "eval_support/verify.sh"],
        cwd=roots.workspace_root,
        check=False,
        text=True,
        capture_output=True,
    )

    assert verification.returncode != 0
    assert (
        verification.stdout.count("DAFNY_VERIFICATION_OUTCOME=verification_failure phase=verify")
        == 1
    )


# The generated verifier must classify a missing workspace as build infrastructure failure.
def test_proof_workspace_classifies_missing_workspace_as_build_failure(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    task_spec = _task_spec("true")
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=_task_inputs(tmp_path, "true"),
        task_spec=task_spec,
    )
    monkeypatch.setenv("EVAL_WORKSPACE_DIR", str(tmp_path / "missing-workspace"))

    verification = subprocess.run(
        ["bash", "eval_support/verify.sh"],
        cwd=roots.workspace_root,
        check=False,
        text=True,
        capture_output=True,
    )

    assert verification.returncode != 0
    assert (
        verification.stdout.count("DAFNY_VERIFICATION_OUTCOME=infrastructure_failure phase=build")
        == 1
    )
    assert verification.stdout.count("DAFNY_VERIFICATION_OUTCOME") == 1


# The generated verifier reports missing installed checker modules as infrastructure failures.
def test_proof_workspace_classifies_missing_installed_checker_as_evidence_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    task_spec = _task_spec("true")
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=_task_inputs(tmp_path, "true"),
        task_spec=task_spec,
    )
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    python = bin_dir / "python3"
    python.write_text(f'#!/bin/sh\nexec "{sys.executable}" -S "$@"\n', encoding="utf-8")
    python.chmod(0o755)
    monkeypatch.setenv("PATH", f"{bin_dir}:{os.environ['PATH']}")

    verification = subprocess.run(
        ["bash", "eval_support/verify.sh"],
        cwd=roots.workspace_root,
        check=False,
        text=True,
        capture_output=True,
    )

    assert verification.returncode != 0
    assert (
        verification.stdout.count(
            "DAFNY_VERIFICATION_OUTCOME=infrastructure_failure phase=evidence"
        )
        == 1
    )
    assert verification.stdout.count("DAFNY_VERIFICATION_OUTCOME") == 1


# A verifier-trusted expect must fail before the verification rubric marker is emitted.
def test_proof_workspace_rejects_model_added_expect(tmp_path: Path) -> None:
    task_spec = _task_spec("true")
    roots = materialize_workspace_layout(
        run_dir=tmp_path / "run",
        task_input_layout=_task_inputs(tmp_path, "true"),
        task_spec=task_spec,
    )
    _populate_true_proof_workspace(roots.workspace_root)
    (roots.workspace_root / "bench" / "utils" / "true" / "Expected.dfy").write_text(
        "module Expected { method Invalid() { expect false; } }\n",
        encoding="utf-8",
    )

    verification = subprocess.run(
        ["bash", "eval_support/verify.sh"],
        cwd=roots.workspace_root,
        check=False,
        text=True,
        capture_output=True,
    )

    assert verification.returncode != 0
    assert (
        verification.stdout.count("DAFNY_VERIFICATION_OUTCOME=infrastructure_failure phase=build")
        == 1
    )
    assert "DAFNY_VERIFICATION_RESULT" not in verification.stdout


# Copying allowlisted repository paths should copy safe directories and reject invalid sources.
def test_copy_allowlisted_repo_subset_reports_invalid_sources(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    existing = repo_root / "agent" / "runner.py"
    existing.parent.mkdir()
    existing.write_text("# runner\n", encoding="utf-8")
    directory = repo_root / "agent" / "pkg"
    directory.mkdir()
    monkeypatch.setattr(benchmark_workspace, "REPO_ROOT", repo_root)

    destination = tmp_path / "workspace"
    benchmark_workspace._copy_allowlisted_repo_subset(destination, (Path("agent/runner.py"),))
    assert (destination / "agent" / "runner.py").read_text(encoding="utf-8") == "# runner\n"

    with pytest.raises(RuntimeError, match="escapes repository root"):
        benchmark_workspace._copy_allowlisted_repo_subset(destination, (Path("../outside.py"),))
    with pytest.raises(FileNotFoundError, match="workspace seed path missing"):
        benchmark_workspace._copy_allowlisted_repo_subset(destination, (Path("agent/missing.py"),))
    (directory / "helper.py").write_text("# helper\n", encoding="utf-8")
    benchmark_workspace._copy_allowlisted_repo_subset(destination, (Path("agent/pkg"),))
    assert (destination / "agent" / "pkg" / "helper.py").read_text(encoding="utf-8") == "# helper\n"


# Task seed copying should reject task escapes, workspace escapes, and missing seed files.
def test_copy_task_seed_files_reports_invalid_sources_and_targets(tmp_path: Path) -> None:
    workspace_root = tmp_path / "workspace"
    task_dir = tmp_path / "task"
    workspace_root.mkdir()
    task_dir.mkdir()
    (task_dir / "formal_spec.dfy").write_text("predicate Spec()\n", encoding="utf-8")

    benchmark_workspace._copy_task_seed_files(
        workspace_root=workspace_root,
        task_dir=task_dir,
        task_seed_files=((Path("bench/utils/cat/CatSpec.dfy"), Path("formal_spec.dfy")),),
    )
    assert (workspace_root / "bench" / "utils" / "cat" / "CatSpec.dfy").is_file()

    with pytest.raises(RuntimeError, match="escapes task input root"):
        benchmark_workspace._copy_task_seed_files(
            workspace_root=workspace_root,
            task_dir=task_dir,
            task_seed_files=((Path("out.dfy"), Path("../outside.dfy")),),
        )
    with pytest.raises(RuntimeError, match="escapes workspace root"):
        benchmark_workspace._copy_task_seed_files(
            workspace_root=workspace_root,
            task_dir=task_dir,
            task_seed_files=((Path("../out.dfy"), Path("formal_spec.dfy")),),
        )
    with pytest.raises(FileNotFoundError, match="task seed file missing"):
        benchmark_workspace._copy_task_seed_files(
            workspace_root=workspace_root,
            task_dir=task_dir,
            task_seed_files=((Path("out.dfy"), Path("missing.dfy")),),
        )


# Generated and placeholder files should reject paths that escape the sandbox workspace.
def test_generated_and_placeholder_paths_reject_workspace_escapes(tmp_path: Path) -> None:
    workspace_root = tmp_path / "workspace"
    workspace_root.mkdir()

    benchmark_workspace._write_generated_files(
        workspace_root=workspace_root,
        generated_files=((Path("eval_support/check.sh"), "#!/usr/bin/env bash\ntrue\n"),),
    )
    benchmark_workspace._apply_hidden_and_placeholder_paths(
        workspace_root=workspace_root,
        hidden_paths=(Path("hidden.txt"),),
        placeholder_paths=(Path("bench/utils/cat/CatCore.dfy"),),
    )

    assert (workspace_root / "eval_support" / "check.sh").stat().st_mode & 0o111
    assert "Agent-editable scaffold" in (
        workspace_root / "bench" / "utils" / "cat" / "CatCore.dfy"
    ).read_text(encoding="utf-8")
    with pytest.raises(RuntimeError, match="generated file escapes"):
        benchmark_workspace._write_generated_files(
            workspace_root=workspace_root,
            generated_files=((Path("../escape.sh"), "bad"),),
        )
    with pytest.raises(RuntimeError, match="placeholder path escapes"):
        benchmark_workspace._apply_hidden_and_placeholder_paths(
            workspace_root=workspace_root,
            hidden_paths=(),
            placeholder_paths=(Path("../escape.dfy"),),
        )


# Workspace support refresh should reject invalid repository and task support inputs.
def test_refresh_workspace_support_files_reports_invalid_support_inputs(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    repo_root = tmp_path / "repo"
    repo_root.mkdir()
    support_dir = repo_root / "support_dir"
    support_dir.mkdir()
    task_dir = tmp_path / "task"
    task_dir.mkdir()
    task_input_layout = SimpleNamespace(task_dir=task_dir)

    def spec(**overrides):  # noqa: ANN003
        values = {
            "copied_paths": (),
            "task_seed_files": (),
            "editable_paths": (),
            "sync_paths": (),
            "generated_files": (),
        }
        values.update(overrides)
        return SimpleNamespace(**values)

    monkeypatch.setattr(benchmark_workspace, "REPO_ROOT", repo_root)

    with pytest.raises(FileNotFoundError, match="workspace support path missing"):
        benchmark_workspace.refresh_workspace_support_files(
            workspace_root=tmp_path / "workspace",
            task_input_layout=task_input_layout,
            task_spec=spec(copied_paths=(Path("missing.py"),)),
        )
    with pytest.raises(IsADirectoryError, match="workspace support path must be a file"):
        benchmark_workspace.refresh_workspace_support_files(
            workspace_root=tmp_path / "workspace",
            task_input_layout=task_input_layout,
            task_spec=spec(copied_paths=(Path("support_dir"),)),
        )
    with pytest.raises(FileNotFoundError, match="task support file missing"):
        benchmark_workspace.refresh_workspace_support_files(
            workspace_root=tmp_path / "workspace",
            task_input_layout=task_input_layout,
            task_spec=spec(
                task_seed_files=((Path("bench/utils/cat/CatSpec.dfy"), Path("missing.dfy")),),
            ),
        )
