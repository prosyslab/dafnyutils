"""Black-box contracts for public release publication and restoration."""

import subprocess
from dataclasses import replace
from pathlib import Path

import pytest

import benchmarks.generated_profile as generated_profile
import evaluation.task.release as release_module
from benchmarks.task import TaskProfile
from evaluation.task.release import load_release, prepare_release, publish_release


# Publication reuses one source analysis to publish runnable public inputs without oracle data.
def test_public_release_contains_only_public_material(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    analyzed_tasks = []
    analyze = generated_profile.analyze_task_entry_contract

    def record_analysis(configuration, task_id, **kwargs):
        analyzed_tasks.append(task_id)
        return analyze(configuration, task_id, **kwargs)

    monkeypatch.setattr(generated_profile, "analyze_task_entry_contract", record_analysis)
    release = tmp_path / "release"
    manifest = publish_release(("algorithm-1",), release)
    assert analyzed_tasks == ["algorithm-1"]
    assert "bench/algorithm/1/cases.json" not in manifest.files
    assert not any("answer" in Path(p).parts or "tests" in Path(p).parts for p in manifest.files)
    assert "bench/algorithm/1/Spec.dfy" in manifest.fixed_files
    assert "bench/algorithm/1/Core.dfy" not in manifest.fixed_files
    assert "bench/algorithm/1/dfyconfig.toml" in manifest.fixed_files
    assert not any(
        path.endswith(".py") and path.startswith("eval_support/") for path in manifest.files
    )
    assert not any(path.startswith("tasks/algorithm-1/bench/") for path in manifest.files)
    restored = prepare_release(release, tmp_path / "workspace")
    task = restored.tasks["algorithm-1"]
    public = TaskProfile.from_json_file(task.input_layout.task_path)
    assert public.public_checks[0].argv == ("./eval_support/algorithm-1/verify.sh",)
    assert restored.release_id == manifest.release_id
    assert (restored.workspace / public.public_checks[0].argv[0]).is_file()
    checker = restored.workspace / "eval_support/algorithm-1/verify.sh"
    assert checker.stat().st_mode & 0o777 == 0o755
    layout_check = subprocess.run(
        ["bash", "eval_support/algorithm-1/check_proof_layout.sh"],
        cwd=restored.workspace,
        text=True,
        capture_output=True,
        check=False,
    )
    assert layout_check.returncode == 0, layout_check.stdout + layout_check.stderr


# Mutating a canonical release file is rejected before preparation.
def test_release_rejects_corrupted_canonical_material(tmp_path: Path) -> None:
    release = tmp_path / "release"
    publish_release(("algorithm-1",), release)
    (release / "workspace/bench/algorithm/1/Spec.dfy").write_text("altered", encoding="utf-8")
    with pytest.raises(ValueError, match="integrity mismatch"):
        load_release(release)


# Multiple public tasks coexist with separate task-specific checkers.
def test_release_restores_multiple_tasks(tmp_path: Path) -> None:
    release = tmp_path / "release"
    manifest = publish_release(("algorithm-1", "algorithm-4"), release)
    restored = prepare_release(release, tmp_path / "workspace")
    assert tuple(restored.tasks) == manifest.task_ids
    assert manifest.task_roots == ("bench/algorithm/1", "bench/algorithm/4")
    for task_id in manifest.task_ids:
        assert (restored.workspace / "eval_support" / task_id / "verify.sh").is_file()


# A changed shared source between tasks cannot silently overwrite the first published copy.
def test_public_release_rejects_shared_file_conflict(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    original = release_module.task_workspace_spec

    def changed_second_task(**kwargs):  # noqa: ANN003, ANN202
        spec = original(**kwargs)
        if kwargs["utility_name"] != "algorithm-4":
            return spec
        return replace(
            spec,
            generated_files=tuple(
                (path, content + "\n" if path == Path("bench/core/Functional.dfy") else content)
                for path, content in spec.generated_files
            ),
        )

    monkeypatch.setattr(release_module, "task_workspace_spec", changed_second_task)
    release = tmp_path / "release"
    with pytest.raises(ValueError, match="public task releases conflict"):
        publish_release(("algorithm-1", "algorithm-4"), release)
    assert not release.exists()


# A linked source cannot escape the reviewed public file selection.
def test_public_release_rejects_linked_source(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    repository = tmp_path / "repository"
    repository.mkdir()
    (repository / "linked.txt").symlink_to(tmp_path / "private.txt")
    (tmp_path / "private.txt").write_text("private\n", encoding="utf-8")
    monkeypatch.setattr(release_module, "REPO_ROOT", repository)

    with pytest.raises(ValueError, match="escapes repository root|contains symlink"):
        release_module._source_file(Path("linked.txt"))
