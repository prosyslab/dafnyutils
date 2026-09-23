"""Publish public task bundles and verify their manifests and fixed-file hashes.

Release authors call publish_release/prepare_release. evaluation.submission.api,
evaluation.submission.archive, and evaluation.submission.workspace consume the contract to evaluate
archives against the same public inputs without consulting authoring answers.
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import tempfile
from dataclasses import dataclass
from enum import StrEnum
from pathlib import Path

from pydantic import Field, field_validator, model_validator

from benchmarks.generated_profile import GeneratedTaskProfile
from benchmarks.paths import REPO_ROOT
from benchmarks.profiles import ResolvedBenchmark
from benchmarks.repository import BenchmarkRepository
from benchmarks.task import TaskModel, TaskProfile, TaskResourceKind, validate_relative_path
from benchmarks.validation import load_validated_benchmark
from entry_contract import DafnyEntry as AnalyzedDafnyEntry
from entry_contract import analyze_entry_contract, entry_contract_source_snapshot
from evaluation.task.preparation import PreparedTask, TaskInputLayout, prepare_task
from evaluation.task.specification_source import PLACEHOLDER_FILE_CONTENT
from evaluation.task.workspace import TaskWorkspaceSpec, task_workspace_spec
from runtime.filesystem import ignore_python_cache


class ReleaseSchemaVersion(StrEnum):
    V1 = "benchmark.public-release.v1"


class ArchiveLimits(TaskModel):
    compressed_bytes: int = Field(default=64 * 1024 * 1024, gt=0)
    expanded_bytes: int = Field(default=256 * 1024 * 1024, gt=0)
    file_bytes: int = Field(default=32 * 1024 * 1024, gt=0)
    entries: int = Field(default=10000, gt=0)


class ReleasedTask(TaskModel):
    task_id: str
    task_root: str
    profile: TaskProfile
    required_outputs: tuple[str, ...]
    placeholder_paths: tuple[str, ...]

    @field_validator("task_root")
    @classmethod
    def _root(cls, value: str) -> str:
        return validate_relative_path(value)


class TaskReleaseManifest(TaskModel):
    schema_version: ReleaseSchemaVersion = ReleaseSchemaVersion.V1
    release_id: str
    task_ids: tuple[str, ...]
    task_roots: tuple[str, ...]
    excluded_names: tuple[str, ...] = (
        ".git",
        "__pycache__",
        ".pytest_cache",
        ".ruff_cache",
        "_build",
        "bin",
        "obj",
    )
    excluded_paths: tuple[str, ...] = ()
    limits: ArchiveLimits = Field(default_factory=ArchiveLimits)
    tasks: dict[str, ReleasedTask]
    files: dict[str, str]
    fixed_files: dict[str, str]

    @model_validator(mode="after")
    def _contract(self) -> TaskReleaseManifest:
        if not self.task_ids or len(set(self.task_ids)) != len(self.task_ids):
            raise ValueError("release task_ids must be nonempty and unique")
        if set(self.tasks) != set(self.task_ids):
            raise ValueError("release tasks must match task_ids")
        if self.task_roots != tuple(self.tasks[t].task_root for t in self.task_ids):
            raise ValueError("release task_roots must match task metadata")
        for path in (*self.files, *self.fixed_files, *self.excluded_paths):
            validate_relative_path(path)
        if any(self.files.get(path) != digest for path, digest in self.fixed_files.items()):
            raise ValueError("fixed files must match released file hashes")
        for task_id, task in self.tasks.items():
            if task.task_id != task_id or task.profile.task_id != task_id:
                raise ValueError("released task identity mismatch")
            if task.task_root != task.profile.dafny.utility_root:
                raise ValueError("released task root mismatch")
            _validate_released_resources(task, self.files)
        if self.release_id != release_digest(self):
            raise ValueError("release manifest identity mismatch")
        return self


def _validate_released_resources(task: ReleasedTask, files: dict[str, str]) -> None:
    if any(resource.path not in files for resource in task.profile.resources):
        raise ValueError("released task resource is missing from public files")


def release_digest(manifest: TaskReleaseManifest) -> str:
    payload = manifest.model_dump(mode="json", exclude={"release_id"})
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


@dataclass(frozen=True)
class PreparedReleaseTask:
    task_id: str
    run_directory: Path
    workspace: Path
    input_layout: TaskInputLayout
    workspace_spec: TaskWorkspaceSpec
    configuration: ResolvedBenchmark


@dataclass(frozen=True)
class PreparedRelease:
    release_id: str
    manifest: TaskReleaseManifest
    workspace: Path
    tasks: dict[str, PreparedReleaseTask]


@dataclass(frozen=True)
class _PublicFile:
    content: bytes
    mode: int


def publish_release(task_ids: tuple[str, ...], directory: Path) -> TaskReleaseManifest:
    """Author a new public release, without copying answers or evaluator data."""
    if not task_ids or len(set(task_ids)) != len(task_ids):
        raise ValueError("task_ids must be nonempty and unique")
    directory.parent.mkdir(parents=True, exist_ok=True)
    if directory.exists() or directory.is_symlink():
        raise FileExistsError(directory)
    with tempfile.TemporaryDirectory(
        prefix="dafnyutils-release-", dir=directory.parent
    ) as temporary:
        staged = Path(temporary) / "release"
        public = staged / "workspace"
        public.mkdir(parents=True)
        metadata: dict[str, ReleasedTask] = {}
        mutable: set[str] = set()
        evaluator_only: set[str] = set()
        published_files: dict[Path, _PublicFile] = {}
        repository = BenchmarkRepository.open(REPO_ROOT)
        for task_id in task_ids:
            validated = load_validated_benchmark(repository, task_id)
            cfg = validated.configuration
            prepared = prepare_task(
                utility_cfg=cfg,
                utility_name=task_id,
                validated_profile=validated.profile,
            )
            spec = task_workspace_spec(
                utility_cfg=cfg,
                utility_name=task_id,
                task=prepared.profile,
                prepared_task=prepared,
                public_task_id=task_id,
            )
            profile = _public_profile(prepared.profile, task_id)
            task_files = _public_task_files(spec, prepared, profile)
            _write_public_files(public, task_files, published_files)
            prepared.validate_source_identity(repository_root=REPO_ROOT)
            metadata[task_id] = ReleasedTask(
                task_id=task_id,
                task_root=profile.dafny.utility_root,
                profile=profile,
                required_outputs=tuple(str(p) for p in spec.required_output_paths),
                placeholder_paths=tuple(str(p) for p in spec.placeholder_paths),
            )
            mutable.update(str(p) for p in spec.required_output_paths)
            evaluator_only.update(str(p) for p in spec.hidden_paths)
        files = {
            p.relative_to(public).as_posix(): _hash(p)
            for p in sorted(public.rglob("*"))
            if p.is_file()
        }
        fixed = {
            p: h
            for p, h in files.items()
            if not any(Path(p).is_relative_to(Path(m)) for m in mutable)
        }
        provisional = TaskReleaseManifest.model_construct(
            schema_version=ReleaseSchemaVersion.V1,
            release_id="",
            task_ids=task_ids,
            task_roots=tuple(metadata[t].task_root for t in task_ids),
            tasks=metadata,
            files=files,
            fixed_files=fixed,
            excluded_paths=tuple(sorted(evaluator_only)),
        )
        manifest = TaskReleaseManifest.model_validate(
            provisional.model_dump(mode="python") | {"release_id": release_digest(provisional)}
        )
        manifest.to_json_file(staged / "manifest.json")
        staged.rename(directory)
        return manifest


def _public_profile(profile: TaskProfile, task_id: str) -> TaskProfile:
    checks = tuple(
        check.model_copy(
            update={
                "argv": tuple(
                    arg.replace("eval_support/", f"eval_support/{task_id}/") for arg in check.argv
                )
            }
        )
        for check in profile.public_checks
    )
    return profile.model_copy(update={"public_checks": checks})


def _public_file(path: Path, content: bytes) -> _PublicFile:
    return _PublicFile(content, 0o755 if path.suffix == ".sh" else 0o644)


def _source_path(path: Path) -> Path:
    validate_relative_path(path.as_posix())
    root = REPO_ROOT.resolve()
    source = REPO_ROOT / path
    if not source.resolve().is_relative_to(root):
        raise ValueError(f"public source escapes repository root: {path}")
    current = REPO_ROOT
    for part in path.parts:
        current /= part
        if current.is_symlink():
            raise ValueError(f"public release contains symlink: {current}")
    return source


def _source_file(path: Path) -> bytes:
    source = _source_path(path)
    if not source.is_file():
        raise ValueError(f"public release source must be a regular file: {source}")
    return source.read_bytes()


def _source_paths(path: Path) -> tuple[Path, ...]:
    source = _source_path(path)
    if source.is_file():
        return (path,)
    if not source.is_dir():
        raise FileNotFoundError(f"workspace seed path missing: {path}")
    found: list[Path] = []
    for directory, directory_names, file_names in os.walk(source, followlinks=False):
        ignored = ignore_python_cache(directory, [*directory_names, *file_names])
        directory_names[:] = sorted(name for name in directory_names if name not in ignored)
        for name in [*directory_names, *sorted(file_names)]:
            if name in ignored:
                continue
            candidate = Path(directory) / name
            if candidate.is_symlink():
                raise ValueError(f"public release contains symlink: {candidate}")
            if candidate.is_file():
                found.append(candidate.relative_to(REPO_ROOT))
            elif not candidate.is_dir():
                raise ValueError(f"public release contains special file: {candidate}")
    return tuple(found)


def _add_public_source_files(
    files: dict[Path, _PublicFile], spec: TaskWorkspaceSpec, prepared: PreparedTask
) -> set[Path]:
    for copied in spec.copied_paths:
        for path in _source_paths(copied):
            files[path] = _public_file(path, _source_file(path))
    seeded = {workspace_path for workspace_path, _ in spec.task_seed_files}
    resources = {Path(resource.path) for resource in prepared.profile.resources}
    for workspace_path, task_path in spec.task_seed_files:
        if task_path not in resources:
            raise FileNotFoundError(f"task seed file missing: {task_path}")
        files[workspace_path] = _public_file(workspace_path, _source_file(task_path))
    return seeded


def _add_declared_resources(
    files: dict[Path, _PublicFile], spec: TaskWorkspaceSpec, profile: TaskProfile
) -> None:
    generated_paths = {path for path, _ in spec.generated_files}
    for resource in profile.resources:
        path = Path(resource.path)
        if any(path.is_relative_to(hidden) for hidden in spec.hidden_paths):
            raise ValueError(f"public task resource is evaluator-only: {path}")
        if resource.kind is TaskResourceKind.FORMAL_SPECIFICATION:
            if path not in generated_paths:
                raise ValueError(f"public formal resource has no generated source: {path}")
        elif path not in files:
            files[path] = _public_file(path, _source_file(path))


def _public_task_files(
    spec: TaskWorkspaceSpec, prepared: PreparedTask, profile: TaskProfile
) -> dict[Path, _PublicFile]:
    task_id = profile.task_id
    files: dict[Path, _PublicFile] = {}
    seeded = _add_public_source_files(files, spec, prepared)
    for hidden in spec.hidden_paths:
        files = {path: item for path, item in files.items() if not path.is_relative_to(hidden)}
    for placeholder in spec.placeholder_paths:
        if placeholder not in seeded:
            files[placeholder] = _public_file(placeholder, PLACEHOLDER_FILE_CONTENT.encode("utf-8"))
    for path, content in spec.generated_files:
        files[path] = _public_file(path, content.encode("utf-8"))
    _add_declared_resources(files, spec, profile)
    task_path = Path("tasks") / task_id / "task.json"
    if task_path in files:
        raise ValueError("task resource path collides with task.json")
    files[task_path] = _public_file(
        task_path, (profile.model_dump_json(indent=2) + "\n").encode("utf-8")
    )
    return files


def _write_public_files(
    destination: Path,
    task_files: dict[Path, _PublicFile],
    published_files: dict[Path, _PublicFile],
) -> None:
    for relative, item in sorted(task_files.items()):
        validate_relative_path(relative.as_posix())
        if any(parent in published_files for parent in relative.parents if parent != Path(".")):
            raise ValueError(f"public task releases conflict: {relative}")
        if relative in published_files:
            if published_files[relative] != item:
                raise ValueError(f"public task releases conflict: {relative}")
            continue
        if any(path.is_relative_to(relative) for path in published_files):
            raise ValueError(f"public task releases conflict: {relative}")
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(item.content)
        target.chmod(item.mode)
        published_files[relative] = item


def load_release(directory: Path) -> TaskReleaseManifest:
    """Verify the trusted release's complete public tree against its manifest."""
    manifest = TaskReleaseManifest.from_json_file(directory / "manifest.json")
    public = directory / "workspace"
    if public.is_symlink() or not public.is_dir():
        raise ValueError("public release workspace must be a regular directory")
    actual: dict[str, str] = {}
    for path in public.rglob("*"):
        if path.is_symlink() or not (path.is_dir() or path.is_file()):
            raise ValueError(f"unsupported release entry: {path}")
        if path.is_file():
            actual[path.relative_to(public).as_posix()] = _hash(path)
    if actual != manifest.files:
        raise ValueError("public release file integrity mismatch")
    return manifest


def prepare_release(release_directory: Path, workspace: Path) -> PreparedRelease:
    """Prepare all public tasks without consulting the authoring answer sources."""
    manifest = load_release(release_directory)
    workspace.mkdir(parents=True, exist_ok=False)
    shutil.copytree(release_directory / "workspace", workspace, dirs_exist_ok=True)
    tasks = {
        task_id: released_task(manifest, task_id, workspace.parent / "tasks" / task_id, workspace)
        for task_id in manifest.task_ids
    }
    return PreparedRelease(manifest.release_id, manifest, workspace, tasks)


def released_task(
    manifest: TaskReleaseManifest, task_id: str, run_directory: Path, workspace: Path
) -> PreparedReleaseTask:
    """Recover the minimal evaluator contract solely from public release metadata."""
    metadata = manifest.tasks[task_id]
    profile = metadata.profile
    analysis = analyze_entry_contract(
        workspace,
        workspace / metadata.task_root,
        AnalyzedDafnyEntry(
            profile.dafny.execution_entry.source_path, profile.dafny.execution_entry.symbol
        ),
        tuple(
            workspace / p
            for p in manifest.fixed_files
            if p.startswith("bench/core/") and p.endswith(".dfy")
        ),
    )
    snapshot = entry_contract_source_snapshot(
        workspace,
        workspace / metadata.task_root,
        analysis.manifest,
        additional_sources=analysis.analysis_sources,
    )
    prepared = PreparedTask(GeneratedTaskProfile(profile, analysis), snapshot)
    task_path = workspace / "tasks" / task_id / "task.json"
    layout = TaskInputLayout(
        task_dir=task_path.parent,
        task_path=task_path,
        visible_artifacts={r.resource_id: workspace / r.path for r in profile.resources},
        prepared_task=prepared,
    )
    fixed = tuple(Path(p) for p in manifest.fixed_files)
    outputs = tuple(Path(p) for p in metadata.required_outputs)
    spec = TaskWorkspaceSpec(
        task_id,
        Path(metadata.task_root),
        (),
        (),
        (),
        tuple(
            Path(path)
            for path in manifest.excluded_paths
            if Path(path).is_relative_to(Path(metadata.task_root))
        ),
        tuple(Path(p) for p in metadata.placeholder_paths),
        tuple(Path(p) for p in profile.workspace.editable_paths),
        outputs,
        outputs,
        fixed,
    )
    return PreparedReleaseTask(
        task_id, run_directory, workspace, layout, spec, ResolvedBenchmark.for_task(task_id)
    )
