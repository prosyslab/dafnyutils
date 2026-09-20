"""Capture candidate output artifacts and enforce fixed-file integrity before overlaying them."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from evaluation.enums import CandidateOutputEntryType
from evaluation.models import (
    CandidateOutputCaptureResultModel,
    CandidateOutputRecordModel,
    CandidateOutputTreeEntryKind,
    CandidateOutputTreeEntryModel,
)
from evaluation.runtime import sha256_hex
from runtime.filesystem import (
    copy_entry,
    copy_tree_within_root,
    path_within_root,
    remove_entry,
    safe_relative_path,
)


def _workspace_baseline_path(roots: Any) -> Path:
    return roots.sandbox_root / "workspace_baseline.json"


def _directory_tree_manifest(root: Path) -> tuple[list[CandidateOutputTreeEntryModel], str]:
    if root.is_symlink() or not root.is_dir():
        raise ValueError(f"source tree must be a directory: {root}")

    root_resolved = root.resolve()
    entries: list[CandidateOutputTreeEntryModel] = []
    for candidate in sorted(root.rglob("*"), key=lambda path: path.relative_to(root).as_posix()):
        relative_path = candidate.relative_to(root).as_posix()
        if candidate.is_symlink():
            try:
                candidate.resolve(strict=False).relative_to(root_resolved)
            except (OSError, RuntimeError, ValueError) as error:
                raise ValueError(f"unsafe symlink in source tree: {candidate}") from error
            entries.append(
                CandidateOutputTreeEntryModel(
                    path=relative_path,
                    kind=CandidateOutputTreeEntryKind.SYMLINK,
                    link_target=str(candidate.readlink()),
                )
            )
        elif candidate.is_file():
            payload = candidate.read_bytes()
            entries.append(
                CandidateOutputTreeEntryModel(
                    path=relative_path,
                    kind=CandidateOutputTreeEntryKind.FILE,
                    bytes=len(payload),
                    sha256=sha256_hex(payload),
                )
            )
        elif candidate.is_dir():
            entries.append(
                CandidateOutputTreeEntryModel(
                    path=relative_path,
                    kind=CandidateOutputTreeEntryKind.DIRECTORY,
                )
            )

    payload = json.dumps(
        [entry.model_dump(mode="json", exclude_none=True) for entry in entries],
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    return entries, sha256_hex(payload)


def write_workspace_baseline(roots: Any, task_spec: Any) -> None:
    baseline: list[dict[str, Any]] = []
    tracked_paths = tuple(
        dict.fromkeys(
            (
                *task_spec.required_output_paths,
                *getattr(task_spec, "read_only_paths", ()),
            )
        )
    )
    for rel_path in tracked_paths:
        source = roots.workspace_root / rel_path
        record: dict[str, Any] = {"path": str(rel_path)}
        if source.is_file():
            payload = source.read_bytes()
            record.update({"kind": "file", "sha256": sha256_hex(payload), "bytes": len(payload)})
        elif source.is_dir():
            tree_manifest, tree_sha256 = _directory_tree_manifest(source)
            record.update(
                {
                    "kind": "directory",
                    "tree_manifest": [
                        entry.model_dump(mode="json", exclude_none=True) for entry in tree_manifest
                    ],
                    "tree_sha256": tree_sha256,
                }
            )
        else:
            record["kind"] = "missing"
        baseline.append(record)
    _workspace_baseline_path(roots).write_text(
        json.dumps(baseline, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _load_workspace_baseline(workspace_root: Path) -> dict[Path, dict[str, Any]]:
    baseline_path = workspace_root.parent / "workspace_baseline.json"
    if not baseline_path.exists():
        return {}
    with baseline_path.open("r", encoding="utf-8") as f:
        raw = json.load(f)
    baseline: dict[Path, dict[str, Any]] = {}
    if not isinstance(raw, list):
        return baseline
    for item in raw:
        if not isinstance(item, dict):
            continue
        path = safe_relative_path(item.get("path"))
        if path is not None:
            baseline[path] = item
    return baseline


def _read_only_path_unchanged(source: Path, baseline_record: dict[str, Any]) -> bool:
    if source.is_file() and not source.is_symlink():
        payload = source.read_bytes()
        return (
            baseline_record.get("kind") == "file"
            and baseline_record.get("sha256") == sha256_hex(payload)
            and baseline_record.get("bytes") == len(payload)
        )
    return not source.exists() and baseline_record.get("kind") == "missing"


def _read_only_capture_violations(
    *,
    workspace_root: Path,
    baseline: dict[Path, dict[str, Any]],
    read_only_paths: tuple[Path, ...],
) -> tuple[list[str], list[CandidateOutputRecordModel]]:
    messages: list[str] = []
    records: list[CandidateOutputRecordModel] = []
    for rel_path in read_only_paths:
        source = workspace_root / rel_path
        baseline_record = baseline.get(rel_path)
        if baseline_record is None:
            message = f"read-only path has no workspace baseline: {rel_path}"
        elif _read_only_path_unchanged(source, baseline_record):
            continue
        else:
            message = f"read-only path changed in sandbox workspace: {rel_path}"
        messages.append(message)
        records.append(
            CandidateOutputRecordModel(
                path=str(rel_path),
                source=str(source),
                captured=False,
                changed_from_baseline=True,
                error=message,
            )
        )
    return messages, records


def _unavailable_output_record(source: Path, rel_path: Path) -> CandidateOutputRecordModel | None:
    if source.is_symlink():
        error = "selected output root must not be a symlink"
    elif not source.exists():
        error = "required output missing from sandbox workspace"
    else:
        return None
    return CandidateOutputRecordModel(
        path=str(rel_path),
        source=str(source),
        captured=False,
        entry_type=CandidateOutputEntryType.MISSING,
        error=error,
    )


def copy_candidate_outputs(
    *,
    workspace_root: Path,
    candidate_output_root: Path,
    task_spec: Any,
) -> tuple[CandidateOutputCaptureResultModel, list[CandidateOutputRecordModel]]:
    candidate_output_root.mkdir(parents=True, exist_ok=True)
    baseline = _load_workspace_baseline(workspace_root)
    placeholder_paths = {Path(path) for path in getattr(task_spec, "placeholder_paths", ())}
    hidden_paths = tuple(Path(path) for path in getattr(task_spec, "hidden_paths", ()))
    records: list[CandidateOutputRecordModel] = []
    captured_paths: list[str] = []
    hidden_violations: list[str] = []

    for rel_path in task_spec.sync_paths:
        source = workspace_root / rel_path
        target = candidate_output_root / rel_path
        present_hidden = tuple(
            path
            for path in hidden_paths
            if path.is_relative_to(rel_path)
            and ((workspace_root / path).exists() or (workspace_root / path).is_symlink())
        )
        if present_hidden:
            remove_entry(target)
            message = "evaluator-only path in candidate output: " + ", ".join(
                str(path) for path in present_hidden
            )
            hidden_violations.append(message)
            records.append(
                CandidateOutputRecordModel(
                    path=str(rel_path),
                    source=str(source),
                    captured=False,
                    error=message,
                )
            )
            continue
        if not path_within_root(source, workspace_root):
            records.append(
                CandidateOutputRecordModel(
                    path=str(rel_path),
                    source=str(source),
                    captured=False,
                    error="source path escapes workspace root",
                )
            )
            continue

        unavailable = _unavailable_output_record(source, rel_path)
        if unavailable is not None:
            records.append(unavailable)
            continue

        baseline_record = baseline.get(rel_path, {})
        try:
            if source.is_file():
                payload = source.read_bytes()
                sha256 = sha256_hex(payload)
                changed_from_baseline = baseline_record.get("sha256") != sha256
                size_bytes = len(payload)
                entry_type = CandidateOutputEntryType.FILE
                tree_manifest = None
                tree_sha256 = None
            else:
                tree_manifest, tree_sha256 = _directory_tree_manifest(source)
                sha256 = None
                changed_from_baseline = (
                    baseline_record.get("tree_sha256") != tree_sha256
                    if "tree_sha256" in baseline_record
                    else True
                )
                size_bytes = None
                entry_type = CandidateOutputEntryType.DIRECTORY
        except ValueError as error:
            records.append(
                CandidateOutputRecordModel(
                    path=str(rel_path),
                    source=str(source),
                    captured=False,
                    entry_type=CandidateOutputEntryType.MISSING,
                    error=str(error),
                )
            )
            continue

        if rel_path in placeholder_paths and not changed_from_baseline:
            records.append(
                CandidateOutputRecordModel(
                    path=str(rel_path),
                    source=str(source),
                    captured=False,
                    changed_from_baseline=False,
                    entry_type=CandidateOutputEntryType.MISSING,
                    error="required output unchanged from placeholder scaffold",
                )
            )
            continue

        try:
            remove_entry(target)
            if source.is_dir() and not source.is_symlink():
                copy_tree_within_root(source, target)
            else:
                copy_entry(source, target)
        except ValueError as error:
            records.append(
                CandidateOutputRecordModel(
                    path=str(rel_path),
                    source=str(source),
                    captured=False,
                    entry_type=CandidateOutputEntryType.MISSING,
                    error=str(error),
                )
            )
            continue

        captured_paths.append(str(rel_path))
        records.append(
            CandidateOutputRecordModel(
                path=str(rel_path),
                source=str(source),
                stored_at=str(target),
                captured=True,
                changed_from_baseline=changed_from_baseline,
                entry_type=entry_type,
                bytes=size_bytes,
                sha256=sha256,
                tree_manifest=tree_manifest,
                tree_sha256=tree_sha256,
            )
        )

    read_only_violations, read_only_records = _read_only_capture_violations(
        workspace_root=workspace_root,
        baseline=baseline,
        read_only_paths=tuple(getattr(task_spec, "read_only_paths", ())),
    )
    records.extend(read_only_records)
    manifest_path = candidate_output_root / "candidate_outputs.json"
    manifest_path.write_text(
        json.dumps(
            [record.model_dump(mode="json") for record in records],
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    result = CandidateOutputCaptureResultModel(
        attempted=True,
        copied=any(record.captured for record in records),
        captured_paths=captured_paths,
        manifest_path=str(manifest_path),
        error="; ".join((*hidden_violations, *read_only_violations)) or None,
    )
    return result, records


def overlay_candidate_outputs(
    *,
    candidate_output_root: Path,
    evaluator_checkout_root: Path,
    records: list[CandidateOutputRecordModel],
) -> None:
    for record in records:
        rel_path = safe_relative_path(record.path)
        if rel_path is None:
            continue
        target = evaluator_checkout_root / rel_path
        if record.entry_type == CandidateOutputEntryType.MISSING:
            remove_entry(target)
            continue
        if not record.captured:
            continue
        source = candidate_output_root / rel_path
        if source.is_symlink():
            if not path_within_root(source, candidate_output_root):
                raise ValueError(f"candidate source path escapes candidate output root: {rel_path}")
            raise ValueError(f"candidate source root must not be a symlink: {rel_path}")
        if not source.exists():
            continue
        if not path_within_root(source, candidate_output_root):
            raise ValueError(f"candidate source path escapes candidate output root: {rel_path}")
        remove_entry(target)
        if source.is_dir():
            copy_tree_within_root(source, target)
        else:
            copy_entry(source, target)
