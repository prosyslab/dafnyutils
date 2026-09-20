"""Create intentionally incomplete benchmark contribution scaffolds."""

from __future__ import annotations

import shutil
from dataclasses import dataclass
from pathlib import Path

from .definition import (
    BenchmarkKind,
    benchmark_item_directory,
    class_name_for_task_id,
    validate_task_id,
)


@dataclass(frozen=True)
class ScaffoldResult:
    task_id: str
    directory: Path
    files: tuple[Path, ...]


def _class_name(task_id: str) -> str:
    return class_name_for_task_id(task_id)


def scaffold_benchmark(*, root: Path, kind: BenchmarkKind, task_id: str) -> ScaffoldResult:
    root = root.resolve()
    validate_task_id(task_id)
    directory = _scaffold_directory(root, kind, task_id)
    if not directory.resolve().is_relative_to(root):
        raise ValueError(f"benchmark directory escapes repository root: {directory}")
    if directory.exists():
        raise FileExistsError(f"benchmark directory already exists: {directory}")

    template_root = root / "tools" / "benchmark_templates" / kind.value
    if not template_root.is_dir():
        raise FileNotFoundError(f"benchmark template directory is missing: {template_root}")
    shutil.copytree(template_root, directory)
    created = _specialize_files(directory, task_id)
    return ScaffoldResult(task_id=task_id, directory=directory, files=created)


def _scaffold_directory(root: Path, kind: BenchmarkKind, task_id: str) -> Path:
    return root / benchmark_item_directory(kind, task_id)


def _specialize_files(directory: Path, task_id: str) -> tuple[Path, ...]:
    class_name = _class_name(task_id)
    replacements = {
        "{{TASK_ID}}": task_id,
        "{{CLASS_NAME}}": class_name,
    }
    rename_map = {
        "Description.md": f"{task_id}.md",
        "UtilitySchema.dfy": f"{class_name}Schema.dfy",
        "UtilitySpec.dfy": f"{class_name}Spec.dfy",
        "UtilityCore.dfy": f"{class_name}Core.dfy",
        "UtilityProof.dfy": f"{class_name}Proof.dfy",
        "Utility.dfy": f"{class_name}.dfy",
        "UtilityCli.dfy": f"{class_name}Cli.dfy",
        "Algorithm.dfy": f"{class_name}.dfy",
    }
    for source_name, destination_name in rename_map.items():
        source = directory / source_name
        if source.exists():
            source.rename(directory / destination_name)

    created: list[Path] = []
    for path in sorted(directory.iterdir()):
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        for marker, replacement in replacements.items():
            text = text.replace(marker, replacement)
        path.write_text(text, encoding="utf-8")
        created.append(path)
    return tuple(created)
