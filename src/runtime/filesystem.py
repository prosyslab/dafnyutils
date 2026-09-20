"""Filesystem copying and containment for isolated workspaces."""

import os
import shutil
from pathlib import Path
from typing import Any

ignore_python_cache = shutil.ignore_patterns("__pycache__", "*.pyc", "*.pyo")


def safe_relative_path(raw: Any) -> Path | None:
    if not isinstance(raw, str):
        return None
    candidate = Path(raw)
    if candidate.is_absolute():
        return None
    normalized = Path(*[part for part in candidate.parts if part not in {"", "."}])
    if any(part == ".." for part in normalized.parts):
        return None
    return normalized


def copy_entry(source: Path, destination: Path) -> None:
    if source.is_dir():
        shutil.copytree(
            source, destination, symlinks=True, dirs_exist_ok=True, ignore=ignore_python_cache
        )
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination, follow_symlinks=False)


def copy_tree_within_root(source: Path, destination: Path) -> None:
    """Copy a directory tree after rejecting links that leave that tree."""
    if source.is_symlink() or not source.is_dir():
        raise ValueError(f"source tree must be a directory: {source}")

    source_root = source.resolve()
    links: list[Path] = []
    for directory, directory_names, file_names in os.walk(source, followlinks=False):
        ignored = ignore_python_cache(directory, [*directory_names, *file_names])
        directory_names[:] = [name for name in directory_names if name not in ignored]
        for name in [*directory_names, *file_names]:
            if name in ignored:
                continue
            candidate = Path(directory) / name
            if not candidate.is_symlink():
                continue
            try:
                candidate.resolve(strict=False).relative_to(source_root)
            except (OSError, RuntimeError, ValueError) as error:
                raise ValueError(f"unsafe symlink in source tree: {candidate}") from error
            links.append(candidate)

    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(source, destination, symlinks=True, ignore=ignore_python_cache)
    for link in links:
        copied_link = destination / link.relative_to(source)
        target = link.resolve(strict=False)
        copied_link.unlink()
        copied_link.symlink_to(
            os.path.relpath(target, start=link.parent.resolve()),
            target_is_directory=target.is_dir(),
        )


def remove_entry(path: Path) -> None:
    if not path.exists():
        return
    if path.is_dir() and not path.is_symlink():
        shutil.rmtree(path)
    else:
        path.unlink()


def path_within_root(path: Path, root: Path) -> bool:
    return path.resolve().is_relative_to(root.resolve())
