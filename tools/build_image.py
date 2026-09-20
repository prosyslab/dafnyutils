"""Stage the shared task toolchain and build its Docker image."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
from pathlib import Path


def create_task_image_context(*, directory: Path, repository_root: Path) -> None:
    """Stage toolchain and package sources without task files."""
    binaries = repository_root / "dafny/Binaries"
    if not (binaries / "Dafny.dll").is_file():
        raise FileNotFoundError("built Dafny.dll is required; run make build-dafny first")
    directory.mkdir(parents=True, exist_ok=False)
    shutil.copytree(binaries, directory / "Binaries")
    shutil.copyfile(repository_root / "docker/task/Dockerfile", directory / "Dockerfile")
    shutil.copyfile(repository_root / "pyproject.toml", directory / "pyproject.toml")
    shutil.copytree(
        repository_root / "src",
        directory / "src",
        ignore=shutil.ignore_patterns("__pycache__", "*.pyc", "*.egg-info"),
    )
    shutil.copyfile(
        repository_root / "docker/evaluation/requirements.txt", directory / "requirements.txt"
    )


def main() -> int:
    root = Path.cwd()
    with tempfile.TemporaryDirectory(prefix="dafnyutils-task-image-") as temporary:
        context = Path(temporary) / "context"
        create_task_image_context(directory=context, repository_root=root)
        tag = os.environ.get("IMAGE_TAG") or "dafnyutils-task:latest"
        return subprocess.run(
            ["docker", "build", "--tag", tag, str(context)], cwd=root, check=False
        ).returncode


if __name__ == "__main__":
    raise SystemExit(main())
