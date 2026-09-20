"""Locate the benchmark checkout used by authoring and evaluation."""

import os
from pathlib import Path


def _repository_root() -> Path:
    configured = os.environ.get("DAFNYUTILS_REPO_ROOT")
    if configured:
        root = Path(configured).resolve()
        if not (root / "bench").is_dir():
            raise ValueError(f"DAFNYUTILS_REPO_ROOT has no bench directory: {root}")
        return root
    for parent in Path(__file__).resolve().parents:
        if (parent / "bench").is_dir():
            return parent
    raise RuntimeError("unable to locate the dafnyutils benchmark checkout")


REPO_ROOT = _repository_root()
