"""Verify every local project source with the ordinary Dafny compiler."""

from __future__ import annotations

import argparse
import hashlib
import os
import subprocess
from pathlib import Path


def verification_sources(project: Path) -> tuple[Path, ...]:
    """Cover all project sources, including unreferenced proofs."""
    sources = {source.resolve() for source in project.rglob("*.dfy")}
    if not sources:
        raise ValueError(f"project has no Dafny sources: {project}")
    return tuple(sorted(sources))


def _source_snapshot(project: Path, libraries: tuple[Path, ...]) -> tuple[tuple[Path, str], ...]:
    paths = {
        *verification_sources(project),
        *(source.resolve() for library in libraries for source in library.rglob("*.dfy")),
        project / "dfyconfig.toml",
        project / "benchmark.yaml",
    }
    return tuple((path, hashlib.sha256(path.read_bytes()).hexdigest()) for path in sorted(paths))


def verify_project(project: Path, libraries: tuple[Path, ...], *, dafny: str) -> int:
    """Verify all sources without inheriting a build project's no-verify setting."""
    project = project.resolve()
    if not project.is_dir():
        raise ValueError(f"invalid project directory: {project}")
    for library in libraries:
        if not library.is_dir() or library.is_symlink():
            raise ValueError(f"invalid library directory: {library}")
    libraries = tuple(path.resolve() for path in libraries)
    snapshot = _source_snapshot(project, libraries)
    sources = verification_sources(project)
    # Passing source files rather than dfyconfig.toml preserves all proof obligations.
    completed = subprocess.run(
        [
            dafny,
            "verify",
            "--standard-libraries:false",
            *(f"--library:{library}" for library in libraries),
            *(("--allow-warnings",) if libraries else ()),
            "--verify-included-files",
            "--boogie=/randomSeed:42",
            "--isolate-assertions",
            "--verification-time-limit:30",
            "--allow-external-contracts",
            *(str(path) for path in sources),
        ],
        cwd=project,
        check=False,
    )
    if _source_snapshot(project, libraries) != snapshot:
        raise RuntimeError("project sources changed during verification")
    return completed.returncode


def main(argv: list[str] | None = None) -> int:
    """Verify a project with every explicitly selected support source."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    parser.add_argument("--library", type=Path, action="append", default=[])
    parser.add_argument("--dafny", default=os.environ.get("DAFNY_BENCHMARK") or "dafny")
    args = parser.parse_args(argv)
    return verify_project(args.project, tuple(args.library), dafny=args.dafny)


if __name__ == "__main__":
    raise SystemExit(main())
