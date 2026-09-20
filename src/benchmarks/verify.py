"""Verify a local Dafny benchmark project using explicit library dependencies."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

from dafny_cli import dafny_command
from entry_contract import (
    DafnyEntry,
    EntryValidationFailure,
    ValidatedEntryContract,
    project_verification_contract,
)
from standard_library import DAFNY_ALLOW_WARNINGS_OPTION
from verification import verification_options, verify_contract

from .definition import BenchmarkDefinition, BenchmarkKind, class_name_for_task_id


def local_verification_contract(
    project: Path, libraries: tuple[Path, ...] = ()
) -> ValidatedEntryContract:
    definition = BenchmarkDefinition.from_yaml_file(project / "benchmark.yaml")
    name = class_name_for_task_id(definition.task_id)
    support = {source for library in libraries for source in library.rglob("*.dfy")}
    symbol = f"{name}.RunCore"
    if definition.kind is BenchmarkKind.COREUTILS:
        symbol = f"{name}.{name}BenchmarkItem.RunCore"
        support.update((project / f"{name}Cli.dfy", project / f"{name}Schema.dfy"))
    return project_verification_contract(project, DafnyEntry(f"{name}.dfy", symbol), support)


def _source_snapshot(project: Path, libraries: tuple[Path, ...]) -> tuple[tuple[Path, str], ...]:
    paths = {
        *project.rglob("*.dfy"),
        *(source for library in libraries for source in library.rglob("*.dfy")),
        project / "dfyconfig.toml",
        project / "benchmark.yaml",
    }
    return tuple((path, hashlib.sha256(path.read_bytes()).hexdigest()) for path in sorted(paths))


def verify_project(project: Path, libraries: tuple[Path, ...], *, dafny: str) -> int:
    project = project.resolve()
    for library in libraries:
        if not library.is_dir() or library.is_symlink():
            raise ValueError(f"invalid library directory: {library}")
    libraries = tuple(path.resolve() for path in libraries)
    snapshot = _source_snapshot(project, libraries)
    contract = local_verification_contract(project, libraries)

    def validate_sources() -> None:
        if _source_snapshot(project, libraries) != snapshot:
            raise EntryValidationFailure("project sources changed during verification")

    library_options = tuple(f"--library:{library}" for library in libraries)
    if libraries:
        library_options += (DAFNY_ALLOW_WARNINGS_OPTION,)
    return verify_contract(
        contract,
        project,
        dafny,
        verification_options(library_options),
        validate=validate_sources,
        libraries=libraries,
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    parser.add_argument("--library", type=Path, action="append", default=[])
    parser.add_argument("--dafny", default=dafny_command())
    args = parser.parse_args(argv)
    return verify_project(args.project, tuple(args.library), dafny=args.dafny)


if __name__ == "__main__":
    raise SystemExit(main())
