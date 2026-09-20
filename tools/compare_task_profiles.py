#!/usr/bin/env python3
"""Show public task contract changes against a committed benchmark baseline."""

from __future__ import annotations

import argparse
import io
import json
import shutil
import subprocess
import sys
import tarfile
from pathlib import Path, PurePosixPath
from tempfile import TemporaryDirectory
from typing import Any, Iterator

from benchmarks.definition import (
    BenchmarkDefinition,
    BenchmarkDefinitionError,
    BenchmarkKind,
    benchmark_item_directory,
)
from benchmarks.generated_profile import generate_task_profile
from benchmarks.paths import REPO_ROOT
from benchmarks.repository import BenchmarkRepository
from benchmarks.task import TaskPayloadError, TaskProfile
from entry_contract import EntryValidationFailure


class ContractComparisonError(ValueError):
    """A baseline cannot be safely read or compared."""


_MISSING = object()
_PRIORITY = (
    "dafny",
    "resources",
    "workspace",
    "public_checks",
    "public_rules",
    "schema_version",
    "task_id",
    "title",
)
_DAFNY_PRIORITY = ("spec_entries", "spec_definitions", "execution_entry", "utility_root")


def _git(root: Path, *arguments: str) -> bytes:
    result = subprocess.run(["git", *arguments], cwd=root, capture_output=True, check=False)
    if result.returncode:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise ContractComparisonError(f"git {' '.join(arguments[:2])} failed: {detail}")
    return result.stdout


def _baseline_commit(root: Path, base_ref: str) -> str:
    if not base_ref or base_ref.startswith("-"):
        raise ContractComparisonError("base reference must name an existing commit")
    result = _git(root, "rev-parse", "--verify", "--end-of-options", f"{base_ref}^{{commit}}")
    return result.decode("ascii").strip()


def _extract_baseline_bench(root: Path, commit: str, destination: Path) -> None:
    if not _git(root, "ls-tree", "--name-only", commit, "bench").strip():
        raise ContractComparisonError(f"baseline commit {commit} has no bench/ directory")
    archive_bytes = _git(root, "archive", "--format=tar", commit, "bench")
    with tarfile.open(fileobj=io.BytesIO(archive_bytes), mode="r:") as archive:
        for member in archive:
            relative = PurePosixPath(member.name)
            if (
                relative.is_absolute()
                or not relative.parts
                or relative.parts[0] != "bench"
                or any(part in {".", ".."} for part in relative.parts)
            ):
                raise ContractComparisonError(f"unsafe baseline archive path: {member.name}")
            target = destination.joinpath(*relative.parts)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
            elif member.isfile():
                target.parent.mkdir(parents=True, exist_ok=True)
                source = archive.extractfile(member)
                if source is None:
                    raise ContractComparisonError(f"unreadable baseline file: {member.name}")
                with source, target.open("wb") as output:
                    shutil.copyfileobj(source, output)
            else:
                raise ContractComparisonError(f"unsupported baseline archive entry: {member.name}")


def _definition_paths(root: Path) -> tuple[Path, ...]:
    return tuple(
        sorted(
            path
            for family in ("utils", "algorithm")
            for path in (root / "bench" / family).glob("*/benchmark.yaml")
        )
    )


def _baseline_profiles(root: Path) -> dict[str, TaskProfile]:
    profiles: dict[str, TaskProfile] = {}
    for definition_path in _definition_paths(root):
        profile_path = definition_path.with_name("task.yaml")
        if profile_path.is_file():
            profile = TaskProfile.from_yaml_file(profile_path)
        else:
            definition = BenchmarkDefinition.from_yaml_file(definition_path)
            profile = _generate_profile(definition, root)
        expected_directory = definition_path.parent.relative_to(root).as_posix()
        kind = (
            BenchmarkKind.ALGORITHM
            if definition_path.parent.parent.name == "algorithm"
            else BenchmarkKind.COREUTILS
        )
        try:
            canonical_directory = benchmark_item_directory(kind, profile.task_id)
        except ValueError as exc:
            raise ContractComparisonError(
                f"invalid baseline task ID in {profile_path.relative_to(root)}: {exc}"
            ) from exc
        if (
            profile.dafny.utility_root != expected_directory
            or canonical_directory != expected_directory
        ):
            raise ContractComparisonError(
                f"baseline task identity does not match {definition_path.relative_to(root)}"
            )
        if profile.task_id in profiles:
            raise ContractComparisonError(f"duplicate baseline task ID: {profile.task_id}")
        profiles[profile.task_id] = profile
    if not profiles:
        raise ContractComparisonError("baseline bench/ has no benchmark definitions")
    return profiles


def _current_profiles(root: Path) -> dict[str, TaskProfile]:
    try:
        repository = BenchmarkRepository.open(root)
    except ValueError as exc:
        raise ContractComparisonError(f"current benchmark root is invalid: {exc}") from exc
    return {
        definition.task_id: _generate_profile(definition, repository.root)
        for definition in repository.definitions()
    }


def _generate_profile(definition: BenchmarkDefinition, root: Path) -> TaskProfile:
    try:
        return generate_task_profile(definition, repository_root=root).profile
    except (EntryValidationFailure, OSError, ValueError) as exc:
        raise ContractComparisonError(
            f"failed to generate public profile for {definition.task_id}: {exc}"
        ) from exc


def _ordered_keys(keys: set[str], path: str) -> list[str]:
    priority = _DAFNY_PRIORITY if path == "/dafny" else _PRIORITY if not path else ()
    return [key for key in priority if key in keys] + sorted(keys.difference(priority))


def _field_changes(before: Any, after: Any, path: str = "") -> Iterator[tuple[str, Any, Any]]:
    if isinstance(before, dict) and isinstance(after, dict):
        for key in _ordered_keys(set(before) | set(after), path):
            escaped = key.replace("~", "~0").replace("/", "~1")
            yield from _field_changes(
                before.get(key, _MISSING), after.get(key, _MISSING), f"{path}/{escaped}"
            )
    elif isinstance(before, list) and isinstance(after, list):
        for index in range(max(len(before), len(after))):
            left = before[index] if index < len(before) else _MISSING
            right = after[index] if index < len(after) else _MISSING
            yield from _field_changes(left, right, f"{path}/{index}")
    elif before != after:
        yield path, before, after


def _display(value: Any) -> str:
    return (
        "<missing>" if value is _MISSING else json.dumps(value, ensure_ascii=False, sort_keys=True)
    )


def compare_task_profiles(root: Path, base_ref: str) -> tuple[str, ...]:
    """Return review lines; contract changes are informative, invalid inputs raise."""
    root = root.resolve()
    commit = _baseline_commit(root, base_ref)
    with TemporaryDirectory(prefix="benchmark-profile-base-") as directory:
        baseline_root = Path(directory)
        _extract_baseline_bench(root, commit, baseline_root)
        baseline = _baseline_profiles(baseline_root)
    current = _current_profiles(root)
    lines = [f"Public task contract comparison against {commit}:"]
    for task_id in sorted(baseline.keys() | current.keys()):
        if task_id not in baseline:
            lines.append(f"+ task {task_id}")
        elif task_id not in current:
            lines.append(f"- task {task_id}")
        else:
            before = baseline[task_id].model_dump(mode="json")
            after = current[task_id].model_dump(mode="json")
            for path, old, new in _field_changes(before, after):
                lines.append(f"~ task {task_id} {path}: {_display(old)} -> {_display(new)}")
    if len(lines) == 1:
        lines.append("No public task contract changes.")
    return tuple(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-ref", required=True, help="existing baseline Git commit")
    parser.add_argument("--root", type=Path, default=REPO_ROOT, help="current checkout root")
    args = parser.parse_args(argv)
    try:
        lines = compare_task_profiles(args.root, args.base_ref)
    except (
        BenchmarkDefinitionError,
        ContractComparisonError,
        OSError,
        tarfile.TarError,
        TaskPayloadError,
    ) as exc:
        print(f"task contract comparison failed: {exc}", file=sys.stderr)
        return 1
    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
