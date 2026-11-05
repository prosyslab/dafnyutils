"""Resolve a selected benchmark and run its build or test command."""

from __future__ import annotations

import argparse
import os
import shlex
import subprocess
import sys
from enum import StrEnum
from pathlib import Path

from benchmarks.definition import BenchmarkDefinition
from benchmarks.profiles import ResolvedBenchmark
from benchmarks.repository import BenchmarkRepository


class TaskCommand(StrEnum):
    """Select a contributor build or implementation-test operation."""

    BUILD = "build"
    TEST = "test"


def _run(command: list[str], *, cwd: Path, env: dict[str, str] | None = None) -> int:
    return subprocess.run(command, cwd=cwd, env=env, check=False).returncode


def _python() -> str:
    return os.environ.get("PYTHON") or sys.executable


def _dafny() -> str:
    return os.environ.get("DAFNY_BENCHMARK") or "dafny"


def build_directory(root: Path) -> Path:
    """Resolve the shared output directory used by native builds and contributor checks."""
    return root / (os.environ.get("BUILD_DIR") or "_build")


def _definition(root: Path, task_id: str) -> BenchmarkDefinition:
    try:
        return BenchmarkRepository.open(root).load_definition(task_id)
    except (KeyError, OSError, ValueError) as error:
        raise ValueError(f"invalid task: {task_id}") from error


def _pytest_args() -> list[str]:
    return shlex.split(os.environ.get("PYTEST_ARGS", ""))


def _build(root: Path, definition: BenchmarkDefinition) -> int:
    if definition.task_id in {"touch", "date"}:
        status = _run(
            [
                "make",
                "-C",
                f"bench/utils/{definition.task_id}",
                "build-time-parser",
                f"BUILD_DIR={build_directory(root)}",
            ],
            cwd=root,
        )
        if status:
            return status

    bench_dir = build_directory(root) / "bench"
    bench_dir.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["MSBuildProjectExtensionsPath"] = (
        str((bench_dir / "obj" / definition.task_id).resolve()) + "/"
    )
    env["TMPDIR"] = "/tmp"
    command = [
        _dafny(),
        "build",
        "--no-verify",
        "--output",
        str(bench_dir / f"{definition.task_id}_bench.dll"),
        definition.project_config_path,
    ]
    command.extend(
        ResolvedBenchmark.from_definition(definition).task_profile.compiler_dependency_paths
    )
    return _run(command, cwd=root, env=env)


def _test(root: Path, definition: BenchmarkDefinition | None) -> int:
    if definition is None:
        return _run(
            [_python(), "-m", "pytest", "-q", "tests"],
            cwd=root,
        )

    test_path = definition.evaluation.test_path
    environment = os.environ.copy()
    environment["PYTEST_PLUGINS"] = "tools.pytest_infrastructure"
    return _run(
        [
            _python(),
            "-m",
            "pytest",
            "-q",
            "-n0",
            "--import-mode=importlib",
            "-m",
            "not dafny_verify",
            test_path,
            *_pytest_args(),
        ],
        cwd=root,
        env=environment,
    )


def main(argv: list[str] | None = None) -> int:
    """Run the selected contributor build or implementation-test command."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", type=TaskCommand, choices=tuple(TaskCommand))
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="benchmark repository root")
    parser.add_argument("--task", help="benchmark task ID; omit for repository-wide tests")
    args = parser.parse_args(argv)
    if args.command is not TaskCommand.TEST and not args.task:
        parser.error(f"--task is required for {args.command}")
    root = args.root.resolve()
    try:
        definition = _definition(root, args.task) if args.task else None
    except ValueError as error:
        parser.error(str(error))
    if args.command is TaskCommand.BUILD and definition is not None:
        return _build(root, definition)
    return _test(root, definition)


if __name__ == "__main__":
    raise SystemExit(main())
