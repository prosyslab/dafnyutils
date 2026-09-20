"""Resolve a selected benchmark and run its build or test command."""

from __future__ import annotations

import argparse
import os
import shlex
import subprocess
import sys
from enum import StrEnum
from pathlib import Path

from benchmarks.definition import BenchmarkDefinition, BenchmarkKind
from benchmarks.repository import BenchmarkRepository


class TaskCommand(StrEnum):
    BUILD = "build"
    TEST = "test"


def _run(command: list[str], *, cwd: Path, env: dict[str, str] | None = None) -> int:
    return subprocess.run(command, cwd=cwd, env=env, check=False).returncode


def _python() -> str:
    return os.environ.get("PYTHON") or sys.executable


def _dafny() -> str:
    return os.environ.get("DAFNY_BENCHMARK") or "dafny-benchmark"


def _build_dir(root: Path) -> Path:
    return root / (os.environ.get("BUILD_DIR") or "_build")


def _definition(root: Path, task_id: str) -> BenchmarkDefinition:
    try:
        return BenchmarkRepository.open(root).load_definition(task_id)
    except (KeyError, OSError, ValueError) as error:
        raise ValueError(f"invalid task: {task_id}") from error


def _pytest_args() -> list[str]:
    return shlex.split(os.environ.get("PYTEST_ARGS", ""))


def _build(root: Path, definition: BenchmarkDefinition) -> int:
    if definition.task_id == "touch":
        status = _run(
            [
                "make",
                "-C",
                "bench/utils/touch",
                "build-time-parser",
                f"BUILD_DIR={_build_dir(root)}",
            ],
            cwd=root,
        )
        if status:
            return status

    bench_dir = _build_dir(root) / "bench"
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
    if definition.kind is BenchmarkKind.COREUTILS:
        command.append("bench/core/IOExtern.cs")
    return _run(command, cwd=root, env=env)


def _test(root: Path, definition: BenchmarkDefinition | None) -> int:
    if definition is None:
        return _run(
            [_python(), "-m", "pytest", "-q", "tests"],
            cwd=root,
        )

    if definition.kind is BenchmarkKind.ALGORITHM:
        env = dict(os.environ)
        env["ALGORITHM_BENCH_ID"] = definition.task_id.removeprefix("algorithm-")
        return _run(
            [
                _python(),
                "-m",
                "pytest",
                "-q",
                "-n0",
                "tools/bench/test_bench_algorithm.py",
                *_pytest_args(),
            ],
            cwd=root,
            env=env,
        )

    target_root = (root / (os.environ.get("EVAL_TARGET_ROOT") or ".")).resolve()
    test_build_dir = target_root / "_build" / "dafny-tests" / definition.task_id
    test_build_dir.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["TMPDIR"] = "/tmp"
    status = _run(
        [
            _dafny(),
            "test",
            "--no-verify",
            "--output",
            str(test_build_dir / "Tests.dll"),
            "Tests.dfy",
            str(target_root / "bench/core/IOExtern.cs"),
        ],
        cwd=target_root / definition.item_directory,
        env=env,
    )
    if status:
        return status
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
            f"{definition.item_directory}/Tests.py",
            *_pytest_args(),
        ],
        cwd=root,
    )


def main(argv: list[str] | None = None) -> int:
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
