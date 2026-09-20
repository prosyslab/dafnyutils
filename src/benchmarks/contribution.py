"""Run mandatory contributor checks and interpret their external evidence."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import xml.etree.ElementTree as ElementTree
from dataclasses import dataclass
from pathlib import Path

from benchmarks.checks import required_checks_for_kind
from benchmarks.definition import BenchmarkDefinition, BenchmarkKind
from benchmarks.repository import BenchmarkRepository
from benchmarks.validation import load_validated_benchmark


@dataclass(frozen=True)
class CheckCommand:
    name: str
    argv: tuple[str, ...]
    environment: tuple[tuple[str, str], ...] = ()
    pytest_report: str | None = None


def check_commands(root: Path, definition: BenchmarkDefinition) -> tuple[CheckCommand, ...]:
    python = sys.executable
    pytest_report = f"_build/contribution_checks/{definition.task_id}/implementation-tests.xml"
    bench_dll = f"_build/bench/{definition.task_id}_bench.dll"
    test_env = (("EVAL_BENCH_DLL", bench_dll),)
    steps: dict[str, tuple[CheckCommand, ...]] = {
        "impl_layout": (CheckCommand("build", ("make", "build", f"TASK={definition.task_id}")),),
        "proof_layout": (),
        "dafny_verify": (
            CheckCommand(
                "dafny-verify",
                ("make", "-C", definition.item_directory, "verify"),
            ),
        ),
    }
    if definition.kind is BenchmarkKind.COREUTILS:
        steps["dafny_verify"] += (
            CheckCommand(
                "utility-proof-tests",
                (
                    python,
                    "-m",
                    "pytest",
                    "-q",
                    "-n0",
                    "--import-mode=importlib",
                    "-m",
                    "dafny_verify",
                    f"{definition.item_directory}/Tests.py",
                ),
            ),
        )
        steps["implementation_tests"] = (
            CheckCommand(
                "coreutils-reference",
                ("make", "build-coreutils"),
            ),
            CheckCommand(
                "implementation-tests",
                (
                    "make",
                    "test",
                    f"TASK={definition.task_id}",
                    f"PYTEST_ARGS=--junitxml={root / pytest_report}",
                ),
                test_env,
                pytest_report,
            ),
        )
        steps["fuzzer"] = (
            CheckCommand(
                "fuzzer",
                (
                    python,
                    "tools/coreutils_fuzzer/run.py",
                    "fuzz",
                    definition.task_id,
                    "--iterations",
                    "20",
                    "--seed",
                    "1",
                ),
            ),
        )
    else:
        steps["implementation_tests"] = (
            CheckCommand(
                "implementation-tests",
                (
                    "make",
                    "test",
                    f"TASK={definition.task_id}",
                    f"PYTEST_ARGS=--junitxml={root / pytest_report}",
                ),
                test_env,
                pytest_report,
            ),
        )

    required = required_checks_for_kind(definition.kind)
    missing = sorted(set(required) - steps.keys())
    if missing:
        raise ValueError("missing contributor commands for required checks: " + ", ".join(missing))
    commands: list[CheckCommand] = []
    for name in required:
        commands.extend(steps[name])
    return tuple(commands)


def run_benchmark_checks(repository: BenchmarkRepository, task_id: str) -> None:
    definition = load_validated_benchmark(repository, task_id).definition
    for command in check_commands(repository.root, definition):
        environment = os.environ.copy()
        environment.update(command.environment)
        report_path = _prepare_pytest_report(repository.root, command)
        completed = subprocess.run(
            command.argv,
            cwd=repository.root,
            env=environment,
            check=False,
        )
        if completed.returncode != 0:
            raise RuntimeError(
                f"benchmark check {command.name!r} failed with exit code {completed.returncode}"
            )
        if report_path is not None:
            validate_pytest_report(report_path)


def _prepare_pytest_report(root: Path, command: CheckCommand) -> Path | None:
    if command.pytest_report is None:
        return None
    report_path = (root / command.pytest_report).resolve()
    if not report_path.is_relative_to(root):
        raise RuntimeError("pytest evidence path escapes repository root")
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.unlink(missing_ok=True)
    return report_path


def validate_pytest_report(report_path: Path) -> None:
    try:
        root = ElementTree.parse(report_path).getroot()
    except (OSError, ElementTree.ParseError) as exc:
        raise RuntimeError(f"invalid or missing pytest JUnit evidence: {report_path}") from exc
    cases = root.findall(".//testcase")
    executed = [case for case in cases if case.find("skipped") is None]
    if not executed:
        raise RuntimeError("mandatory implementation test suite executed no tests")


def validate_fuzzer_capabilities(definition: BenchmarkDefinition, raw: str) -> None:
    try:
        payload = json.loads(raw)
        if payload.get("schema_version") != 3 or not isinstance(payload.get("utilities"), list):
            raise ValueError("unsupported capability schema")
        matches = [
            item for item in payload["utilities"] if item.get("utility") == definition.task_id
        ]
        if len(matches) != 1:
            raise ValueError("task is not registered exactly once")
        capability = matches[0]
        if capability.get("fuzz_strategy") not in {"generic", "custom"}:
            raise ValueError("task has no supported fuzz strategy")
        if capability.get("time_coverage") not in {"none", "exact_per_execution"}:
            raise ValueError("task has no supported time-coverage requirement")
    except (AttributeError, json.JSONDecodeError, TypeError, ValueError) as exc:
        raise RuntimeError(
            f"invalid fuzzer capability result for {definition.task_id}: {exc}"
        ) from exc
