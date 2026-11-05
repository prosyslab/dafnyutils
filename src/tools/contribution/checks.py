"""Run mandatory contributor checks and interpret their external evidence."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import xml.etree.ElementTree as ElementTree
from dataclasses import dataclass
from pathlib import Path

from benchmarks.checks import required_checks_for_evaluation_capabilities
from benchmarks.definition import BenchmarkDefinition
from benchmarks.repository import BenchmarkRepository
from tools.contribution.make_tasks import build_directory
from tools.contribution.validation import load_validated_benchmark
from tools.environment import EVAL_BENCH_DLL_ENV


@dataclass(frozen=True)
class CheckCommand:
    """Describe one named check command and its execution context."""

    name: str
    argv: tuple[str, ...]
    environment: tuple[tuple[str, str], ...] = ()
    pytest_report: str | None = None


def check_commands(root: Path, definition: BenchmarkDefinition) -> tuple[CheckCommand, ...]:
    """Select every mandatory contributor command for a benchmark task."""
    if build_directory(root).resolve() != (root / "_build").resolve():
        raise ValueError("contribution checks require the default BUILD_DIR=_build")
    python = sys.executable
    pytest_report = f"_build/contribution_checks/{definition.task_id}/implementation-tests.xml"
    bench_dll = f"_build/bench/{definition.task_id}_bench.dll"
    test_env = ((EVAL_BENCH_DLL_ENV, bench_dll),)
    task_command = (python, "-m", "tools.contribution.make_tasks")
    task_selection = ("--root", str(root), "--task", definition.task_id)
    steps: dict[str, tuple[CheckCommand, ...]] = {
        "impl_layout": (CheckCommand("build", (*task_command, "build", *task_selection)),),
        "proof_layout": (),
        "dafny_verify": (
            CheckCommand(
                "dafny-verify",
                ("make", "-C", definition.item_directory, "verify"),
            ),
        ),
    }
    steps["dafny_verify"] += (
        CheckCommand(
            "benchmark-proof-tests",
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
            (("PYTEST_PLUGINS", "tools.pytest_infrastructure"),),
        ),
    )
    reference = (
        (CheckCommand("coreutils-reference", ("make", "build-coreutils")),)
        if definition.evaluation.reference_executable is not None
        else ()
    )
    steps["implementation_tests"] = (
        *reference,
        CheckCommand(
            "implementation-tests",
            (*task_command, "test", *task_selection),
            (*test_env, ("PYTEST_ARGS", f"--junitxml={root / pytest_report}")),
            pytest_report,
        ),
    )
    if definition.evaluation.fuzzer_target is not None:
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
    required = required_checks_for_evaluation_capabilities(definition.evaluation)
    missing = sorted(set(required) - steps.keys())
    if missing:
        raise ValueError("missing contributor commands for required checks: " + ", ".join(missing))
    commands: list[CheckCommand] = []
    for name in required:
        commands.extend(steps[name])
    return tuple(commands)


def run_benchmark_checks(repository: BenchmarkRepository, task_id: str) -> None:
    """Run required contributor commands and reject failed or missing evidence."""
    definition = load_validated_benchmark(repository, task_id).definition
    run_check_commands(repository.root, check_commands(repository.root, definition))


def run_check_commands(root: Path, commands: tuple[CheckCommand, ...]) -> None:
    """Run selected commands and require execution evidence for implementation tests."""
    for command in commands:
        environment = os.environ.copy()
        environment.update(command.environment)
        report_path = _prepare_pytest_report(root, command)
        completed = subprocess.run(
            command.argv,
            cwd=root,
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
    """Require at least one executed test in a JUnit report."""
    try:
        root = ElementTree.parse(report_path).getroot()
    except (OSError, ElementTree.ParseError) as exc:
        raise RuntimeError(f"invalid or missing pytest JUnit evidence: {report_path}") from exc
    cases = root.findall(".//testcase")
    executed = [case for case in cases if case.find("skipped") is None]
    if not executed:
        raise RuntimeError("mandatory implementation test suite executed no tests")


def validate_fuzzer_capabilities(definition: BenchmarkDefinition, raw: str) -> None:
    """Validate that fuzzer capability output covers the selected task."""
    try:
        payload = json.loads(raw)
        if payload.get("schema_version") != 4 or not isinstance(payload.get("utilities"), list):
            raise ValueError("unsupported capability schema")
        matches = [
            item for item in payload["utilities"] if item.get("utility") == definition.task_id
        ]
        if len(matches) != 1:
            raise ValueError("task is not registered exactly once")
        capability = matches[0]
        if capability.get("fuzz_strategy") not in {"generic", "custom"}:
            raise ValueError("task has no supported fuzz strategy")
        limitations = payload.get("limitations")
        if (
            not isinstance(limitations, list)
            or not limitations
            or any(not isinstance(item, str) or not item.strip() for item in limitations)
        ):
            raise ValueError("capability limitations must be a nonempty list of text")
    except (AttributeError, json.JSONDecodeError, TypeError, ValueError) as exc:
        raise RuntimeError(
            f"invalid fuzzer capability result for {definition.task_id}: {exc}"
        ) from exc
