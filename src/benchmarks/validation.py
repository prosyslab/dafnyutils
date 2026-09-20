"""Validate authoring inputs once and retain the resulting source analysis."""

from __future__ import annotations

from dataclasses import dataclass

from benchmarks.definition import BenchmarkDefinition, SourceStatus
from benchmarks.generated_profile import GeneratedTaskProfile, generate_task_profile
from benchmarks.profiles import ResolvedBenchmark
from benchmarks.repository import BenchmarkRepository


@dataclass(frozen=True)
class ValidationIssue:
    task_id: str
    message: str


@dataclass(frozen=True)
class ValidatedBenchmark:
    definition: BenchmarkDefinition
    configuration: ResolvedBenchmark
    profile: GeneratedTaskProfile


class BenchmarkValidationError(ValueError):
    def __init__(self, issues: tuple[ValidationIssue, ...]) -> None:
        self.issues = issues
        super().__init__("; ".join(issue.message for issue in issues))


def load_validated_benchmark(repository: BenchmarkRepository, task_id: str) -> ValidatedBenchmark:
    """Load external definitions and analyze trusted sources for one preparation."""
    try:
        definition = repository.load_definition(task_id)
    except (OSError, ValueError, KeyError) as exc:
        raise BenchmarkValidationError((ValidationIssue(task_id, str(exc)),)) from exc
    issues = list(_validate_declared_files(repository, definition))
    if definition.source.status is SourceStatus.INCOMPLETE:
        issues.append(ValidationIssue(task_id, "source provenance is incomplete"))
    if issues:
        raise BenchmarkValidationError(tuple(issues))
    configuration = ResolvedBenchmark.for_task(task_id)
    try:
        validated = generate_task_profile(
            definition, repository_root=repository.root, configuration=configuration
        )
    except (OSError, RuntimeError, ValueError) as exc:
        raise BenchmarkValidationError((ValidationIssue(task_id, str(exc)),)) from exc
    evaluation_only = {
        path
        for path in (definition.evaluation.cases_path, definition.evaluation.test_path)
        if path is not None
    }
    exposed = {resource.path for resource in validated.profile.resources}
    leaked = sorted(evaluation_only & exposed)
    if leaked:
        raise BenchmarkValidationError(
            (
                ValidationIssue(
                    task_id,
                    "evaluation-only paths are exposed as public resources: " + ", ".join(leaked),
                ),
            )
        )
    return ValidatedBenchmark(definition, configuration, validated)


def validate_benchmark(
    repository: BenchmarkRepository, task_id: str
) -> tuple[ValidationIssue, ...]:
    try:
        load_validated_benchmark(repository, task_id)
    except BenchmarkValidationError as exc:
        return exc.issues
    return ()


def _validate_declared_files(
    repository: BenchmarkRepository,
    definition: BenchmarkDefinition,
) -> tuple[ValidationIssue, ...]:
    issues: list[ValidationIssue] = []
    for label, relative_path in _declared_paths(definition):
        path = (repository.root / relative_path).resolve()
        if not path.is_relative_to(repository.root):
            issues.append(ValidationIssue(definition.task_id, f"{label} escapes repository root"))
        elif not path.is_file():
            issues.append(ValidationIssue(definition.task_id, f"missing {label}: {relative_path}"))
    return tuple(issues)


def _declared_paths(definition: BenchmarkDefinition) -> tuple[tuple[str, str], ...]:
    paths = [
        ("description", definition.description_path),
        ("project config", definition.project_config_path),
        ("evaluation test", definition.evaluation.test_path),
    ]
    if definition.evaluation.cases_path is not None:
        paths.append(("evaluation cases", definition.evaluation.cases_path))
    return tuple(paths)
