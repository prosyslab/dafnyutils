"""Validate contributor metadata and declared local files without source analysis."""

from __future__ import annotations

from dataclasses import dataclass

from benchmarks.definition import BenchmarkDefinition, SourceStatus
from benchmarks.profiles import ResolvedBenchmark
from benchmarks.repository import BenchmarkRepository


@dataclass(frozen=True)
class ValidationIssue:
    """Identify a task and a local authoring problem."""

    task_id: str
    message: str


@dataclass(frozen=True)
class ValidatedBenchmark:
    """Retain the definition and derived configuration after basic validation."""

    definition: BenchmarkDefinition
    configuration: ResolvedBenchmark


class BenchmarkValidationError(ValueError):
    """Report metadata or declared-file problems preventing local checks."""

    def __init__(self, issues: tuple[ValidationIssue, ...]) -> None:
        self.issues = issues
        super().__init__("; ".join(issue.message for issue in issues))


def load_validated_benchmark(repository: BenchmarkRepository, task_id: str) -> ValidatedBenchmark:
    """Check schema, provenance completeness and declared files without a compiler."""
    try:
        definition = repository.load_definition(task_id)
    except (OSError, ValueError, KeyError) as exc:
        raise BenchmarkValidationError((ValidationIssue(task_id, str(exc)),)) from exc
    issues = list(_validate_declared_files(repository, definition))
    if definition.source.status is SourceStatus.INCOMPLETE:
        issues.append(ValidationIssue(task_id, "source details are incomplete"))
    if issues:
        raise BenchmarkValidationError(tuple(issues))
    return ValidatedBenchmark(definition, ResolvedBenchmark.from_definition(definition))


def validate_benchmark(
    repository: BenchmarkRepository, task_id: str
) -> tuple[ValidationIssue, ...]:
    """Return basic authoring issues without raising a validation failure."""
    try:
        load_validated_benchmark(repository, task_id)
    except BenchmarkValidationError as exc:
        return exc.issues
    return ()


def _validate_declared_files(
    repository: BenchmarkRepository, definition: BenchmarkDefinition
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
