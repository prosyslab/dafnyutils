"""Versioned, contributor-owned benchmark item definitions."""

from __future__ import annotations

import re
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from urllib.parse import urlparse

import yaml
from pydantic import BaseModel, ConfigDict, field_validator, model_validator
from yaml import YAMLError


class BenchmarkDefinitionError(ValueError):
    """A benchmark definition is malformed or inconsistent with its location."""


class BenchmarkDefinitionSchemaVersion(str, Enum):
    V2 = "benchmark.definition.v2"


class BenchmarkKind(str, Enum):
    COREUTILS = "coreutils"
    ALGORITHM = "algorithm"


class SourceStatus(str, Enum):
    VERIFIED = "verified"
    LEGACY_UNVERIFIED = "legacy-unverified"
    INCOMPLETE = "incomplete"


# These are the only pre-manifest-migration tasks allowed to retain unknown provenance.
LEGACY_TASK_IDS = frozenset(
    {
        "algorithm-1",
        "algorithm-100",
        "algorithm-20",
        "algorithm-3690",
        "algorithm-38",
        "algorithm-4",
        "algorithm-4004",
        "algorithm-59",
        "algorithm-63",
        "algorithm-75",
        "base64",
        "basename",
        "cat",
        "chmod",
        "comm",
        "csplit",
        "cut",
        "dirname",
        "du",
        "echo",
        "expand",
        "expr",
        "factor",
        "false",
        "fold",
        "head",
        "ln",
        "logname",
        "ls",
        "mv",
        "nl",
        "paste",
        "printenv",
        "printf",
        "pwd",
        "readlink",
        "seq",
        "stat",
        "tac",
        "tail",
        "tee",
        "touch",
        "tr",
        "true",
        "uniq",
        "wc",
    }
)


class _DefinitionModel(BaseModel):
    model_config = ConfigDict(extra="forbid")


def validate_task_id(value: str) -> str:
    if value != value.strip() or re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", value) is None:
        raise ValueError("task_id must contain lowercase letters, digits, and hyphens")
    return value


def benchmark_item_directory(kind: BenchmarkKind, task_id: str) -> str:
    """Return the canonical repository-relative directory for a benchmark item."""
    validate_task_id(task_id)
    if kind is BenchmarkKind.COREUTILS:
        if task_id.startswith("algorithm-"):
            raise ValueError("coreutils task IDs cannot use the algorithm- prefix")
        return f"bench/utils/{task_id}"
    if kind is not BenchmarkKind.ALGORITHM:
        raise ValueError(f"unknown benchmark kind: {kind!r}")
    algorithm_id = task_id.removeprefix("algorithm-")
    if not task_id.startswith("algorithm-") or not algorithm_id.isdigit():
        raise ValueError("algorithm task IDs must have the form algorithm-<number>")
    return f"bench/algorithm/{algorithm_id}"


def class_name_for_task_id(task_id: str) -> str:
    validate_task_id(task_id)
    if task_id.startswith("algorithm-"):
        algorithm_id = task_id.removeprefix("algorithm-")
        if not algorithm_id.isdigit():
            raise ValueError("algorithm task IDs must have the form algorithm-<number>")
        return "Algorithm" + algorithm_id
    return "".join(part[:1].upper() + part[1:] for part in task_id.split("-"))


class BenchmarkSource(_DefinitionModel):
    status: SourceStatus
    name: str
    url: str | None = None
    license: str | None = None

    @field_validator("name")
    @classmethod
    def _validate_name(cls, value: str) -> str:
        if not value.strip() or value != value.strip():
            raise ValueError("source name must be non-empty and trimmed")
        return value

    @model_validator(mode="after")
    def _validate_verified_source(self) -> BenchmarkSource:
        if self.status is SourceStatus.VERIFIED and not (self.url and self.license):
            raise ValueError("a verified source requires both url and license")
        if self.status is SourceStatus.VERIFIED:
            url = self.url or ""
            license_id = self.license or ""
            parsed = urlparse(url)
            if parsed.scheme not in {"http", "https"} or not parsed.netloc:
                raise ValueError("a verified source requires an HTTP(S) URL")
            if url != url.strip() or license_id != license_id.strip():
                raise ValueError("verified source URL and license must be trimmed")
            if "TODO" in self.name.upper() or "TODO" in license_id.upper():
                raise ValueError("verified source fields cannot contain TODO placeholders")
        return self


@dataclass(frozen=True)
class BenchmarkEvaluation:
    test_path: str
    cases_path: str | None
    fuzzer_target: str | None


class BenchmarkDefinition(_DefinitionModel):
    schema_version: BenchmarkDefinitionSchemaVersion
    task_id: str
    kind: BenchmarkKind
    source: BenchmarkSource

    @field_validator("task_id")
    @classmethod
    def _validate_task_id(cls, value: str) -> str:
        return validate_task_id(value)

    @model_validator(mode="after")
    def _validate_family_fields(self) -> BenchmarkDefinition:
        if (
            self.source.status is SourceStatus.LEGACY_UNVERIFIED
            and self.task_id not in LEGACY_TASK_IDS
        ):
            raise ValueError("legacy-unverified is reserved for the migration baseline")
        benchmark_item_directory(self.kind, self.task_id)
        return self

    @property
    def item_directory(self) -> str:
        return benchmark_item_directory(self.kind, self.task_id)

    @property
    def title(self) -> str:
        return f"Implement and verify {self.task_id}"

    @property
    def description_path(self) -> str:
        return f"{self.item_directory}/{self.task_id}.md"

    @property
    def project_config_path(self) -> str:
        return f"{self.item_directory}/dfyconfig.toml"

    @property
    def evaluation(self) -> BenchmarkEvaluation:
        if self.kind is BenchmarkKind.COREUTILS:
            return BenchmarkEvaluation(f"{self.item_directory}/Tests.py", None, self.task_id)
        return BenchmarkEvaluation(
            "tools/bench/test_bench_algorithm.py", f"{self.item_directory}/cases.json", None
        )

    @classmethod
    def from_yaml_file(cls, path: Path) -> BenchmarkDefinition:
        try:
            parsed = yaml.safe_load(path.read_text(encoding="utf-8"))
        except (OSError, YAMLError) as exc:
            raise BenchmarkDefinitionError(
                f"failed to read benchmark definition {path}: {exc}"
            ) from exc
        try:
            return cls.model_validate(parsed)
        except (TypeError, ValueError) as exc:
            raise BenchmarkDefinitionError(f"invalid benchmark definition {path}: {exc}") from exc
