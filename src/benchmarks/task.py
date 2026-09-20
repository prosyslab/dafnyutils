"""Define and parse public task metadata, resource kinds, and workspace boundary contracts."""

from __future__ import annotations

import json
import re
from collections.abc import Hashable
from enum import StrEnum
from pathlib import Path, PurePosixPath
from typing import Self, TypeVar

import yaml
from pydantic import (
    BaseModel,
    ConfigDict,
    Field,
    StrictStr,
    ValidationError,
    field_validator,
    model_validator,
)
from yaml import YAMLError

from analysis.kinds import DefinitionKind

UniqueValue = TypeVar("UniqueValue", bound=Hashable)


class TaskPayloadError(ValueError):
    """Raised when a public benchmark payload cannot be read or validated."""


class TaskModel(BaseModel):
    """Strict base class for JSON values exchanged across the benchmark boundary."""

    model_config = ConfigDict(extra="forbid", frozen=True, strict=True)

    @classmethod
    def from_json_file(cls, path: Path) -> Self:
        try:
            raw = path.read_text(encoding="utf-8")
        except OSError as exc:
            raise TaskPayloadError(f"failed to read benchmark payload: {path}") from exc
        try:
            return cls.model_validate_json(raw)
        except ValidationError as exc:
            raise TaskPayloadError(_validation_message(path, exc)) from None

    def to_json_file(self, path: Path) -> None:
        try:
            path.write_text(self.model_dump_json(indent=2) + "\n", encoding="utf-8")
        except OSError as exc:
            raise TaskPayloadError(f"failed to write benchmark payload: {path}") from exc


_SAFE_ID = re.compile(r"[a-z0-9][a-z0-9._-]*")
_SAFE_DAFNY_SYMBOL = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+")


def validate_id(value: str, *, label: str = "identifier") -> str:
    if _SAFE_ID.fullmatch(value) is None:
        raise ValueError(
            f"{label} must start with a lowercase letter or digit and contain only "
            "lowercase letters, digits, '.', '_', or '-'"
        )
    return value


def validate_dafny_symbol(value: str) -> str:
    if _SAFE_DAFNY_SYMBOL.fullmatch(value) is None:
        raise ValueError("symbol must be a qualified Dafny declaration name")
    return value


def validate_relative_path(value: str, *, label: str = "path") -> str:
    path = PurePosixPath(value)
    if (
        not value
        or value != value.strip()
        or "\x00" in value
        or "\\" in value
        or value.endswith("/")
        or path.is_absolute()
        or any(part in {"", ".", ".."} for part in value.removeprefix("/").split("/"))
    ):
        raise ValueError(f"{label} must be a traversal-free workspace-relative POSIX path")
    return value


def validate_absolute_path(value: str, *, root: str, label: str) -> str:
    path = PurePosixPath(value)
    expected_root = PurePosixPath(root)
    if (
        not value
        or value != value.strip()
        or "\x00" in value
        or "\\" in value
        or value.endswith("/")
        or not path.is_absolute()
        or any(part in {"", ".", ".."} for part in value.removeprefix("/").split("/"))
        or path == expected_root
        or not path.is_relative_to(expected_root)
    ):
        raise ValueError(f"{label} must be a traversal-free absolute path below {root}")
    return value


def require_unique(values: tuple[UniqueValue, ...], *, label: str) -> tuple[UniqueValue, ...]:
    if len(values) != len(set(values)):
        raise ValueError(f"{label} must not contain duplicates")
    return values


def is_path_within(path: str, parent: str) -> bool:
    candidate = PurePosixPath(path)
    return candidate == PurePosixPath(parent) or candidate.is_relative_to(PurePosixPath(parent))


def _validation_message(path: Path, exc: ValidationError) -> str:
    errors = exc.errors(include_input=False, include_url=False)
    details = "; ".join(
        f"{'.'.join(str(part) for part in error['loc']) or '<root>'}: "
        f"{error['msg']} [{error['type']}]"
        for error in errors
    )
    kind = (
        "invalid JSON syntax"
        if any(error["type"] == "json_invalid" for error in errors)
        else "invalid benchmark payload"
    )
    return f"{kind}: {path}: {details}"


def json_compatible(value: object) -> str:
    """Serialize an already parsed YAML value using JSON input semantics for strict models."""

    return json.dumps(value, ensure_ascii=False)


class TaskResourceKind(StrEnum):
    NATURAL_SPECIFICATION = "natural-specification"
    FORMAL_SPECIFICATION = "formal-specification"
    SUPPORT = "support"


class RequiredOutputKind(StrEnum):
    IMPLEMENTATION = "implementation"
    PROOF = "proof"
    GENERATED_SOURCE = "generated-source"


class TaskProfileSchemaVersion(StrEnum):
    V2 = "benchmark.task-profile.v2"


class TaskResource(TaskModel):
    resource_id: StrictStr
    kind: TaskResourceKind
    path: StrictStr
    description: StrictStr

    @field_validator("resource_id")
    @classmethod
    def _validate_resource_id(cls, value: str) -> str:
        return validate_id(value, label="resource_id")

    @field_validator("path")
    @classmethod
    def _validate_path(cls, value: str) -> str:
        return validate_relative_path(value, label="resource path")

    @field_validator("description")
    @classmethod
    def _validate_description(cls, value: str) -> str:
        if not value.strip():
            raise ValueError("resource description must not be empty")
        return value

    @model_validator(mode="after")
    def _validate_kind_path(self) -> TaskResource:
        if self.kind is TaskResourceKind.FORMAL_SPECIFICATION and not self.path.endswith(".dfy"):
            raise ValueError("formal specification resources must be Dafny source files")
        return self


class PublicRule(TaskModel):
    rule_id: StrictStr
    title: StrictStr
    description: StrictStr

    @field_validator("rule_id")
    @classmethod
    def _validate_rule_id(cls, value: str) -> str:
        return validate_id(value, label="rule_id")

    @field_validator("title", "description")
    @classmethod
    def _validate_text(cls, value: str) -> str:
        if not value.strip():
            raise ValueError("public rule text must not be empty")
        return value


class PublicCheck(TaskModel):
    check_id: StrictStr
    title: StrictStr
    argv: tuple[StrictStr, ...]
    working_directory: StrictStr | None = None

    @field_validator("check_id")
    @classmethod
    def _validate_check_id(cls, value: str) -> str:
        return validate_id(value, label="check_id")

    @field_validator("title")
    @classmethod
    def _validate_title(cls, value: str) -> str:
        if not value.strip():
            raise ValueError("public check title must not be empty")
        return value

    @field_validator("argv")
    @classmethod
    def _validate_argv(cls, value: tuple[str, ...]) -> tuple[str, ...]:
        if not value or any(not argument or "\x00" in argument for argument in value):
            raise ValueError("public check argv must contain non-empty, NUL-free arguments")
        return value

    @field_validator("working_directory")
    @classmethod
    def _validate_working_directory(cls, value: str | None) -> str | None:
        if value is not None:
            return validate_relative_path(value, label="public check working_directory")
        return value


class DafnyEntry(TaskModel):
    source_path: StrictStr
    symbol: StrictStr

    @field_validator("source_path")
    @classmethod
    def _validate_source_path(cls, value: str) -> str:
        value = validate_relative_path(value, label="Dafny source_path")
        if not value.endswith(".dfy"):
            raise ValueError("Dafny source_path must name a .dfy file")
        return value

    @field_validator("symbol")
    @classmethod
    def _validate_symbol(cls, value: str) -> str:
        return validate_dafny_symbol(value)


class DafnyDefinition(DafnyEntry):
    kind: DefinitionKind


class DafnyEntryContract(TaskModel):
    utility_root: StrictStr
    execution_entry: DafnyEntry
    spec_entries: tuple[DafnyEntry, ...]
    spec_definitions: tuple[DafnyDefinition, ...]

    @field_validator("utility_root")
    @classmethod
    def _validate_utility_root(cls, value: str) -> str:
        return validate_relative_path(value, label="utility_root")

    @model_validator(mode="after")
    def _validate_entries(self) -> DafnyEntryContract:
        if not self.spec_entries:
            raise ValueError("spec_entries must not be empty")
        if not self.spec_definitions:
            raise ValueError("spec_definitions must not be empty")
        entries = tuple((entry.source_path, entry.symbol) for entry in self.spec_entries)
        definitions = tuple(
            (definition.source_path, definition.symbol) for definition in self.spec_definitions
        )
        require_unique(entries, label="spec_entries")
        require_unique(definitions, label="spec_definitions")
        if not is_path_within(self.execution_entry.source_path, self.utility_root):
            raise ValueError("execution entry source must be below utility_root")
        if any(entry not in set(definitions) for entry in entries):
            raise ValueError("every spec entry must be present in spec_definitions")
        return self


class RequiredOutput(TaskModel):
    kind: RequiredOutputKind
    path: StrictStr
    role: StrictStr

    @field_validator("path")
    @classmethod
    def _validate_path(cls, value: str) -> str:
        return validate_relative_path(value, label="required output path")

    @field_validator("role")
    @classmethod
    def _validate_role(cls, value: str) -> str:
        return validate_id(value, label="required output role")


class WorkspaceContract(TaskModel):
    editable_paths: tuple[StrictStr, ...]
    required_outputs: tuple[RequiredOutput, ...]

    @field_validator("editable_paths")
    @classmethod
    def _validate_editable_paths(cls, value: tuple[str, ...]) -> tuple[str, ...]:
        if not value:
            raise ValueError("editable_paths must not be empty")
        validated = tuple(validate_relative_path(path, label="editable path") for path in value)
        return require_unique(validated, label="editable_paths")

    @model_validator(mode="after")
    def _validate_outputs(self) -> WorkspaceContract:
        output_paths = tuple(output.path for output in self.required_outputs)
        require_unique(output_paths, label="required output paths")
        if any(
            not any(is_path_within(output.path, editable) for editable in self.editable_paths)
            for output in self.required_outputs
        ):
            raise ValueError("every required output must be within an editable path")
        return self


class _TaskDefinition(TaskModel):
    task_id: StrictStr
    title: StrictStr
    resources: tuple[TaskResource, ...]
    public_rules: tuple[PublicRule, ...]
    public_checks: tuple[PublicCheck, ...]
    dafny: DafnyEntryContract
    workspace: WorkspaceContract

    @field_validator("task_id")
    @classmethod
    def _validate_task_id(cls, value: str) -> str:
        return validate_id(value, label="task_id")

    @field_validator("title")
    @classmethod
    def _validate_title(cls, value: str) -> str:
        if not value.strip():
            raise ValueError("task title must not be empty")
        return value

    @model_validator(mode="after")
    def _validate_task_definition(self) -> _TaskDefinition:
        if not self.resources:
            raise ValueError("task resources must not be empty")
        require_unique(
            tuple(resource.resource_id for resource in self.resources),
            label="resource_ids",
        )
        require_unique(tuple(resource.path for resource in self.resources), label="resource paths")
        require_unique(tuple(rule.rule_id for rule in self.public_rules), label="rule_ids")
        require_unique(tuple(check.check_id for check in self.public_checks), label="check_ids")

        formal_resource_paths = {
            resource.path
            for resource in self.resources
            if resource.kind is TaskResourceKind.FORMAL_SPECIFICATION
        }
        definition_paths = {definition.source_path for definition in self.dafny.spec_definitions}
        if not definition_paths.issubset(formal_resource_paths):
            raise ValueError("every specification definition source must be a formal resource")
        output_paths = tuple(output.path for output in self.workspace.required_outputs)
        if any(
            is_path_within(formal_path, output_path) or is_path_within(output_path, formal_path)
            for formal_path in formal_resource_paths
            for output_path in output_paths
        ):
            raise ValueError("formal specification resources must not overlap required outputs")
        return self


class TaskProfile(_TaskDefinition):
    schema_version: TaskProfileSchemaVersion = Field()

    @classmethod
    def from_yaml_file(cls, path: Path) -> TaskProfile:
        try:
            raw = path.read_text(encoding="utf-8")
        except OSError as exc:
            raise TaskPayloadError(f"failed to read task profile: {path}") from exc
        try:
            parsed = yaml.safe_load(raw)
        except YAMLError as exc:
            raise TaskPayloadError(f"invalid task profile YAML: {path}: {exc}") from exc
        try:
            return cls.model_validate_json(json_compatible(parsed))
        except ValidationError as exc:
            details = "; ".join(
                f"{'.'.join(str(part) for part in error['loc']) or '<root>'}: "
                f"{error['msg']} [{error['type']}]"
                for error in exc.errors(include_input=False, include_url=False)
            )
            raise TaskPayloadError(f"invalid task profile: {path}: {details}") from None
        except TypeError as exc:
            details = str(exc)
            raise TaskPayloadError(f"invalid task profile: {path}: {details}") from None
