"""Owner-authored declarations and generated identities for public inputs."""

from enum import StrEnum
from io import StringIO
from pathlib import PurePosixPath

import yaml
from pydantic import BaseModel, ConfigDict, Field, field_validator, model_validator
from yaml.constructor import ConstructorError
from yaml.nodes import MappingNode


class Role(StrEnum):
    """Classify immutable files and excluded candidate sources."""

    SPECIFICATION = "specification"
    SUPPORT = "public-support"
    CANDIDATE = "candidate-output"
    PRIVATE = "private"


class Permission(StrEnum):
    """Describe the specific reason that a declaration needs owner review."""

    EXECUTABLE = "executable"
    PROOF = "proof"
    UNREACHABLE = "unreachable"
    TRUST = "trust"


class Model(BaseModel):
    """Reject unknown owner artifact fields."""

    model_config = ConfigDict(extra="forbid", frozen=True)


class ExceptionEntry(Model):
    """Approve specific declaration properties with a public review reason."""

    path: str
    symbol: str
    permits: tuple[Permission, ...] = Field(min_length=1)
    reason: str = Field(min_length=10)


class Obligation(Model):
    """Freeze an entry header while leaving its native method body editable."""

    path: str
    symbol: str
    signature: str = Field(min_length=1)
    hole: str = "method-body"
    candidate_outputs: tuple[str, ...] = ()

    @field_validator("hole")
    @classmethod
    def _hole_kind(cls, value: str) -> str:
        if value != "method-body":
            raise ValueError("only native method-body holes are supported")
        return value


class Manifest(Model):
    """Hold the three owner-authored parts of one public-input contract."""

    schema_version: str = "dafnyutils.public-input-manifest.v1"

    @field_validator("schema_version")
    @classmethod
    def _schema_version(cls, value: str) -> str:
        if value != "dafnyutils.public-input-manifest.v1":
            raise ValueError("unsupported manifest schema version")
        return value

    task_id: str = Field(min_length=1)
    release: str = Field(default="public-input-adoption-2026-10-28", min_length=1)
    public_roots: tuple[str, ...] = Field(min_length=1)
    obligation: Obligation
    specification_exceptions: tuple[ExceptionEntry, ...] = ()

    @model_validator(mode="after")
    def _paths(self) -> "Manifest":
        paths = (*self.public_roots, self.obligation.path, *self.obligation.candidate_outputs)
        paths += tuple(entry.path for entry in self.specification_exceptions)
        for value in paths:
            path = PurePosixPath(value)
            if path.is_absolute() or ".." in path.parts or path.as_posix() != value:
                raise ValueError(f"noncanonical repository path: {value}")
        if len(set(self.public_roots)) != len(self.public_roots):
            raise ValueError("public roots must be unique")
        keys = [(entry.path, entry.symbol) for entry in self.specification_exceptions]
        if len(set(keys)) != len(keys):
            raise ValueError("specification exceptions must be unique")
        return self


class LockedFile(Model):
    """Bind a public file's role and bytes, with an optional declared body hole."""

    path: str
    role: Role
    sha256: str = Field(pattern=r"^[0-9a-f]{64}$")
    excludes_obligation_body: bool = False


class Lock(Model):
    """Bind the complete public closure to its manifest and native producer."""

    schema_version: str = "dafnyutils.public-input-lock.v1"

    @field_validator("schema_version")
    @classmethod
    def _schema_version(cls, value: str) -> str:
        if value != "dafnyutils.public-input-lock.v1":
            raise ValueError("unsupported lock schema version")
        return value

    manifest_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")
    release: str
    checker: str
    analysis_client: str
    files: tuple[LockedFile, ...]

    @model_validator(mode="after")
    def _public_files(self) -> "Lock":
        paths = [item.path for item in self.files]
        if paths != sorted(set(paths)):
            raise ValueError("locked files must be unique and sorted")
        if not paths or sum(item.excludes_obligation_body for item in self.files) != 1:
            raise ValueError("lock must contain exactly one declared obligation hole")
        for item in self.files:
            path = PurePosixPath(item.path)
            if path.is_absolute() or ".." in path.parts or path.as_posix() != item.path:
                raise ValueError("locked file paths must be canonical repository paths")
            if item.role not in {Role.SPECIFICATION, Role.SUPPORT}:
                raise ValueError("lock contains a forbidden public role")
            if item.excludes_obligation_body and item.role is not Role.SUPPORT:
                raise ValueError("the obligation-hole file must be public support")
        return self


class TaskResult(Model):
    """Expose all release defects for one catalog task."""

    task: str
    errors: tuple[str, ...]


class Report(Model):
    """Serialize one owner maintenance result without implying release acceptance."""

    command: str
    results: tuple[TaskResult, ...]


class InitializationResult(Model):
    """Report how many new owner manifests the command authored."""

    manifests_created: int


class ProjectOptions(Model):
    """Admit only the existing fixed compilation and library policy."""

    target: str = Field(strict=True)
    no_verify: bool = Field(alias="no-verify", strict=True)
    standard_libraries: bool = Field(alias="standard-libraries", strict=True)

    @model_validator(mode="after")
    def _supported(self) -> "ProjectOptions":
        if self.target != "cs" or not self.no_verify or self.standard_libraries:
            raise ValueError("unsupported project checker/library policy")
        return self


class Project(Model):
    """Describe the owner-supported native Dafny project shape."""

    includes: tuple[str, ...]
    options: ProjectOptions


class _UniqueKeyLoader(yaml.SafeLoader):
    def construct_mapping(self, node: MappingNode, deep: bool = False) -> dict[object, object]:
        """Reject duplicate keys before returning a safely constructed YAML mapping."""
        mapping = super().construct_mapping(node, deep=deep)
        seen = set()
        for key_node, _ in node.value:
            key = self.construct_object(key_node, deep=deep)
            if key in seen:
                raise ConstructorError(
                    "while constructing a manifest mapping",
                    node.start_mark,
                    f"duplicate mapping key: {key}",
                    key_node.start_mark,
                )
            seen.add(key)
        return mapping


class _ManifestDumper(yaml.SafeDumper):
    def represent_str(self, data: str) -> yaml.nodes.ScalarNode:
        """Keep multiline signatures readable without changing their whitespace."""
        return self.represent_scalar(
            "tag:yaml.org,2002:str",
            data,
            style="|" if "\n" in data else None,
        )


_ManifestDumper.add_representer(str, _ManifestDumper.represent_str)


def manifest_from_yaml(payload: bytes | str) -> Manifest:
    """Validate an owner-authored YAML manifest without duplicate-key overwrites."""
    return Manifest.model_validate(yaml.load(payload, Loader=_UniqueKeyLoader))


def manifest_to_yaml(manifest: Manifest) -> str:
    """Serialize an owner manifest as safe YAML with exact multiline strings."""
    stream = StringIO()
    dumper = _ManifestDumper(stream, sort_keys=False, allow_unicode=True, width=100)
    try:
        dumper.open()
        dumper.represent(manifest.model_dump(mode="json"))
        dumper.close()
        return stream.getvalue()
    finally:
        dumper.dispose()
