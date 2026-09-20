#!/usr/bin/env python3
"""Create and validate generic Dafny entry-contract manifests."""

from __future__ import annotations

import argparse
import hashlib
import sys
from collections.abc import Collection, Sequence
from dataclasses import dataclass, field
from enum import StrEnum
from pathlib import Path, PurePosixPath

from pydantic import BaseModel, ConfigDict, StrictStr, field_validator, model_validator

from analysis.client import definition_analysis_document_from_paths
from analysis.kinds import DefinitionKind
from analysis.models import (
    DafnyFingerprintRegion,
    DafnyFingerprintSpan,
    DefinitionAnalysisDocument,
    DefinitionAnalysisInclude,
    DefinitionInfo,
)
from analysis.queries import (
    definition_semantic_fingerprint,
    source_semantic_fingerprint,
    spec_dependency_closure,
)
from analysis.source_fingerprints import dafny_source_fingerprints
from standard_library import dafny_standard_library_import_errors


@dataclass(frozen=True)
class DafnyEntry:
    """A configured declaration in a workspace-relative Dafny source file."""

    source_path: str
    symbol: str


class EntryValidationFailure(RuntimeError):
    """An invalid entry contract or candidate utility tree."""


class EntryContractSchemaVersion(StrEnum):
    V5 = "5"


class ManifestEntry(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, strict=True)

    source_path: StrictStr
    symbol: StrictStr


class ManifestDefinition(ManifestEntry):
    kind: DefinitionKind


class EntryContractManifest(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, strict=True)

    schema_version: EntryContractSchemaVersion
    execution_entry: ManifestEntry
    spec_entries: tuple[ManifestEntry, ...]
    spec_definitions: tuple[ManifestDefinition, ...]
    parameters: tuple[StrictStr, ...]
    returns: tuple[StrictStr, ...]
    requires: tuple[StrictStr, ...]
    ensures: tuple[StrictStr, ...]
    modifies: tuple[StrictStr, ...]
    reads: tuple[StrictStr, ...]
    decreases: tuple[StrictStr, ...]
    run_core_header_sha256: StrictStr
    project_config_sha256: StrictStr
    support_source_sha256: dict[StrictStr, StrictStr]
    execution_scaffold_sha256: StrictStr
    spec_definition_sha256: dict[StrictStr, StrictStr]

    @field_validator(
        "project_config_sha256",
        "execution_scaffold_sha256",
        "run_core_header_sha256",
    )
    @classmethod
    def _validate_optional_hash(cls, value: str | None) -> str | None:
        if value is not None and (
            len(value) != 64 or any(c not in "0123456789abcdef" for c in value)
        ):
            raise ValueError("source hashes must be lowercase SHA-256 hex digests")
        return value

    @field_validator("support_source_sha256", "spec_definition_sha256")
    @classmethod
    def _validate_spec_hashes(cls, value: dict[str, str]) -> dict[str, str]:
        if any(
            len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest)
            for digest in value.values()
        ):
            raise ValueError("source hashes must be lowercase SHA-256 hex digests")
        return value

    @model_validator(mode="after")
    def _validate_collections(self) -> EntryContractManifest:
        if not self.spec_entries or not self.spec_definitions or not self.spec_definition_sha256:
            raise ValueError(
                "specification entries, definitions, and definition hashes must not be empty"
            )
        entry_keys = [(entry.source_path, entry.symbol) for entry in self.spec_entries]
        definition_keys = [
            (definition.source_path, definition.symbol) for definition in self.spec_definitions
        ]
        if entry_keys != sorted(set(entry_keys)):
            raise ValueError("specification entries must be unique and sorted")
        if definition_keys != sorted(set(definition_keys)):
            raise ValueError("specification definitions must be unique and sorted")
        return self


@dataclass(frozen=True)
class _ResolvedContract:
    sources: tuple[Path, ...]
    analysis_sources: tuple[Path, ...]
    document: DefinitionAnalysisDocument
    infos: tuple[DefinitionInfo, ...]
    execution_source: Path
    execution: DefinitionInfo
    spec_entries: tuple[DefinitionInfo, ...]
    spec_closure: tuple[DefinitionInfo, ...]


@dataclass(frozen=True)
class EntryContractAnalysis:
    """Baseline manifest and implementation span from one Dafny analysis."""

    manifest: EntryContractManifest
    execution_source: Path
    execution: DefinitionInfo
    source_document: DefinitionAnalysisDocument
    utility_sources: tuple[Path, ...]
    analysis_sources: tuple[Path, ...] = ()


@dataclass(frozen=True)
class EntryContractSourceSnapshot:
    """Raw source identity used to bind an in-process contract result."""

    files: tuple[tuple[str, str, str], ...]
    manifest_sha256: str
    utility_sources: tuple[tuple[str, str], ...] = ()


@dataclass
class EntryContractCheckSession:
    """Validate one manifest once and safely reuse it for one source snapshot."""

    workspace_root: Path
    utility_root: Path
    manifest: EntryContractManifest
    tool_identity: str | None = None
    verification_options: tuple[str, ...] = ()
    _snapshot: EntryContractSourceSnapshot | None = field(
        default=None,
        init=False,
        repr=False,
        compare=False,
    )
    _contract: ValidatedEntryContract | None = field(
        default=None,
        init=False,
        repr=False,
        compare=False,
    )

    def __post_init__(self) -> None:
        workspace_root = self.workspace_root.resolve()
        utility_root = (workspace_root / self.utility_root).resolve()
        self.workspace_root = workspace_root
        self.utility_root = utility_root

    def validate(self) -> ValidatedEntryContract:
        """Return the checked contract, rejecting reuse after any raw source change."""
        current = _entry_contract_source_snapshot(
            self.workspace_root,
            self.utility_root,
            self.manifest,
            contract=self._contract,
            all_workspace_sources=self._contract is None,
        )
        if self._contract is not None:
            if current != self._snapshot:
                raise EntryValidationFailure(
                    "workspace source snapshot changed since contract validation"
                )
            return self._contract

        contract = validated_entry_contract(
            self.workspace_root,
            self.utility_root,
            self.manifest,
        )
        after = _entry_contract_source_snapshot(
            self.workspace_root,
            self.utility_root,
            self.manifest,
            contract=contract,
        )
        if not _snapshot_matches_known_files(current, after):
            raise EntryValidationFailure("workspace source snapshot changed during validation")
        self._contract = contract
        self._snapshot = after
        return contract


@dataclass(frozen=True)
class ValidatedEntryContract:
    """Validated entry source and candidate-editable sources reachable from it."""

    execution_source: Path
    utility_sources: tuple[Path, ...]
    verification_sources: tuple[Path, ...]
    verification_definitions: tuple[DefinitionInfo, ...]
    analysis_sources: tuple[Path, ...] = ()


def _safe_workspace_path(workspace_root: Path, source_path: str) -> Path:
    relative = PurePosixPath(source_path)
    if (
        not source_path
        or source_path != source_path.strip()
        or "\\" in source_path
        or source_path.endswith("/")
        or relative.is_absolute()
        or any(part in {"", ".", ".."} for part in relative.parts)
        or relative.suffix != ".dfy"
    ):
        raise EntryValidationFailure("source path must be a workspace-relative Dafny source")
    candidate = (workspace_root / relative).resolve()
    if not candidate.is_relative_to(workspace_root):
        raise EntryValidationFailure("source path escapes the workspace root")
    if not candidate.is_file():
        raise EntryValidationFailure(f"configured source is missing: {candidate}")
    return candidate


def _safe_execution_path(
    workspace_root: Path,
    utility_root: Path,
    source_path: str,
) -> Path:
    source = _safe_workspace_path(workspace_root, source_path)
    if not source.is_relative_to(utility_root):
        raise EntryValidationFailure("execution entry source is outside the utility root")
    return source


def enumerate_dafny_sources(workspace_root: Path, utility_root: Path) -> tuple[Path, ...]:
    """Return every utility-local Dafny source once, sorted and workspace-confined."""
    workspace_root = workspace_root.resolve()
    utility_root = utility_root.resolve()
    if not utility_root.is_relative_to(workspace_root):
        raise EntryValidationFailure("utility root escapes the workspace")
    resolved_sources: set[Path] = set()
    for path in utility_root.rglob("*.dfy"):
        if path.is_symlink():
            raise EntryValidationFailure(f"utility Dafny source must not be a symlink: {path}")
        # Evaluator-owned runtime tests are not candidate task sources.
        if path == utility_root / "Tests.dfy":
            continue
        resolved = path.resolve()
        if not resolved.is_relative_to(utility_root):
            raise EntryValidationFailure(
                f"utility Dafny source resolves outside the utility root: {path}"
            )
        if resolved.is_file():
            resolved_sources.add(resolved)
    sources = tuple(sorted(resolved_sources))
    if not sources:
        raise EntryValidationFailure(f"utility root has no Dafny sources: {utility_root}")
    return sources


def _analyze_document(
    sources: tuple[Path, ...],
) -> DefinitionAnalysisDocument:
    try:
        return definition_analysis_document_from_paths(sources)
    except (OSError, RuntimeError, ValueError) as error:
        raise EntryValidationFailure(f"Dafny definition analysis failed: {error}") from error


def _validate_includes(
    workspace_root: Path,
    includes: tuple[DefinitionAnalysisInclude, ...],
) -> None:
    for include in includes:
        source = Path(include.source_path).resolve()
        target = Path(include.target_path).resolve()
        if not source.is_relative_to(workspace_root):
            raise EntryValidationFailure(
                f"{include.source_path} includes a source outside the workspace: "
                f"{include.target_path}"
            )
        if source.suffix != ".dfy" or not source.is_file():
            raise EntryValidationFailure(
                f"include source is missing Dafny source: {include.source_path}"
            )
        if not target.is_relative_to(workspace_root):
            raise EntryValidationFailure(
                f"{include.source_path} includes a source outside the workspace: "
                f"{include.target_path}"
            )
        if target.suffix != ".dfy" or not target.is_file():
            raise EntryValidationFailure(
                f"{include.source_path} includes a missing Dafny source: {include.target_path}"
            )


def _reachable_sources(
    execution_source: Path,
    includes: tuple[DefinitionAnalysisInclude, ...],
) -> frozenset[Path]:
    include_targets: dict[Path, set[Path]] = {}
    for include in includes:
        source = Path(include.source_path).resolve()
        include_targets.setdefault(source, set()).add(Path(include.target_path).resolve())

    reachable = {execution_source.resolve()}
    pending = [execution_source.resolve()]
    while pending:
        source = pending.pop()
        for target in include_targets.get(source, ()):
            if target not in reachable:
                reachable.add(target)
                pending.append(target)
    return frozenset(reachable)


def _trust_scan(sources: tuple[Path, ...], infos: tuple[DefinitionInfo, ...]) -> None:
    source_names = {str(path) for path in sources}
    for info in infos:
        if info.source_path not in source_names:
            continue
        if info.has_assume_statement or info.has_axiom_attribute or info.has_extern_attribute:
            raise EntryValidationFailure(
                f"{info.source_path} contains a trusted proof shortcut in {info.full_name}"
            )
        if info.has_verify_false_attribute:
            raise EntryValidationFailure(
                f"{info.source_path} disables verification in {info.full_name}"
            )


def _resolve_entry(
    infos: tuple[DefinitionInfo, ...], source: Path, entry: DafnyEntry
) -> DefinitionInfo:
    matches = [
        info for info in infos if info.full_name == entry.symbol and info.source_path == str(source)
    ]
    if len(matches) != 1:
        raise EntryValidationFailure(
            f"{source} does not resolve configured entry exactly once: {entry.symbol}"
        )
    return matches[0]


def _resolved_contract(
    workspace_root: Path,
    utility_root: Path,
    execution_entry: DafnyEntry,
    additional_analysis_sources: Collection[Path] = (),
) -> _ResolvedContract:
    workspace_root = workspace_root.resolve()
    utility_root = utility_root.resolve()
    sources = enumerate_dafny_sources(workspace_root, utility_root)
    execution_source = _safe_execution_path(
        workspace_root, utility_root, execution_entry.source_path
    )
    resolved = _resolve_contract(
        sources, execution_source, execution_entry, additional_analysis_sources
    )
    _validate_includes(workspace_root, resolved.document.source_facts.includes)
    return resolved


def _resolve_contract(
    sources: tuple[Path, ...],
    execution_source: Path,
    execution_entry: DafnyEntry,
    additional_analysis_sources: Collection[Path],
) -> _ResolvedContract:
    analysis_inputs = tuple(
        sorted(set(sources) | {path.resolve() for path in additional_analysis_sources})
    )
    document = _analyze_document(analysis_inputs)
    standard_library_errors = dafny_standard_library_import_errors(
        document.source_facts.imports,
        selected_source_paths=tuple(str(path) for path in analysis_inputs),
    )
    if standard_library_errors:
        raise EntryValidationFailure("; ".join(standard_library_errors))
    infos = tuple(document.definitions)
    _trust_scan(sources, infos)
    execution = _resolve_entry(infos, execution_source, execution_entry)
    if (
        execution.kind is not DefinitionKind.METHOD
        or execution.name != "RunCore"
        or execution.body_start is None
    ):
        raise EntryValidationFailure(
            "execution entry must resolve to a method named RunCore with a body"
        )
    by_full_name = {info.full_name: info for info in infos}
    spec_entry_names = sorted(
        set(execution.direct_precondition_callees) | set(execution.direct_postcondition_callees)
    )
    spec_entries: list[DefinitionInfo] = []
    for full_name in spec_entry_names:
        info = by_full_name.get(full_name)
        if info is None:
            raise EntryValidationFailure(
                f"RunCore specification call does not resolve: {full_name}"
            )
        spec_entries.append(info)
    try:
        closure = spec_dependency_closure(
            infos,
            source_paths=analysis_inputs,
            spec_entries=tuple((Path(info.source_path), info.full_name) for info in spec_entries),
        )
    except RuntimeError as error:
        raise EntryValidationFailure(str(error)) from error
    return _ResolvedContract(
        sources,
        analysis_inputs,
        document,
        infos,
        execution_source,
        execution,
        tuple(spec_entries),
        closure,
    )


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _entry_contract_source_snapshot(
    workspace_root: Path,
    utility_root: Path,
    manifest: EntryContractManifest,
    *,
    contract: ValidatedEntryContract | None = None,
    additional_sources: Collection[Path] = (),
    all_workspace_sources: bool = False,
) -> EntryContractSourceSnapshot:
    """Capture raw bytes for every source that can affect entry validation."""
    workspace_root = workspace_root.resolve()
    utility_root = utility_root.resolve()
    utility_sources = enumerate_dafny_sources(workspace_root, utility_root)
    support_paths = tuple(
        (relative, _safe_workspace_path(workspace_root, relative))
        for relative in manifest.support_source_sha256
    )
    support_sources = tuple(source for _, source in support_paths)
    analyzed_sources = () if contract is None else contract.analysis_sources
    project_config = _project_config(utility_root)
    if not project_config.is_relative_to(workspace_root):
        raise EntryValidationFailure("project configuration escapes the workspace root")
    additional_paths: list[Path] = []
    additional_aliases: dict[Path, set[str]] = {}
    for path in (*analyzed_sources, *additional_sources):
        lexical = path if path.is_absolute() else workspace_root / path
        resolved = lexical.resolve()
        if not lexical.is_relative_to(workspace_root):
            raise EntryValidationFailure(f"contract input source escapes workspace: {lexical}")
        if not resolved.is_relative_to(workspace_root) or not lexical.is_file():
            raise EntryValidationFailure(f"contract input source is invalid: {lexical}")
        additional_paths.append(resolved)
        additional_aliases.setdefault(resolved, set()).add(
            lexical.relative_to(workspace_root).as_posix()
        )
    workspace_source_aliases: dict[Path, set[str]] = {}
    if all_workspace_sources:
        for path in workspace_root.rglob("*.dfy"):
            try:
                resolved = path.resolve()
            except (OSError, RuntimeError):
                continue
            if not resolved.is_relative_to(workspace_root) or not resolved.is_file():
                continue
            workspace_source_aliases.setdefault(resolved, set()).add(
                path.relative_to(workspace_root).as_posix()
            )
    sources = tuple(
        sorted(
            {
                *utility_sources,
                *support_sources,
                *additional_paths,
                project_config,
                *workspace_source_aliases,
            }
        )
    )
    aliases: dict[Path, set[str]] = {
        source: {
            source.relative_to(workspace_root).as_posix(),
            *workspace_source_aliases.get(source, ()),
            *additional_aliases.get(source, ()),
        }
        for source in sources
    }
    for relative, source in support_paths:
        aliases.setdefault(source, set()).add(relative)
    files = tuple(
        (relative, source.relative_to(workspace_root).as_posix(), _sha256(source))
        for source in sources
        for relative in sorted(aliases[source])
    )
    manifest_sha256 = hashlib.sha256(manifest.model_dump_json().encode("utf-8")).hexdigest()
    utility_source_keys = tuple(
        (
            source.relative_to(workspace_root).as_posix(),
            source.relative_to(workspace_root).as_posix(),
        )
        for source in utility_sources
    )
    return EntryContractSourceSnapshot(
        files=files,
        manifest_sha256=manifest_sha256,
        utility_sources=utility_source_keys,
    )


def entry_contract_source_snapshot(
    workspace_root: Path,
    utility_root: Path,
    manifest: EntryContractManifest,
    *,
    additional_sources: Collection[Path] = (),
    all_workspace_sources: bool = False,
) -> EntryContractSourceSnapshot:
    """Capture raw source identity for a prepared contract input snapshot."""
    return _entry_contract_source_snapshot(
        workspace_root,
        utility_root,
        manifest,
        additional_sources=additional_sources,
        all_workspace_sources=all_workspace_sources,
    )


def _snapshot_matches_known_files(
    before: EntryContractSourceSnapshot,
    after: EntryContractSourceSnapshot,
) -> bool:
    """Ensure every source consumed after analysis matched the initial snapshot."""
    before_files = {(logical, resolved): digest for logical, resolved, digest in before.files}
    after_files = {(logical, resolved): digest for logical, resolved, digest in after.files}
    return (
        before.manifest_sha256 == after.manifest_sha256
        and before.utility_sources == after.utility_sources
        and all(before_files.get(key) == digest for key, digest in after_files.items())
    )


def _project_config(utility_root: Path) -> Path:
    path = utility_root / "dfyconfig.toml"
    if path.is_symlink() or not path.is_file():
        raise EntryValidationFailure(f"project configuration is missing: {path}")
    return path


def _masked_sha256(
    path: Path,
    info: DefinitionInfo,
) -> str:
    assert info.body_start is not None
    try:
        return dafny_source_fingerprints(
            (
                DafnyFingerprintRegion(
                    id="execution-scaffold",
                    sourcePath=str(path),
                    includedSpan=None,
                    excludedSpans=(DafnyFingerprintSpan(start=info.body_start, end=info.end),),
                ),
            ),
            cwd=path.parent,
        )["execution-scaffold"]
    except (OSError, RuntimeError, ValueError) as error:
        raise EntryValidationFailure(
            f"Dafny execution scaffold fingerprinting failed: {error}"
        ) from error


def _definition_sha256(
    document: DefinitionAnalysisDocument,
    info: DefinitionInfo,
) -> str:
    return definition_semantic_fingerprint(
        document.source_facts,
        info,
    ).declaration_sha256


def _run_core_header_sha256(
    document: DefinitionAnalysisDocument,
    info: DefinitionInfo,
) -> str:
    assert info.body_start is not None
    return definition_semantic_fingerprint(document.source_facts, info).contract_sha256


def _definition_hash_key(workspace_root: Path, info: DefinitionInfo) -> str:
    source_path = Path(info.source_path).resolve().relative_to(workspace_root).as_posix()
    return f"{source_path}::{info.full_name}"


def _manifest_entry(workspace_root: Path, info: DefinitionInfo) -> ManifestEntry:
    source_path = Path(info.source_path).resolve().relative_to(workspace_root).as_posix()
    return ManifestEntry(source_path=source_path, symbol=info.full_name)


def _manifest_definition(workspace_root: Path, info: DefinitionInfo) -> ManifestDefinition:
    entry = _manifest_entry(workspace_root, info)
    return ManifestDefinition(
        source_path=entry.source_path,
        symbol=entry.symbol,
        kind=info.kind,
    )


def _resolved_analysis_sources(resolved: _ResolvedContract) -> tuple[Path, ...]:
    return tuple(
        sorted(
            {
                *resolved.analysis_sources,
                *(Path(include.source_path) for include in resolved.document.source_facts.includes),
                *(Path(include.target_path) for include in resolved.document.source_facts.includes),
                *(
                    Path(include.source_path).resolve()
                    for include in resolved.document.source_facts.includes
                ),
                *(
                    Path(include.target_path).resolve()
                    for include in resolved.document.source_facts.includes
                ),
            }
        )
    )


def _entry(entry: ManifestEntry) -> DafnyEntry:
    return DafnyEntry(entry.source_path, entry.symbol)


def analyze_entry_contract(
    workspace_root: Path,
    utility_root: Path,
    execution_entry: DafnyEntry,
    support_source_paths: Collection[Path] = (),
) -> EntryContractAnalysis:
    """Analyze one execution entry and derive its specification roots and closure."""
    workspace_root = workspace_root.resolve()
    support_sources = tuple(sorted({path.resolve() for path in support_source_paths}))
    for source in support_sources:
        if not source.is_relative_to(workspace_root) or not source.is_file():
            raise EntryValidationFailure(f"build support source is invalid: {source}")
    resolved = _resolved_contract(
        workspace_root,
        utility_root,
        execution_entry,
        support_sources,
    )
    manifest = EntryContractManifest(
        schema_version=EntryContractSchemaVersion.V5,
        execution_entry=_manifest_entry(workspace_root, resolved.execution),
        spec_entries=tuple(
            sorted(
                (_manifest_entry(workspace_root, info) for info in resolved.spec_entries),
                key=lambda entry: (entry.source_path, entry.symbol),
            )
        ),
        spec_definitions=tuple(
            sorted(
                (_manifest_definition(workspace_root, info) for info in resolved.spec_closure),
                key=lambda definition: (definition.source_path, definition.symbol),
            )
        ),
        parameters=resolved.execution.parameters,
        returns=resolved.execution.returns,
        requires=resolved.execution.requires,
        ensures=resolved.execution.ensures,
        modifies=resolved.execution.modifies,
        reads=resolved.execution.reads,
        decreases=resolved.execution.decreases,
        run_core_header_sha256=_run_core_header_sha256(resolved.document, resolved.execution),
        project_config_sha256=_sha256(_project_config(utility_root)),
        support_source_sha256={
            path.relative_to(workspace_root).as_posix(): source_semantic_fingerprint(
                resolved.document.source_facts,
                path,
            ).full_sha256
            for path in support_sources
            if path != resolved.execution_source
        },
        execution_scaffold_sha256=_masked_sha256(
            resolved.execution_source,
            resolved.execution,
        ),
        spec_definition_sha256={
            _definition_hash_key(workspace_root, info): _definition_sha256(
                resolved.document,
                info,
            )
            for info in resolved.spec_closure
        },
    )
    return EntryContractAnalysis(
        manifest=manifest,
        execution_source=resolved.execution_source,
        execution=resolved.execution,
        source_document=resolved.document,
        utility_sources=resolved.sources,
        analysis_sources=_resolved_analysis_sources(resolved),
    )


def create_manifest(
    workspace_root: Path,
    utility_root: Path,
    execution_entry: DafnyEntry,
    support_source_paths: Collection[Path] = (),
) -> EntryContractManifest:
    """Create a fail-closed baseline for one derived entry contract."""
    return analyze_entry_contract(
        workspace_root,
        utility_root,
        execution_entry,
        support_source_paths,
    ).manifest


def validated_entry_contract(
    workspace_root: Path,
    utility_root: Path,
    manifest: EntryContractManifest,
) -> ValidatedEntryContract:
    """Validate a candidate and derive its entry-reachable local declarations."""
    if _sha256(_project_config(utility_root)) != manifest.project_config_sha256:
        raise EntryValidationFailure("project configuration changed")
    workspace_root = workspace_root.resolve()
    support_sources = tuple(
        _safe_workspace_path(workspace_root, relative)
        for relative in manifest.support_source_sha256
    )
    resolved = _resolved_contract(
        workspace_root,
        utility_root,
        _entry(manifest.execution_entry),
        support_sources,
    )
    if (
        _run_core_header_sha256(resolved.document, resolved.execution)
        != manifest.run_core_header_sha256
    ):
        raise EntryValidationFailure("RunCore semantic header changed")
    if (
        resolved.execution.parameters != manifest.parameters
        or resolved.execution.returns != manifest.returns
        or resolved.execution.requires != manifest.requires
        or resolved.execution.ensures != manifest.ensures
        or resolved.execution.modifies != manifest.modifies
        or resolved.execution.reads != manifest.reads
        or resolved.execution.decreases != manifest.decreases
    ):
        raise EntryValidationFailure("RunCore structured contract changed")
    if (
        _masked_sha256(resolved.execution_source, resolved.execution)
        != manifest.execution_scaffold_sha256
    ):
        raise EntryValidationFailure("execution scaffold changed outside RunCore body")
    current_entries = tuple(
        sorted(
            (_manifest_entry(workspace_root, info) for info in resolved.spec_entries),
            key=lambda entry: (entry.source_path, entry.symbol),
        )
    )
    current_definitions = tuple(
        sorted(
            (_manifest_definition(workspace_root, info) for info in resolved.spec_closure),
            key=lambda definition: (definition.source_path, definition.symbol),
        )
    )
    if current_entries != manifest.spec_entries:
        raise EntryValidationFailure("RunCore specification entries changed")
    if current_definitions != manifest.spec_definitions:
        raise EntryValidationFailure("specification definition closure changed")
    current_support_hashes = {
        relative: source_semantic_fingerprint(
            resolved.document.source_facts,
            _safe_workspace_path(workspace_root, relative),
        ).full_sha256
        for relative in manifest.support_source_sha256
    }
    if current_support_hashes != manifest.support_source_sha256:
        raise EntryValidationFailure("build support source changed")
    current_definition_hashes = {
        _definition_hash_key(workspace_root, info): _definition_sha256(
            resolved.document,
            info,
        )
        for info in resolved.spec_closure
    }
    if current_definition_hashes != manifest.spec_definition_sha256:
        raise EntryValidationFailure("specification definition changed")

    immutable_sources = {
        _safe_workspace_path(workspace_root, path)
        for path in (
            *manifest.support_source_sha256,
            *(definition.source_path for definition in manifest.spec_definitions),
        )
    }
    return _verification_contract(resolved, immutable_sources)


def _verification_contract(
    resolved: _ResolvedContract, immutable_sources: set[Path]
) -> ValidatedEntryContract:
    local_sources = set(resolved.sources)
    reachable_sources = _reachable_sources(
        resolved.execution_source,
        resolved.document.source_facts.includes,
    )
    verification_sources = tuple(sorted((local_sources & reachable_sources) - immutable_sources))
    verification_definitions = tuple(
        info for info in resolved.infos if Path(info.source_path).resolve() in verification_sources
    )
    return ValidatedEntryContract(
        execution_source=resolved.execution_source,
        utility_sources=resolved.sources,
        verification_sources=verification_sources,
        verification_definitions=verification_definitions,
        analysis_sources=_resolved_analysis_sources(resolved),
    )


def project_verification_contract(
    project: Path,
    execution_entry: DafnyEntry,
    support_sources: Collection[Path] = (),
) -> ValidatedEntryContract:
    """Resolve a local project's proof surface from explicit source dependencies."""
    project = project.resolve()
    _project_config(project)
    sources = enumerate_dafny_sources(project, project)
    execution_source = _safe_execution_path(project, project, execution_entry.source_path)
    support = {path.resolve() for path in support_sources}
    for source in support:
        if not source.is_file() or source.suffix != ".dfy":
            raise EntryValidationFailure(f"build support source is invalid: {source}")
    resolved = _resolve_contract(sources, execution_source, execution_entry, support)
    allowed_sources = set(resolved.analysis_sources)
    for include in resolved.document.source_facts.includes:
        if Path(include.target_path).resolve() not in allowed_sources:
            raise EntryValidationFailure(
                f"include is outside project dependencies: {include.target_path}"
            )
    immutable = support | {Path(info.source_path).resolve() for info in resolved.spec_closure}
    return _verification_contract(resolved, immutable)


def validate_manifest(
    workspace_root: Path,
    utility_root: Path,
    manifest: EntryContractManifest,
) -> tuple[Path, ...]:
    """Validate a candidate and return its complete utility-local Dafny source set."""
    return validated_entry_contract(workspace_root, utility_root, manifest).utility_sources


def contract_check_session(
    workspace_root: Path,
    utility_root: Path,
    manifest: EntryContractManifest,
    *,
    tool_identity: str | None = None,
    verification_options: tuple[str, ...] = (),
) -> EntryContractCheckSession:
    """Create an object-scoped checker for one manifest and candidate workspace."""
    return EntryContractCheckSession(
        workspace_root,
        utility_root,
        manifest,
        tool_identity=tool_identity,
        verification_options=verification_options,
    )


def _entry_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--workspace-root", default=".", type=Path)
    parser.add_argument("--utility-root", required=True, type=Path)
    parser.add_argument("--execution-source", required=True)
    parser.add_argument("--execution-symbol", required=True)
    parser.add_argument("--support-source", action="append", default=[])


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("create-manifest")
    _entry_arguments(create)
    create.add_argument("--output", required=True, type=Path)
    check = commands.add_parser("check")
    check.add_argument("--workspace-root", default=".", type=Path)
    check.add_argument("--utility-root", required=True, type=Path)
    check.add_argument("--manifest", required=True, type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    workspace_root = args.workspace_root.resolve()
    utility_root = (workspace_root / args.utility_root).resolve()
    try:
        if args.command == "create-manifest":
            manifest = create_manifest(
                workspace_root,
                utility_root,
                DafnyEntry(args.execution_source, args.execution_symbol),
                tuple((workspace_root / path).resolve() for path in args.support_source),
            )
            args.output.write_text(manifest.model_dump_json(indent=2) + "\n", encoding="utf-8")
        else:
            manifest = EntryContractManifest.model_validate_json(
                args.manifest.read_text(encoding="utf-8")
            )
            contract_check_session(workspace_root, utility_root, manifest).validate()
    except (EntryValidationFailure, OSError, ValueError) as error:
        print(f"[fail] {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
