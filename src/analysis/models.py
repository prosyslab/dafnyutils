"""Pydantic models used by the Dafny analysis adapters.

This module intentionally has no subprocess or Dafny-tool imports.  Protocol
consumers can import :class:`DefinitionKind` without importing the external
analysis client.
"""

from __future__ import annotations

from functools import cached_property
from pathlib import Path

from pydantic import BaseModel, ConfigDict, Field, StrictBool, StrictInt, StrictStr, TypeAdapter

from .kinds import DefinitionKind


class DafnyFingerprintSpan(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, strict=True)

    start: StrictInt
    end: StrictInt


class DafnyFingerprintRegion(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True, strict=True)

    region_id: StrictStr = Field(alias="id")
    source_path: StrictStr = Field(alias="sourcePath")
    included_span: DafnyFingerprintSpan | None = Field(default=None, alias="includedSpan")
    excluded_spans: tuple[DafnyFingerprintSpan, ...] = Field(alias="excludedSpans")


class DafnyFingerprintRequest(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, strict=True)

    regions: tuple[DafnyFingerprintRegion, ...]


class DafnyFingerprintResult(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, strict=True)

    id: StrictStr
    sha256: StrictStr


class DafnyFingerprintDocument(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, strict=True)

    fingerprints: tuple[DafnyFingerprintResult, ...]


class DefinitionAnalysisInclude(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    source_path: StrictStr = Field(alias="sourcePath")
    target_path: StrictStr = Field(alias="targetPath")
    start: StrictInt
    end: StrictInt


class DefinitionAnalysisModule(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    name: StrictStr
    source_path: StrictStr = Field(alias="sourcePath")
    body_start: StrictInt = Field(alias="bodyStart")
    body_end: StrictInt = Field(alias="bodyEnd")


class DefinitionAnalysisImport(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    module_name: StrictStr = Field(alias="moduleName")
    alias: StrictStr
    has_alias: StrictBool = Field(alias="hasAlias")
    resolved_target: StrictStr = Field(alias="resolvedTarget")
    resolved_target_source_path: StrictStr = Field(alias="resolvedTargetSourcePath")
    opened: StrictBool
    source_path: StrictStr = Field(alias="sourcePath")
    start: StrictInt
    end: StrictInt


class DafnySourceSemanticFingerprint(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    source_path: StrictStr = Field(alias="sourcePath")
    full_sha256: StrictStr = Field(alias="fullSha256")
    declaration_scaffold_sha256: StrictStr = Field(alias="declarationScaffoldSha256")
    scaffold_sha256: StrictStr = Field(alias="scaffoldSha256")


class DafnyDefinitionSemanticFingerprint(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    source_path: StrictStr = Field(alias="sourcePath")
    full_name: StrictStr = Field(alias="fullName")
    kind: DefinitionKind
    declaration_sha256: StrictStr = Field(alias="declarationSha256")
    contract_sha256: StrictStr = Field(alias="contractSha256")
    body_sha256: StrictStr = Field(alias="bodySha256")


class DafnySemanticFacts(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    sources: tuple[DafnySourceSemanticFingerprint, ...]
    definitions: tuple[DafnyDefinitionSemanticFingerprint, ...]

    @cached_property
    def sources_by_path(self) -> dict[Path, tuple[DafnySourceSemanticFingerprint, ...]]:
        found: dict[Path, list[DafnySourceSemanticFingerprint]] = {}
        for source in self.sources:
            found.setdefault(Path(source.source_path).resolve(), []).append(source)
        return {path: tuple(items) for path, items in found.items()}

    @cached_property
    def definitions_by_key(
        self,
    ) -> dict[
        tuple[Path, str, DefinitionKind],
        tuple[DafnyDefinitionSemanticFingerprint, ...],
    ]:
        found: dict[
            tuple[Path, str, DefinitionKind],
            list[DafnyDefinitionSemanticFingerprint],
        ] = {}
        for definition in self.definitions:
            key = (
                Path(definition.source_path).resolve(),
                definition.full_name,
                definition.kind,
            )
            found.setdefault(key, []).append(definition)
        return {key: tuple(items) for key, items in found.items()}


class DefinitionSourceFacts(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    modules: tuple[DefinitionAnalysisModule, ...]
    imports: tuple[DefinitionAnalysisImport, ...]
    includes: tuple[DefinitionAnalysisInclude, ...]
    semantic_facts: DafnySemanticFacts | None = Field(default=None, alias="semanticFacts")


class DefinitionFormal(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    name: StrictStr
    type: StrictStr
    ghost: StrictBool


class DefinitionAttribute(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True)

    name: StrictStr
    arguments: tuple[StrictStr, ...]
    start: StrictInt
    end: StrictInt


class DefinitionStatement(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    kind: StrictStr
    start: StrictInt
    end: StrictInt
    direct_call_targets: tuple[StrictStr, ...] = Field(alias="directCallTargets")


class DefinitionControlContext(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    kind: StrictStr
    start: StrictInt
    end: StrictInt
    branch_index: StrictInt = Field(alias="branchIndex")
    branch_count: StrictInt = Field(alias="branchCount")
    other_branch_statement_count: StrictInt = Field(alias="otherBranchStatementCount")
    guard: StrictStr
    invariants: tuple[StrictStr, ...]
    decreases: tuple[StrictStr, ...]


class DefinitionCallSite(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    target_full_name: StrictStr = Field(alias="targetFullName")
    start: StrictInt
    end: StrictInt
    arguments: tuple[StrictStr, ...]
    assigned_names: tuple[StrictStr, ...] = Field(alias="assignedNames")
    control_path: tuple[DefinitionControlContext, ...] = Field(alias="controlPath")


class DefinitionContractClause(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    kind: StrictStr
    index: StrictInt
    text: StrictStr
    has_existential: StrictBool = Field(alias="hasExistential")
    has_old: StrictBool = Field(alias="hasOld")
    referenced_variables: tuple[StrictStr, ...] = Field(alias="referencedVariables")
    referenced_members: tuple[StrictStr, ...] = Field(alias="referencedMembers")
    index_selections: tuple[StrictStr, ...] = Field(alias="indexSelections")
    index_selection_count: StrictInt = Field(alias="indexSelectionCount")


class DefinitionMemberAssignment(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    start: StrictInt
    end: StrictInt
    target_full_name: StrictStr = Field(alias="targetFullName")
    receiver_type: StrictStr = Field(alias="receiverType")
    target_is_ghost: StrictBool = Field(alias="targetIsGhost")


class DefinitionPostconditionCall(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    target_full_name: StrictStr = Field(alias="targetFullName")
    start: StrictInt
    end: StrictInt
    text: StrictStr
    arguments: tuple[StrictStr | None, ...]


class DefinitionPreconditionCall(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    target_full_name: StrictStr = Field(alias="targetFullName")
    start: StrictInt
    end: StrictInt
    text: StrictStr
    arguments: tuple[StrictStr | None, ...]


class DefinitionReference(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    target_full_name: StrictStr = Field(alias="targetFullName")
    target_module: StrictStr = Field(alias="targetModule")
    target_kind: DefinitionKind = Field(alias="targetKind")
    is_pattern: StrictBool = Field(alias="isPattern")
    start: StrictInt
    end: StrictInt


class DefinitionInfo(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    name: StrictStr
    full_name: StrictStr = Field(alias="fullName")
    kind: DefinitionKind
    enclosing_name: StrictStr = Field(alias="enclosingName")
    line: StrictInt
    column: StrictInt
    start: StrictInt
    body_start: StrictInt | None = Field(alias="bodyStart")
    end: StrictInt
    source_path: StrictStr = Field(default="", alias="sourcePath")
    ghost: StrictBool
    has_by_method: StrictBool = Field(alias="hasByMethod")
    has_loop: StrictBool = Field(alias="hasLoop")
    world_related: StrictBool = Field(alias="worldRelated")
    declaration_kind: StrictStr = Field(default="", alias="declarationKind")
    has_axiom_attribute: StrictBool = Field(default=False, alias="hasAxiomAttribute")
    has_extern_attribute: StrictBool = Field(default=False, alias="hasExternAttribute")
    has_verify_false_attribute: StrictBool = Field(
        default=False,
        alias="hasVerifyFalseAttribute",
    )
    attributes: tuple[DefinitionAttribute, ...] = ()
    has_assume_statement: StrictBool = Field(default=False, alias="hasAssumeStatement")
    has_var_declaration: StrictBool = Field(default=False, alias="hasVarDeclaration")
    statements: tuple[DefinitionStatement, ...] = ()
    member_assignments: tuple[DefinitionMemberAssignment, ...] = Field(
        default=(), alias="memberAssignments"
    )
    call_sites: tuple[DefinitionCallSite, ...] = Field(default=(), alias="callSites")
    contract_clauses: tuple[DefinitionContractClause, ...] = Field(
        default=(), alias="contractClauses"
    )
    body_shape: StrictStr = Field(default="", alias="bodyShape")
    has_broad_exit_range_disjunct: StrictBool = Field(
        default=False,
        alias="hasBroadExitRangeDisjunct",
    )
    type_parameters: tuple[StrictStr, ...] = Field(default=(), alias="typeParameters")
    type_parameter_names: tuple[StrictStr, ...] = Field(
        default=(),
        alias="typeParameterNames",
    )
    parameters: tuple[StrictStr, ...] = ()
    parameter_names: tuple[StrictStr, ...] = Field(default=(), alias="parameterNames")
    returns: tuple[StrictStr, ...]
    return_names: tuple[StrictStr, ...] = Field(alias="returnNames")
    requires: tuple[StrictStr, ...]
    ensures: tuple[StrictStr, ...]
    modifies: tuple[StrictStr, ...]
    parameter_details: tuple[DefinitionFormal, ...] = Field(default=(), alias="parameterDetails")
    return_details: tuple[DefinitionFormal, ...] = Field(default=(), alias="returnDetails")
    reads: tuple[StrictStr, ...] = ()
    decreases: tuple[StrictStr, ...] = ()
    source_modules: tuple[StrictStr, ...] = Field(default=(), alias="sourceModules")
    included_files: tuple[StrictStr, ...] = Field(default=(), alias="includedFiles")
    local_included_modules: tuple[StrictStr, ...] = Field(
        default=(),
        alias="localIncludedModules",
    )
    imported_modules: tuple[StrictStr, ...] = Field(default=(), alias="importedModules")
    local_includes: tuple[DefinitionAnalysisInclude, ...] = Field(
        default=(),
        alias="localIncludes",
    )
    recursive: StrictBool
    recursive_group: tuple[StrictStr, ...] = Field(alias="recursiveGroup")
    callees: tuple[StrictStr, ...]
    call_sequence: tuple[StrictStr, ...] = Field(default=(), alias="callSequence")
    call_names: tuple[StrictStr, ...] = Field(default=(), alias="callNames")
    direct_precondition_callees: tuple[StrictStr, ...] = Field(
        default=(),
        alias="directPreconditionCallees",
    )
    direct_precondition_calls: tuple[DefinitionPreconditionCall, ...] = Field(
        default=(), alias="directPreconditionCalls"
    )
    direct_postcondition_callees: tuple[StrictStr, ...] = Field(
        default=(),
        alias="directPostconditionCallees",
    )
    direct_postcondition_calls: tuple[DefinitionPostconditionCall, ...] = Field(
        default=(), alias="directPostconditionCalls"
    )
    contract_header_without_axiom: StrictStr = Field(default="", alias="contractHeaderWithoutAxiom")
    contract_header_with_axiom: StrictStr = Field(default="", alias="contractHeaderWithAxiom")
    references: tuple[DefinitionReference, ...]
    dependencies: tuple[StrictStr, ...] = ()


DEFINITION_INFO_LIST = TypeAdapter(list[DefinitionInfo])


class StructuredDefinitionInfo(DefinitionInfo):
    parameter_details: tuple[DefinitionFormal, ...] = Field(default=..., alias="parameterDetails")
    return_details: tuple[DefinitionFormal, ...] = Field(default=..., alias="returnDetails")
    reads: tuple[StrictStr, ...] = Field(default=...)
    decreases: tuple[StrictStr, ...] = Field(default=...)
    direct_precondition_calls: tuple[DefinitionPreconditionCall, ...] = Field(
        default=..., alias="directPreconditionCalls"
    )
    direct_postcondition_calls: tuple[DefinitionPostconditionCall, ...] = Field(
        default=..., alias="directPostconditionCalls"
    )
    contract_header_without_axiom: StrictStr = Field(
        default=..., alias="contractHeaderWithoutAxiom"
    )
    contract_header_with_axiom: StrictStr = Field(default=..., alias="contractHeaderWithAxiom")


class DefinitionAnalysisDocument(BaseModel):
    model_config = ConfigDict(extra="forbid", frozen=True, populate_by_name=True)

    definitions: tuple[StructuredDefinitionInfo, ...]
    source_facts: DefinitionSourceFacts = Field(alias="sourceFacts")
