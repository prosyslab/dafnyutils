"""Define serialized evaluation plans, check results, output records, and failure evidence."""

from __future__ import annotations

from enum import StrEnum
from typing import Literal

from pydantic import BaseModel, ConfigDict, Field

from benchmarks.checks import EvaluationName
from evaluation.enums import CandidateOutputEntryType, CheckStatus


class StrictModel(BaseModel):
    model_config = ConfigDict(extra="forbid")


class OutputMetadataModel(StrictModel):
    bytes: int
    line_count: int
    sha256: str
    preview_utf8: str


class OutputDigestModel(StrictModel):
    bytes: int
    line_count: int
    sha256: str


class CheckPlanEntryModel(StrictModel):
    evaluation: EvaluationName
    name: str
    command: str
    cwd: str


class CheckReportModel(StrictModel):
    applicable: bool
    status: CheckStatus
    required_checks: list[str]
    passed_checks: list[str]
    failed_checks: list[str]
    blocked_reason: str | None = None


class EvaluationResultsModel(StrictModel):
    layout: CheckReportModel
    testcase: CheckReportModel
    fuzzing: CheckReportModel
    verification: CheckReportModel


class FuzzerOutcome(StrEnum):
    INFRASTRUCTURE_FAILURE = "fuzzer_infrastructure_failure"
    BUILD_FAILURE = "fuzzer_build_failure"
    TARGET_SPAWN_FAILURE = "fuzzer_target_spawn_failure"
    DOTNET_RUNTIME_FAILURE = "fuzzer_dotnet_runtime_failure"
    SEMANTIC_MISMATCH = "semantic_mismatch"
    INCOMPLETE_COVERAGE = "incomplete_coverage"
    TIMEOUT = "fuzzer_timeout"


class DafnyVerificationOutcome(StrEnum):
    VERIFIED = "verified"
    VERIFICATION_FAILURE = "verification_failure"
    INFRASTRUCTURE_FAILURE = "infrastructure_failure"
    EVIDENCE_MISSING = "evidence_missing"
    TIMEOUT = "timeout"


class CommandResultModel(StrictModel):
    evaluation: EvaluationName
    name: str
    command: str
    cwd: str
    started_at: str
    completed_at: str
    duration_sec: float
    timeout_sec: int | None
    timed_out: bool
    exit_code: int | None
    passed: bool
    command_script: str
    stdout_log: str
    stderr_log: str
    stdout: OutputMetadataModel
    stderr: OutputMetadataModel
    dafny_verification_outcome: DafnyVerificationOutcome | None = None
    dafny_verification_phase: str | None = None
    infrastructure_failure_reason: str | None = None
    check_failure_observed: bool = False
    fuzzer_outcome: FuzzerOutcome | None = None
    fuzzer_marker: str | None = None
    fuzzer_seed: int | None = None
    fuzzer_iteration: int | None = None
    fuzzer_repro_path: str | None = None


class CommandStartedEventModel(StrictModel):
    event: Literal["command_started"] = "command_started"
    sequence_id: int
    evaluation: EvaluationName
    name: str
    started_at: str
    timeout_sec: int | None
    command: str
    command_script: str
    cwd: str


class CommandCompletedEventModel(StrictModel):
    event: Literal["command_completed"] = "command_completed"
    sequence_id: int
    evaluation: EvaluationName
    name: str
    completed_at: str
    duration_sec: float
    timed_out: bool
    exit_code: int | None
    passed: bool
    stdout_log: str
    stderr_log: str
    stdout: OutputDigestModel
    stderr: OutputDigestModel
    cwd: str


class CandidateOutputTreeEntryKind(StrEnum):
    FILE = "file"
    DIRECTORY = "directory"
    SYMLINK = "symlink"


class CandidateOutputTreeEntryModel(StrictModel):
    path: str
    kind: CandidateOutputTreeEntryKind
    bytes: int | None = None
    sha256: str | None = None
    link_target: str | None = None


class MaterializationReason(StrEnum):
    SPEC_REACHABLE = "spec_reachable"
    EXECUTION_ENTRY = "execution_entry"
    SCHEMA = "schema"


class MaterializedDefinitionModel(StrictModel):
    full_name: str
    source_path: str
    reason: MaterializationReason


class MaterializationEvidenceModel(StrictModel):
    spec_roots: list[str]
    retained_definitions: list[MaterializedDefinitionModel]


class CandidateOutputRecordModel(StrictModel):
    path: str
    source: str
    stored_at: str | None = None
    captured: bool
    changed_from_baseline: bool | None = None
    entry_type: CandidateOutputEntryType | None = None
    bytes: int | None = None
    sha256: str | None = None
    tree_manifest: list[CandidateOutputTreeEntryModel] | None = None
    tree_sha256: str | None = None
    error: str | None = None


class CandidateOutputCaptureResultModel(StrictModel):
    attempted: bool
    copied: bool
    captured_paths: list[str] = Field(default_factory=list)
    manifest_path: str | None = None
    error: str | None = None


class CandidateOutputsCapturedEventModel(StrictModel):
    event: Literal["candidate_outputs_captured"] = "candidate_outputs_captured"
    run_id: str
    captured_at: str
    count: int
    outputs: list[CandidateOutputRecordModel]


class ScoresModel(StrictModel):
    overall_passed: bool
    layout_passed: bool
    testcase_passed: bool
    fuzzing_passed: bool | None
    verification_passed: bool
    total_commands: int
    passed_commands: int


EventModel = (
    CommandStartedEventModel | CommandCompletedEventModel | CandidateOutputsCapturedEventModel
)
