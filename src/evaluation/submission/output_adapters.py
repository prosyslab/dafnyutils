"""Parse evaluator-owned check output into typed internal evidence."""

from __future__ import annotations

import re
from dataclasses import dataclass

from evaluation.models import DafnyVerificationOutcome, FuzzerOutcome

_FUZZER_OUTCOME_PATTERN = re.compile(rb"^FUZZER_OUTCOME=([a-z_]+)$", re.MULTILINE)
_FUZZER_SEED_PATTERN = re.compile(rb"\bseed=(\d+)\b")
_FUZZER_ITERATION_PATTERN = re.compile(rb"\biteration=(\d+)\b")
_FUZZER_REPRO_PATH_PATTERN = re.compile(rb"\brepro saved to ([^\r\n]+)")
_DAFNY_VERIFICATION_RESULT_PATTERN = re.compile(
    rb"^DAFNY_VERIFICATION_RESULT total=(\d+) failed=(\d+)\r?$", re.MULTILINE
)
_DAFNY_VERIFICATION_OUTCOME_PATTERN = re.compile(
    rb"^DAFNY_VERIFICATION_OUTCOME=([a-z_]+) phase=([a-z_]+)\r?$",
    re.MULTILINE,
)
_DAFNY_VERIFICATION_OUTCOME_LINE_PATTERN = re.compile(
    rb"^DAFNY_VERIFICATION_OUTCOME.*\r?$",
    re.MULTILINE,
)
_DAFNY_VERIFICATION_RESULT_LINE_PATTERN = re.compile(
    rb"^DAFNY_VERIFICATION_RESULT.*\r?$",
    re.MULTILINE,
)


@dataclass(frozen=True, slots=True)
class DafnyVerificationEvidence:
    """The validated Dafny marker pair emitted by the verification gate."""

    outcome: DafnyVerificationOutcome | None
    phase: str | None

    def model_fields(self) -> dict[str, DafnyVerificationOutcome | str | None]:
        """Return fields with the names used by the persisted command model."""
        return {
            "dafny_verification_outcome": self.outcome,
            "dafny_verification_phase": self.phase,
        }


@dataclass(frozen=True, slots=True)
class FuzzerEvidence:
    """The fuzzer marker and optional reproduction metadata."""

    outcome: FuzzerOutcome | None
    marker: str | None
    seed: int | None
    iteration: int | None
    repro_path: str | None

    def model_fields(self) -> dict[str, FuzzerOutcome | str | int | None]:
        """Return fields with the names used by the persisted command model."""
        return {
            "fuzzer_outcome": self.outcome,
            "fuzzer_marker": self.marker,
            "fuzzer_seed": self.seed,
            "fuzzer_iteration": self.iteration,
            "fuzzer_repro_path": self.repro_path,
        }


def parse_dafny_verification(
    *,
    name: str,
    timed_out: bool,
    exit_code: int | None,
    stdout_bytes: bytes,
    stderr_bytes: bytes,
) -> DafnyVerificationEvidence:
    """Validate the Dafny marker protocol for one command invocation."""
    if name != "dafny_verify":
        return DafnyVerificationEvidence(outcome=None, phase=None)
    if timed_out:
        return DafnyVerificationEvidence(
            outcome=DafnyVerificationOutcome.TIMEOUT,
            phase=None,
        )

    output = stdout_bytes + b"\n" + stderr_bytes
    outcome_matches = _DAFNY_VERIFICATION_OUTCOME_PATTERN.findall(output)
    if (
        len(_DAFNY_VERIFICATION_OUTCOME_LINE_PATTERN.findall(output)) != 1
        or len(outcome_matches) != 1
    ):
        return DafnyVerificationEvidence(
            outcome=DafnyVerificationOutcome.EVIDENCE_MISSING,
            phase=None,
        )
    try:
        outcome = DafnyVerificationOutcome(outcome_matches[0][0].decode("ascii"))
        phase = outcome_matches[0][1].decode("ascii")
    except (UnicodeDecodeError, ValueError):
        outcome = DafnyVerificationOutcome.EVIDENCE_MISSING
        phase = None

    valid_phases = {
        DafnyVerificationOutcome.VERIFIED: {"verify"},
        DafnyVerificationOutcome.VERIFICATION_FAILURE: {"verify"},
        DafnyVerificationOutcome.INFRASTRUCTURE_FAILURE: {
            "build",
            "proof_layout",
            "evidence",
        },
    }
    consistent = phase in valid_phases.get(outcome, set())
    if outcome == DafnyVerificationOutcome.VERIFIED:
        result_matches = _DAFNY_VERIFICATION_RESULT_PATTERN.findall(output)
        result_line_count = len(_DAFNY_VERIFICATION_RESULT_LINE_PATTERN.findall(output))
        try:
            total, failed = (
                map(int, result_matches[0])
                if result_line_count == 1 and len(result_matches) == 1
                else (0, 1)
            )
        except ValueError:
            total, failed = 0, 1
        consistent = consistent and exit_code == 0 and total > 0 and failed == 0
    else:
        consistent = (
            consistent
            and exit_code not in {None, 0}
            and not _DAFNY_VERIFICATION_RESULT_LINE_PATTERN.search(output)
        )

    if not consistent:
        outcome = DafnyVerificationOutcome.EVIDENCE_MISSING
        phase = None
    return DafnyVerificationEvidence(outcome=outcome, phase=phase)


def parse_fuzzer_outcome(
    *,
    name: str,
    stdout_bytes: bytes,
    stderr_bytes: bytes,
    timed_out: bool,
    exit_code: int | None,
) -> FuzzerEvidence:
    """Parse fuzzer outcome markers and optional run metadata."""
    if name != "fuzzer":
        return FuzzerEvidence(
            outcome=None,
            marker=None,
            seed=None,
            iteration=None,
            repro_path=None,
        )

    output = stdout_bytes + b"\n" + stderr_bytes
    marker_match = _FUZZER_OUTCOME_PATTERN.search(output)
    outcome = None
    marker = None
    if marker_match is not None:
        marker = marker_match.group(0).decode("ascii")
        try:
            outcome = FuzzerOutcome(marker_match.group(1).decode("ascii"))
        except ValueError:
            pass
    if outcome is None and timed_out:
        outcome = FuzzerOutcome.TIMEOUT
    elif outcome is None and exit_code not in {None, 0}:
        outcome = FuzzerOutcome.BUILD_FAILURE

    def capture_int(pattern: re.Pattern[bytes]) -> int | None:
        match = pattern.search(output)
        return int(match.group(1)) if match is not None else None

    repro_match = _FUZZER_REPRO_PATH_PATTERN.search(output)
    return FuzzerEvidence(
        outcome=outcome,
        marker=marker,
        seed=capture_int(_FUZZER_SEED_PATTERN),
        iteration=capture_int(_FUZZER_ITERATION_PATTERN),
        repro_path=(
            repro_match.group(1).decode("utf-8", errors="replace").strip()
            if repro_match is not None
            else None
        ),
    )


def command_passed(
    *,
    name: str,
    timed_out: bool,
    exit_code: int | None,
    stdout_bytes: bytes,
    stderr_bytes: bytes = b"",
    dafny_evidence: DafnyVerificationEvidence | None = None,
) -> bool:
    """Apply the evaluator pass rule, including Dafny evidence validation."""
    if name == "dafny_verify":
        evidence = dafny_evidence or parse_dafny_verification(
            name=name,
            timed_out=timed_out,
            exit_code=exit_code,
            stdout_bytes=stdout_bytes,
            stderr_bytes=stderr_bytes,
        )
        return evidence.outcome == DafnyVerificationOutcome.VERIFIED
    return not timed_out and exit_code == 0
