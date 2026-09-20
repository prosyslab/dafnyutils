"""Evaluator result and container mount vocabulary."""

from enum import StrEnum


class CandidateOutputEntryType(StrEnum):
    FILE = "file"
    DIRECTORY = "directory"
    MISSING = "missing"


class MountMode(StrEnum):
    READ_ONLY = "ro"
    READ_WRITE = "rw"


class CheckStatus(StrEnum):
    PASSED = "passed"
    FAILED = "failed"
    BLOCKED = "blocked"
    NOT_APPLICABLE = "not_applicable"
