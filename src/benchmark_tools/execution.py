"""Execute evaluated programs within the outer Docker boundary."""

from __future__ import annotations

import os
import shutil
import subprocess
from collections.abc import Callable, Mapping, Sequence
from enum import StrEnum
from pathlib import Path
from typing import IO, Any

from benchmark_tools.environment import EVAL_BENCH_EXECUTION_KIND_ENV
from benchmark_tools.infrastructure import record_candidate_infrastructure_failure


class CandidateExecutionKind(StrEnum):
    """Select the runtime that executes a compiled candidate."""

    DOTNET = "dotnet"
    NATIVE = "native"


class CandidateInfrastructureError(RuntimeError):
    """A trusted pre-candidate prerequisite or setup operation failed."""

    def __init__(self, reason: str) -> None:
        super().__init__(reason)
        record_candidate_infrastructure_failure(reason)


def run_candidate(
    dll: Path,
    args: Sequence[str],
    *,
    cwd: Path,
    execution_kind: CandidateExecutionKind | None = None,
    env: Mapping[str, str] | None = None,
    input: bytes | str | None = None,
    stdin: int | IO[Any] | None = None,
    stdout: int | IO[Any] | None = subprocess.PIPE,
    stderr: int | IO[Any] | None = subprocess.PIPE,
    text: bool = False,
    check: bool = False,
    timeout: float | None = 60,
    preexec_fn: Callable[[], None] | None = None,
) -> subprocess.CompletedProcess[Any]:
    """Run a compiled candidate directly in the caller's Docker execution environment."""

    kind = CandidateExecutionKind(
        os.environ.get(EVAL_BENCH_EXECUTION_KIND_ENV, CandidateExecutionKind.DOTNET.value)
        if execution_kind is None
        else execution_kind
    )
    command: list[str] = []
    if kind == CandidateExecutionKind.DOTNET:
        dotnet = shutil.which("dotnet")
        if dotnet is None:
            raise CandidateInfrastructureError("candidate execution requires dotnet")
        command.append(dotnet)
    command.extend([str(dll.resolve(strict=True)), *args])
    return subprocess.run(
        command,
        cwd=cwd,
        env=env,
        input=input,
        stdin=stdin,
        stdout=stdout,
        stderr=stderr,
        text=text,
        check=check,
        timeout=timeout,
        preexec_fn=preexec_fn,
    )
