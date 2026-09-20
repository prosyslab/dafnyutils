"""Execute evaluated .NET programs within the outer Docker boundary."""

from __future__ import annotations

import shutil
import subprocess
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path
from typing import IO, Any

from evaluation.submission.infrastructure import record_candidate_infrastructure_failure


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

    dotnet = shutil.which("dotnet")
    if dotnet is None:
        raise CandidateInfrastructureError("candidate execution requires dotnet")
    return subprocess.run(
        [dotnet, str(dll.resolve(strict=True)), *args],
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
