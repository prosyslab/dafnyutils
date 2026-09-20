"""Select the benchmark Dafny executable and run it with repository library options."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

DAFNY_TOOL_TIMEOUT_SEC = 300


def dafny_command() -> str:
    return os.environ.get("DAFNY_BENCHMARK") or "dafny-benchmark"


def run_dafny_command(
    command: list[str],
    *,
    cwd: Path,
    operation: str,
    source_text: str | None = None,
    timeout_seconds: float = DAFNY_TOOL_TIMEOUT_SEC,
) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            command,
            cwd=cwd,
            env={**os.environ, "TMPDIR": "/tmp"},
            input=source_text,
            text=True,
            capture_output=True,
            check=False,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(f"{operation} timed out after {timeout_seconds:g} seconds") from exc
