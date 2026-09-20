"""External Dafny source-fingerprint client."""

from __future__ import annotations

import json
import tempfile
from collections.abc import Collection
from pathlib import Path

from dafny_cli import DAFNY_TOOL_TIMEOUT_SEC, dafny_command, run_dafny_command

from .models import (
    DafnyFingerprintDocument,
    DafnyFingerprintRegion,
    DafnyFingerprintRequest,
)


def dafny_source_fingerprints(
    regions: Collection[DafnyFingerprintRegion],
    *,
    cwd: Path,
    timeout_seconds: float = DAFNY_TOOL_TIMEOUT_SEC,
) -> dict[str, str]:
    request = DafnyFingerprintRequest(regions=tuple(regions))
    if not request.regions:
        raise ValueError("Dafny source fingerprinting requires at least one region")
    with tempfile.NamedTemporaryFile(
        "w",
        suffix=".json",
        encoding="utf-8",
    ) as handle:
        json.dump(request.model_dump(by_alias=True), handle, ensure_ascii=False)
        handle.flush()
        completed = run_dafny_command(
            [dafny_command(), "source-fingerprint", handle.name],
            cwd=cwd,
            operation="Dafny source fingerprinting",
            timeout_seconds=timeout_seconds,
        )
    if completed.returncode != 0:
        detail = "\n".join(part for part in (completed.stdout, completed.stderr) if part)
        raise RuntimeError(f"Dafny source fingerprinting failed:\n{detail}")
    document = DafnyFingerprintDocument.model_validate_json(completed.stdout)
    result = {item.id: item.sha256 for item in document.fingerprints}
    expected = {region.region_id for region in request.regions}
    if set(result) != expected or len(result) != len(document.fingerprints):
        raise RuntimeError("Dafny source fingerprinting returned incomplete region results")
    return result
