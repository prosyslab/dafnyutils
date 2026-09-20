"""Trusted setup evidence stored outside evaluated candidate namespaces."""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path

from evaluation.models import StrictModel

CANDIDATE_INFRASTRUCTURE_REPORT_ENV = "DAFNYUTILS_CANDIDATE_INFRASTRUCTURE_REPORT"


class CandidateInfrastructureReport(StrictModel):
    reason: str


def record_candidate_infrastructure_failure(reason: str) -> None:
    """Atomically record a trusted setup failure without replacing its exception."""
    destination = os.environ.get(CANDIDATE_INFRASTRUCTURE_REPORT_ENV)
    if not destination:
        return
    report = CandidateInfrastructureReport(reason=reason)
    path = Path(destination)
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            prefix=".infrastructure-",
            dir=path.parent,
            delete=False,
        ) as output:
            temporary = Path(output.name)
            output.write(report.model_dump_json() + "\n")
        temporary.replace(path)
    except OSError as error:
        print(f"could not record candidate setup failure: {error}", file=sys.stderr)
    finally:
        if temporary is not None:
            try:
                temporary.unlink(missing_ok=True)
            except OSError as error:
                print(
                    f"could not remove candidate setup journal temporary file: {error}",
                    file=sys.stderr,
                )


def record_check_failure() -> None:
    """Keep independent protected failure evidence without racing setup journals."""
    destination = os.environ.get(CANDIDATE_INFRASTRUCTURE_REPORT_ENV)
    if not destination:
        return
    directory = Path(destination).parent / "check-failures"
    try:
        directory.mkdir(exist_ok=True)
        with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", prefix="failure-", dir=directory, delete=False
        ) as output:
            output.write("failed\n")
    except OSError as error:
        print(f"could not record failed evaluator check: {error}", file=sys.stderr)
