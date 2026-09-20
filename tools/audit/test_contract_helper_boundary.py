"""Audit that utility benchmark files do not depend on contract helper modules."""

from __future__ import annotations

import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
BENCH_UTILS_DIR = ROOT / "bench" / "utils"
FORBIDDEN_CONTRACT_HELPER_RE = re.compile(
    r"^\s*(?:include|import(?:\s+opened)?)\b[^\n]*\b[A-Za-z0-9_]*ContractHelpers?\b"
)


def utility_dafny_files() -> list[Path]:
    """All utility-local Dafny files that define a benchmark item surface."""
    paths = sorted(BENCH_UTILS_DIR.glob("*/*.dfy"))
    assert paths, "no utility-local Dafny files were discovered"
    return paths


def contract_helper_violations(path: Path) -> list[str]:
    """Direct contract-helper imports/includes in utility files are forbidden."""
    violations: list[str] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        if FORBIDDEN_CONTRACT_HELPER_RE.search(line):
            violations.append(f"{path.relative_to(ROOT)}:{line_no}: {line.strip()}")
    return violations


@pytest.mark.parametrize(
    "path", utility_dafny_files(), ids=lambda path: str(path.relative_to(ROOT))
)
def test_utility_files_do_not_import_or_include_contract_helpers(path: Path) -> None:
    """Contract-helper modules stay unavailable to utility benchmark artifacts."""
    violations = contract_helper_violations(path)
    assert not violations, "forbidden contract-helper dependency detected:\n" + "\n".join(
        f"- {violation}" for violation in violations
    )
