"""Keep public benchmark authoring independent of evaluator orchestration."""

import ast
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2] / "src"


# A lower layer must remain importable without pulling in higher-level implementation policy.
@pytest.mark.parametrize(
    ("package", "forbidden"),
    [("benchmarks", {"evaluation"}), ("runtime", {"benchmarks", "evaluation", "analysis"})],
)
def test_package_dependencies_follow_ownership(package: str, forbidden: set[str]) -> None:
    violations = []
    for source in sorted((ROOT / package).rglob("*.py")):
        for node in ast.walk(ast.parse(source.read_text(encoding="utf-8"))):
            if isinstance(node, ast.Import):
                modules = [alias.name for alias in node.names]
            elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
                modules = [node.module]
            else:
                continue
            violations.extend(
                f"{source.relative_to(ROOT)}:{node.lineno}: {module}"
                for module in modules
                if module.split(".")[0] in forbidden
            )
    assert not violations, "\n".join(violations)
