"""Keep benchmark problem data independent of evaluator, analysis and harness code."""

import ast
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]


# Evaluator, analysis and harness modules are root- or Cosyn-owned and never imported here.
FORBIDDEN = {
    "agent",
    "analysis",
    "cosyn",
    "dafny_analysis",
    "dafny_cli",
    "entry_contract",
    "evaluation",
    "execution",
    "experiment_analysis",
    "runtime",
    "standard_library",
    "utils",
    "verification",
}


# Authored data, contributor tooling and oracle tests share the independent package boundary.
@pytest.mark.parametrize(
    ("package", "forbidden"),
    [
        ("src/benchmarks", FORBIDDEN | {"tools"}),
        ("src/tools", FORBIDDEN),
        ("bench", FORBIDDEN),
        ("tools", FORBIDDEN),
    ],
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
