"""Audit that benchmark parity tests account for their upstream coreutils origins."""

from __future__ import annotations

import re
from collections.abc import Iterator
from pathlib import Path

import pytest

from tools.bench.bench_test_support import repo_root
from tools.bench.upstream_markers import (
    test_names as upstream_test_names,
)
from tools.bench.upstream_markers import (
    upstream_references_by_test,
)

BENCH_DIR = Path(__file__).resolve().parent
COREUTILS_TEST_PREFIX = "coreutils/tests/"
GNULIB_TEST_PREFIX = "coreutils/gnulib-tests/"
GNULIB_SOURCE_TEST_PREFIX = "coreutils/gnulib/tests/"
COREUTILS_TEST_VARIABLES = ("all_tests", "all_root_tests", "factor_tests")
COREUTILS_DISTRIBUTED_VARIABLES = (*COREUTILS_TEST_VARIABLES, "EXTRA_DIST")
COREUTILS_VARIABLE_ASSIGNMENT = re.compile(
    r"^(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*(?P<operator>\+?=)\s*(?P<value>.*)$"
)
COREUTILS_VARIABLE_REFERENCE = re.compile(r"\$\((?P<name>[A-Za-z_][A-Za-z0-9_]*)\)")
LEGACY_UPSTREAM_COMMENT_PREFIXES = tuple(
    f"# {prefix}"
    for prefix in (
        "Source: coreutils/",
        "GNU coreutils regression: coreutils/",
    )
)


def _bench_utility_names(root: Path) -> list[str]:
    return sorted(path.name for path in (root / "bench" / "utils").iterdir() if path.is_dir())


def _bench_test_modules() -> list[Path]:
    root = repo_root(BENCH_DIR.parents[1])
    return sorted(
        (*BENCH_DIR.glob("test_bench_*.py"), *(root / "bench" / "utils").glob("*/Tests.py"))
    )


def _utility_bench_test_modules(root: Path) -> dict[str, Path]:
    return {
        utility_name: root / "bench" / "utils" / utility_name / "Tests.py"
        for utility_name in _bench_utility_names(root)
    }


def _declared_upstream_paths() -> set[str]:
    paths: set[str] = set()
    for module_path in _bench_test_modules():
        for reference in upstream_references_by_test(module_path).values():
            paths.update(reference.paths)
    return paths


def _accounted_coreutils_test_paths(local_mk: Path) -> set[str]:
    variables = _coreutils_local_mk_variables(local_mk)
    accounted_paths: set[str] = set()
    for variable_name in COREUTILS_DISTRIBUTED_VARIABLES:
        value = _expanded_coreutils_variable_value(
            variables,
            variables.get(variable_name, ""),
            {variable_name},
        )
        for token in value.split():
            if token.startswith("tests/"):
                accounted_paths.add(f"coreutils/{token}")

    return accounted_paths


def _coreutils_local_mk_variables(local_mk: Path) -> dict[str, str]:
    variables: dict[str, str] = {}

    for assignment_name, assignment_operator, value in _iter_coreutils_local_mk_assignments(
        local_mk
    ):
        existing_value = variables.get(assignment_name)
        if assignment_operator == "+=" and existing_value:
            variables[assignment_name] = f"{existing_value} {value}".strip()
        else:
            variables[assignment_name] = value

    return variables


def _iter_coreutils_local_mk_assignments(
    local_mk: Path,
) -> Iterator[tuple[str, str, str]]:
    assignment_name: str | None = None
    assignment_operator = ""
    assignment_parts: list[str] = []

    for raw_line in local_mk.read_text(encoding="utf-8").splitlines():
        line = raw_line.split("#", 1)[0].rstrip()
        if assignment_name is None:
            match = COREUTILS_VARIABLE_ASSIGNMENT.match(line.strip())
            if match is None:
                continue
            assignment_name = match.group("name")
            assignment_operator = match.group("operator")
            assignment_parts = []
            value = match.group("value")
        else:
            value = line.strip()

        parsing_variable = value.endswith("\\")
        if parsing_variable:
            value = value[:-1]
        assignment_parts.append(value.strip())
        if parsing_variable:
            continue

        value = " ".join(part for part in assignment_parts if part)
        yield assignment_name, assignment_operator, value

        assignment_name = None
        assignment_operator = ""
        assignment_parts = []


def _expanded_coreutils_variable_value(
    variables: dict[str, str],
    value: str,
    seen_names: set[str],
) -> str:
    def replace_reference(match: re.Match[str]) -> str:
        name = match.group("name")
        if name in seen_names:
            return match.group(0)
        referenced_value = variables.get(name)
        if referenced_value is None:
            return match.group(0)
        return _expanded_coreutils_variable_value(variables, referenced_value, {*seen_names, name})

    return COREUTILS_VARIABLE_REFERENCE.sub(replace_reference, value)


def _upstream_path_exists(root: Path, path: str) -> bool:
    upstream_path = root / path
    if upstream_path.exists():
        return True
    if path.startswith(GNULIB_TEST_PREFIX):
        relative_path = Path(path.removeprefix(GNULIB_TEST_PREFIX))
        source_path = root / GNULIB_SOURCE_TEST_PREFIX / relative_path
        if source_path.suffix == "":
            source_path = source_path.with_suffix(".c")
        # Generated gnulib-tests links can retain an absolute path from another checkout.
        if source_path.exists():
            return True
        if upstream_path.suffix == "":
            return upstream_path.with_suffix(".c").exists()
    return False


def test_declared_upstream_paths_exist_and_coreutils_paths_are_accounted() -> None:
    # Audit that every declared upstream path exists in the checkout.
    root = repo_root(BENCH_DIR.parents[1])
    coreutils_tests_dir = root / "coreutils" / "tests"
    if not coreutils_tests_dir.is_dir():
        pytest.skip("coreutils upstream checkout is not available")
    local_mk = coreutils_tests_dir / "local.mk"
    assert local_mk.is_file(), "missing coreutils/tests/local.mk"

    declared_paths = _declared_upstream_paths()
    accounted_paths = _accounted_coreutils_test_paths(local_mk)
    missing_paths = sorted(path for path in declared_paths if not _upstream_path_exists(root, path))
    unaccounted_paths = sorted(
        path
        for path in declared_paths
        if path.startswith(COREUTILS_TEST_PREFIX) and path not in accounted_paths
    )
    problems = [
        *(f"missing upstream path: {path}" for path in missing_paths),
        *(f"unaccounted coreutils test/support path: {path}" for path in unaccounted_paths),
    ]
    assert not problems, "\n".join(problems)


# This marker-derived validator audits declared marker completeness per test and
# utility-level coreutils coverage, not equivalence to a removed mapping snapshot.
def test_bench_utils_have_complete_upstream_accounting() -> None:
    missing_modules: list[str] = []
    mismatched_modules: list[str] = []
    missing_markers: list[str] = []
    missing_coreutils_paths: list[str] = []

    root = repo_root(BENCH_DIR.parents[1])
    utility_modules = _utility_bench_test_modules(root)
    bench_modules = _bench_test_modules()
    module_references = {
        module_path: upstream_references_by_test(module_path) for module_path in bench_modules
    }

    for utility_name, module_path in utility_modules.items():
        if not module_path.is_file():
            missing_modules.append(f"{utility_name}: {module_path.name}")

    for module_path in bench_modules:
        references = module_references[module_path]
        utility_name = (
            module_path.parent.name
            if module_path.name == "Tests.py"
            else module_path.stem.removeprefix("test_bench_")
        )
        if utility_name not in utility_modules and any(
            reference.paths for reference in references.values()
        ):
            mismatched_modules.append(
                f"{module_path.name}: upstream paths but no bench/utils/{utility_name}"
            )

        for test_name in upstream_test_names(module_path):
            reference = references[test_name]
            if not reference.paths and reference.repo_only_reason is None:
                missing_markers.append(f"{module_path.name}::{test_name}")

    for module_path in utility_modules.values():
        if not module_path.is_file():
            continue
        references = module_references[module_path]
        has_coreutils_test = any(
            path.startswith(COREUTILS_TEST_PREFIX)
            for reference in references.values()
            for path in reference.paths
        )
        if not has_coreutils_test:
            missing_coreutils_paths.append(module_path.name)

    problems = [
        *(f"missing utility benchmark module: {item}" for item in missing_modules),
        *(f"utility module mismatch: {item}" for item in mismatched_modules),
        *(f"unmarked test function: {item}" for item in missing_markers),
        *(f"missing coreutils/tests coverage: {item}" for item in missing_coreutils_paths),
    ]
    assert not problems, "\n".join(problems)


def test_bench_modules_use_only_standard_upstream_comments() -> None:
    # Audit that marker comments are machine-readable by the extracted marker parser.
    problems: list[str] = []
    for module_path in _bench_test_modules():
        for line_number, line in enumerate(
            module_path.read_text(encoding="utf-8").splitlines(), start=1
        ):
            stripped = line.lstrip()
            if any(stripped.startswith(prefix) for prefix in LEGACY_UPSTREAM_COMMENT_PREFIXES):
                problems.append(f"legacy upstream comment: {module_path.name}:{line_number}")
            if (
                COREUTILS_TEST_PREFIX in line or GNULIB_TEST_PREFIX in line
            ) and not stripped.startswith("# upstream:"):
                problems.append(f"nonstandard upstream comment: {module_path.name}:{line_number}")

    assert not problems, "\n".join(problems)
