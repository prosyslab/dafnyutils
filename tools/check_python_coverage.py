#!/usr/bin/env python3
"""Require per-file test coverage for the Dafnyutils package."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import tempfile
from configparser import ConfigParser
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pydantic import BaseModel, ConfigDict, Field

DEFAULT_TARGET_ROOTS = ("src",)
DEFAULT_EXCLUDED_PATHS: tuple[str, ...] = ()
DEFAULT_THRESHOLD = 90.0


class CoverageSummaryModel(BaseModel):
    model_config = ConfigDict(extra="ignore")

    percent_covered: float = 0.0


class CoverageFileModel(BaseModel):
    model_config = ConfigDict(extra="ignore")

    summary: CoverageSummaryModel = Field(default_factory=CoverageSummaryModel)


class CoverageJsonReportModel(BaseModel):
    model_config = ConfigDict(extra="ignore")

    files: dict[str, CoverageFileModel] = Field(default_factory=dict)


@dataclass(frozen=True)
class CoverageFailure:
    path: str
    percent: float


@dataclass(frozen=True)
class CoverageResult:
    failures: tuple[CoverageFailure, ...]


def normalize_report_path(path: str, repo_root: Path | None = None) -> str:
    raw_path = Path(path)
    if repo_root is not None and raw_path.is_absolute() and raw_path.is_relative_to(repo_root):
        return raw_path.relative_to(repo_root).as_posix()
    return raw_path.as_posix()


def is_target_path(path: str, target_roots: tuple[str, ...]) -> bool:
    normalized = normalize_report_path(path)
    return any(normalized == root or normalized.startswith(f"{root}/") for root in target_roots)


def iter_target_python_files(repo_root: Path, target_roots: tuple[str, ...]) -> tuple[str, ...]:
    paths: list[str] = []
    for root_name in target_roots:
        target = repo_root / root_name
        if target.is_file() and target.suffix == ".py":
            paths.append(target.relative_to(repo_root).as_posix())
            continue
        if target.is_dir():
            paths.extend(
                path.relative_to(repo_root).as_posix()
                for path in sorted(target.rglob("*.py"))
                if path.is_file()
            )
    return tuple(sorted(paths))


def evaluate_coverage_report(
    *,
    report: CoverageJsonReportModel | dict[str, Any],
    target_roots: tuple[str, ...],
    excluded_paths: tuple[str, ...] = (),
    threshold: float,
    repo_root: Path | None = None,
) -> CoverageResult:
    report_model = (
        report
        if isinstance(report, CoverageJsonReportModel)
        else CoverageJsonReportModel.model_validate(report)
    )
    covered_files = {
        normalize_report_path(path, repo_root): file_report
        for path, file_report in report_model.files.items()
    }
    target_paths = {
        normalize_report_path(path, repo_root)
        for path in covered_files
        if is_target_path(path, target_roots)
    }
    if repo_root is not None:
        target_paths.update(iter_target_python_files(repo_root, target_roots))

    target_paths.difference_update(
        normalize_report_path(path, repo_root) for path in excluded_paths
    )

    failures: list[CoverageFailure] = []
    for path in sorted(target_paths):
        file_report = covered_files.get(path, CoverageFileModel())
        percent = file_report.summary.percent_covered
        if percent < threshold:
            failures.append(CoverageFailure(path, percent))
    return CoverageResult(tuple(failures))


def run_coverage_command(args: list[str], repo_root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "coverage", *args],
        cwd=repo_root,
        check=False,
        text=True,
    )


def run_pytest_command(args: list[str], repo_root: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "-m", "pytest", *args],
        cwd=repo_root,
        check=False,
        text=True,
    )


def write_coverage_config(path: Path, data_file: Path) -> None:
    parser = ConfigParser()
    parser["run"] = {
        "data_file": str(data_file),
        "parallel": "true",
        "patch": "subprocess",
    }
    with path.open("w", encoding="utf-8") as config_file:
        parser.write(config_file)


def run_tests_with_coverage(repo_root: Path, report_path: Path) -> int:
    config_path = report_path.parent / ".coveragerc"
    write_coverage_config(config_path, report_path.parent / ".coverage")

    erase = run_coverage_command(["erase", "--rcfile", str(config_path)], repo_root)
    if erase.returncode != 0:
        return erase.returncode

    run = run_pytest_command(
        [
            "-q",
            "-n",
            "auto",
            "--cov=src",
            "--cov-config",
            str(config_path),
            f"--cov-report=json:{report_path}",
            "tests",
        ],
        repo_root,
    )
    if run.returncode != 0:
        return run.returncode

    return 0


def load_report(path: Path) -> CoverageJsonReportModel:
    return CoverageJsonReportModel.model_validate(json.loads(path.read_text(encoding="utf-8")))


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--threshold", type=float, default=DEFAULT_THRESHOLD)
    parser.add_argument("--check-only", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = Path(__file__).resolve().parents[1]

    try:
        version = run_coverage_command(["--version"], repo_root)
    except ModuleNotFoundError:
        print(
            "coverage is required for this pre-commit gate; install a test environment "
            "where `python3 -m coverage --version` succeeds.",
            file=sys.stderr,
        )
        return 2
    if version.returncode != 0:
        print(
            "coverage is required for this pre-commit gate; install a test environment "
            "where `python3 -m coverage --version` succeeds.",
            file=sys.stderr,
        )
        return 2
    if args.check_only:
        return 0

    with tempfile.TemporaryDirectory(prefix="dafnyutils-coverage-") as tmp_dir:
        report_path = Path(tmp_dir) / "coverage.json"
        coverage_status = run_tests_with_coverage(repo_root, report_path)
        if coverage_status != 0:
            return coverage_status

        result = evaluate_coverage_report(
            report=load_report(report_path),
            target_roots=DEFAULT_TARGET_ROOTS,
            excluded_paths=DEFAULT_EXCLUDED_PATHS,
            threshold=args.threshold,
            repo_root=repo_root,
        )

    if result.failures:
        print(
            f"Python coverage for every file under src/ must be at least {args.threshold:.1f}%.",
            file=sys.stderr,
        )
        for failure in result.failures:
            print(f"- {failure.path}: {failure.percent:.1f}%", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
