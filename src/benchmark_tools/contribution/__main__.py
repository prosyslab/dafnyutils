"""Command-line interface for contributor checks that validate or execute benchmark tasks."""

from __future__ import annotations

import argparse
from pathlib import Path

from benchmark_tools.contribution.checks import run_benchmark_checks
from benchmark_tools.contribution.validation import validate_benchmark
from benchmarks.repository import BenchmarkRepository
from benchmarks.selection import affected_task_ids


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="python -m benchmark_tools.contribution")
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="benchmark repository root")
    subparsers = parser.add_subparsers(dest="command", required=True)

    validate_parser = subparsers.add_parser(
        "validate", help="validate definitions and declared local files"
    )
    validate_parser.add_argument("task_ids", nargs="*")

    check_parser = subparsers.add_parser("check", help="run every mandatory focused item check")
    check_parser.add_argument("task_ids", nargs="*")
    check_parser.add_argument("--changed-path", action="append", default=[])
    return parser


def main(argv: list[str] | None = None) -> int:
    """Validate or check the selected benchmark tasks and return a process status."""
    args = _parser().parse_args(argv)
    repository = BenchmarkRepository.open(args.root)
    return _validate_or_check(args, repository)


def _validate_or_check(args: argparse.Namespace, repository: BenchmarkRepository) -> int:

    selected = tuple(args.task_ids)
    explicit_selection = bool(selected)
    if args.command == "check" and args.changed_path:
        if selected:
            raise SystemExit("task IDs and --changed-path cannot be combined")
        selected = affected_task_ids(repository, tuple(args.changed_path))
        explicit_selection = True
    if not selected and not explicit_selection:
        selected = repository.task_ids()

    failed = False
    for task_id in selected:
        if args.command == "validate":
            issues = validate_benchmark(repository, task_id)
            if issues:
                failed = True
                for issue in issues:
                    print(f"{issue.task_id}: {issue.message}")
            else:
                print(f"{task_id}: valid")
        else:
            try:
                run_benchmark_checks(repository, task_id)
            except (OSError, ValueError, RuntimeError) as exc:
                failed = True
                print(f"{task_id}: {exc}")
            else:
                print(f"{task_id}: checks passed")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
