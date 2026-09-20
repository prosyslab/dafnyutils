"""Command-line interface for benchmark contributors."""

from __future__ import annotations

import argparse
from pathlib import Path

from benchmarks.contribution import run_benchmark_checks
from benchmarks.selection import affected_task_ids
from benchmarks.validation import validate_benchmark

from .definition import BenchmarkKind
from .repository import BenchmarkRepository
from .scaffold import scaffold_benchmark


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="python -m benchmarks")
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="benchmark repository root")
    subparsers = parser.add_subparsers(dest="command", required=True)

    list_parser = subparsers.add_parser("list", help="list registered benchmark IDs")
    list_parser.add_argument("--kind", type=BenchmarkKind, choices=tuple(BenchmarkKind))

    init_parser = subparsers.add_parser("init", help="create an incomplete benchmark scaffold")
    init_parser.add_argument(
        "--kind", type=BenchmarkKind, choices=tuple(BenchmarkKind), required=True
    )
    init_parser.add_argument("--id", required=True, dest="task_id")

    validate_parser = subparsers.add_parser("validate", help="validate definitions and contracts")
    validate_parser.add_argument("task_ids", nargs="*")

    check_parser = subparsers.add_parser("check", help="run every mandatory focused item check")
    check_parser.add_argument("task_ids", nargs="*")
    check_parser.add_argument("--changed-path", action="append", default=[])
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    if args.command == "init":
        return _init(args)

    repository = BenchmarkRepository.open(args.root)
    if args.command == "list":
        return _list(repository, args.kind)

    return _validate_or_check(args, repository)


def _init(args: argparse.Namespace) -> int:
    try:
        result = scaffold_benchmark(root=args.root, kind=args.kind, task_id=args.task_id)
    except (FileExistsError, OSError, ValueError) as exc:
        print(f"init failed: {exc}")
        return 1
    print(result.directory.relative_to(args.root.resolve()).as_posix())
    print("scaffold is incomplete; replace TODO content and source status before validation")
    return 0


def _list(repository: BenchmarkRepository, kind: BenchmarkKind | None) -> int:
    for task_id in repository.task_ids(kind):
        print(task_id)
    return 0


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
