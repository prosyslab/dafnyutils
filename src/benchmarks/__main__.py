"""List benchmark definitions from the installed data package.

Run independent contributor validation and checks with
`python -m tools.contribution`. Full source analysis remains root-owned.
Create new contributions with `python -m tools.scaffold`.
"""

from __future__ import annotations

import argparse
from pathlib import Path

from .definition import BenchmarkKind
from .repository import BenchmarkRepository


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="python -m benchmarks")
    parser.add_argument("--root", type=Path, default=Path.cwd(), help="benchmark repository root")
    subparsers = parser.add_subparsers(dest="command", required=True)

    list_parser = subparsers.add_parser("list", help="list registered benchmark IDs")
    list_parser.add_argument("--kind", type=BenchmarkKind, choices=tuple(BenchmarkKind))

    return parser


def main(argv: list[str] | None = None) -> int:
    """List task IDs, optionally restricted to one benchmark kind."""
    args = _parser().parse_args(argv)
    return _list(BenchmarkRepository.open(args.root), args.kind)


def _list(repository: BenchmarkRepository, kind: BenchmarkKind | None) -> int:
    for task_id in repository.task_ids(kind):
        print(task_id)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
