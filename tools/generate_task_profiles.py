#!/usr/bin/env python3
"""Validate generated public task profiles and optionally export review copies."""

from __future__ import annotations

import argparse
from pathlib import Path

from benchmarks.generated_profile import generate_task_profile
from benchmarks.paths import REPO_ROOT
from benchmarks.repository import BenchmarkRepository


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--utility", action="append", default=[])
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()

    repository = BenchmarkRepository.open(REPO_ROOT)
    selected = set(args.utility)
    definitions = tuple(
        definition
        for definition in repository.definitions()
        if not selected or definition.task_id in selected
    )
    unknown = selected.difference(definition.task_id for definition in definitions)
    if unknown:
        parser.error("unknown utilities: " + ", ".join(sorted(unknown)))

    for definition in definitions:
        profile = generate_task_profile(definition, repository_root=repository.root).profile
        if args.output_dir is not None:
            output = args.output_dir / definition.task_id / "task.json"
            output.parent.mkdir(parents=True, exist_ok=True)
            profile.to_json_file(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
