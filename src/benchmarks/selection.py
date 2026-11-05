"""Select benchmark tasks affected by repository changes."""

from pathlib import Path

from benchmarks.repository import BenchmarkRepository


def affected_task_ids(
    repository: BenchmarkRepository,
    changed_paths: tuple[str, ...],
) -> tuple[str, ...]:
    all_ids = set(repository.task_ids())
    fuzzer_ids = {
        definition.task_id
        for definition in repository.definitions()
        if definition.evaluation.fuzzer_target is not None
    }
    affected: set[str] = set()
    for raw_path in changed_paths:
        path = Path(raw_path)
        parts = path.parts
        if len(parts) >= 3 and parts[:2] == ("bench", "utils"):
            affected.add(parts[2])
        elif len(parts) >= 3 and parts[:2] == ("bench", "algorithm"):
            affected.add(f"algorithm-{parts[2]}")
        elif raw_path.startswith("tools/coreutils_fuzzer/"):
            affected.update(fuzzer_ids)
        elif raw_path == "tools/bench_test_support.py":
            affected.update(all_ids)
        elif (
            raw_path.startswith("bench/core/")
            or raw_path.startswith("src/analysis/")
            or raw_path.startswith("src/benchmarks/")
            or raw_path.startswith("src/benchmark_tools/")
            or raw_path.startswith("src/evaluation/")
            or raw_path.startswith("src/entry_contract")
            or raw_path.startswith("src/protocol/")
            or raw_path.startswith("src/runtime/")
            or raw_path == "src/standard_library.py"
            or raw_path == "src/dafny_cli.py"
            or raw_path == "src/verification.py"
            or raw_path
            in {
                ".gitmodules",
                "Makefile",
                "pyproject.toml",
                "dafny-version.toml",
                "tools/generate_task_profiles.py",
            }
        ):
            affected.update(all_ids)
    return tuple(sorted(affected))
