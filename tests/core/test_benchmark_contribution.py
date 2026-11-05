from __future__ import annotations

from pathlib import Path

import pytest

from benchmarks.definition import BenchmarkDefinition, BenchmarkKind, BenchmarkSource
from benchmarks.profiles import ResolvedBenchmark, utility_paths
from benchmarks.repository import BenchmarkRepository
from benchmarks.selection import affected_task_ids

ROOT = Path(__file__).resolve().parents[2]


# Utility profiles publish role directories while algorithm profiles retain flat paths.
@pytest.mark.parametrize(
    ("task_id", "kind", "directory", "entry"),
    (
        ("cat", BenchmarkKind.COREUTILS, "bench/utils/cat", "Impl/Cat.dfy"),
        ("algorithm-1", BenchmarkKind.ALGORITHM, "bench/algorithm/1", "Algorithm1.dfy"),
    ),
)
def test_profile_source_paths_follow_task_layout(
    task_id: str, kind: BenchmarkKind, directory: str, entry: str
) -> None:
    definition = BenchmarkDefinition.model_validate(
        {
            "schema_version": "benchmark.definition.v2",
            "task_id": task_id,
            "kind": kind,
            "source": {"status": "legacy-unverified", "name": "Existing task"},
            "capabilities": {},
        }
    )
    resolved = ResolvedBenchmark.from_definition(definition)
    paths = utility_paths(resolved, task_id)
    assert resolved.task_profile.execution_entry.source_path == entry
    assert paths["wrapper"] == f"{directory}/{entry}"
    for key, role in (
        ("schema", "Spec"),
        ("spec", "Spec"),
        ("core", "Impl"),
        ("proof", "Proof"),
        ("cli", "Impl"),
        ("cli_support", "Impl"),
    ):
        expected = f"{directory}/{role}" if kind is BenchmarkKind.COREUTILS else directory
        assert str(Path(paths[key]).parent) == expected
    assert paths["project_config"] == f"{directory}/dfyconfig.toml"


# Registered definitions preserve canonical IDs across utility and algorithm directory layouts.
@pytest.mark.integration
def test_repository_round_trips_every_registered_task() -> None:
    repository = BenchmarkRepository.open(ROOT)

    for task_id in repository.task_ids():
        definition = repository.load_definition(task_id)
        assert definition.task_id == task_id
        assert repository.definition_path(task_id) == (
            ROOT / definition.item_directory / "benchmark.yaml"
        )

    assert "cat" in repository.task_ids(BenchmarkKind.COREUTILS)
    assert "algorithm-1" in repository.task_ids(BenchmarkKind.ALGORITHM)
    assert "1" not in repository.task_ids()


# Only the fixed migration baseline can use unknown legacy provenance.
def test_new_definition_cannot_claim_legacy_provenance() -> None:
    payload = {
        "schema_version": "benchmark.definition.v2",
        "task_id": "new-task",
        "kind": "coreutils",
        "capabilities": {"gnu_reference": True, "fuzzer": True},
        "source": {
            "status": "legacy-unverified",
            "name": "Unknown",
        },
    }

    with pytest.raises(ValueError, match="migration baseline"):
        BenchmarkDefinition.model_validate(payload)


# Unsupported contributor schema versions require an explicit migration.
@pytest.mark.parametrize("schema_version", ("benchmark.definition.v1", "benchmark.definition.v3"))
def test_definition_rejects_unsupported_schema_version(schema_version: str) -> None:
    payload = {
        "schema_version": schema_version,
        "task_id": "sample",
        "kind": "coreutils",
        "capabilities": {"gnu_reference": True, "fuzzer": True},
        "source": {
            "status": "verified",
            "name": "Sample source",
            "url": "https://example.com/sample",
            "license": "MIT",
        },
    }

    with pytest.raises(ValueError, match="benchmark.definition.v2"):
        BenchmarkDefinition.model_validate(payload)


# A copied v1 path cannot override the evaluator path derived from the v2 task ID.
def test_definition_rejects_legacy_path_override() -> None:
    payload = {
        "schema_version": "benchmark.definition.v2",
        "task_id": "sample",
        "kind": "coreutils",
        "capabilities": {"gnu_reference": True, "fuzzer": True},
        "source": {
            "status": "verified",
            "name": "Sample source",
            "url": "https://example.com/sample",
            "license": "MIT",
        },
        "evaluation": {"test_path": "tools/bench/other.py"},
    }

    with pytest.raises(ValueError, match="evaluation"):
        BenchmarkDefinition.model_validate(payload)


# Verified provenance requires normalized human-readable fields and an HTTP(S) URL.
@pytest.mark.parametrize(
    "source",
    (
        {"status": "verified", "name": " Source", "url": "https://example.com", "license": "MIT"},
        {"status": "verified", "name": "Source", "url": "file:///tmp/source", "license": "MIT"},
        {"status": "verified", "name": "Source", "url": "https://example.com", "license": " TODO "},
    ),
)
def test_verified_provenance_rejects_placeholder_or_malformed_fields(
    source: dict[str, object],
) -> None:
    with pytest.raises(ValueError):
        BenchmarkSource.model_validate(source)


# Shared changes expand selection; item changes stay focused and algorithms use canonical IDs.
def test_affected_task_selection_uses_manifest_families() -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(repository, ("bench/utils/cat/Spec/CatSpec.dfy",)) == ("cat",)
    assert affected_task_ids(repository, ("bench/algorithm/1/Algorithm1Spec.dfy",)) == (
        "algorithm-1",
    )
    assert set(affected_task_ids(repository, ("tools/coreutils_fuzzer/src/lib.rs",))) == set(
        repository.task_ids(BenchmarkKind.COREUTILS)
    )


# Shared benchmark helpers affect every item rather than naming a nonexistent task.
def test_affected_selection_includes_all_tasks_for_shared_benchmark_helpers() -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(repository, ("tools/bench_test_support.py",)) == repository.task_ids()


# Changes to shared analysis, verifier, and candidate execution select every item.
@pytest.mark.parametrize(
    "path",
    (
        "src/analysis/client.py",
        "src/benchmark_tools/contribution/checks.py",
        "src/dafny_cli.py",
        "dafny-version.toml",
    ),
)
def test_affected_selection_includes_all_tasks_for_shared_execution(path: str) -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(repository, (path,)) == repository.task_ids()


# Deleted and renamed item paths remain selected so CI fails closed on missing definitions.
def test_affected_selection_retains_missing_deleted_or_renamed_ids() -> None:
    repository = BenchmarkRepository.open(ROOT)

    assert affected_task_ids(
        repository,
        (
            "bench/utils/deleted/benchmark.yaml",
            "bench/utils/replacement/benchmark.yaml",
            "bench/algorithm/999/benchmark.yaml",
        ),
    ) == ("algorithm-999", "deleted", "replacement")
