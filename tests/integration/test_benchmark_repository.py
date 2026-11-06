from pathlib import Path

import pytest

from benchmarks.definition import BenchmarkKind
from benchmarks.repository import BenchmarkRepository


# Registered definitions preserve canonical IDs across both task layouts.
@pytest.mark.integration
def test_repository_round_trips_every_registered_task(monkeypatch: pytest.MonkeyPatch) -> None:
    root = Path(__file__).resolve().parents[2]
    repository = BenchmarkRepository.open(root)
    definitions = repository._definitions_by_id()
    monkeypatch.setattr(BenchmarkRepository, "_definitions_by_id", lambda self: definitions)

    for task_id in repository.task_ids():
        definition = repository.load_definition(task_id)
        assert definition.task_id == task_id
        assert (
            repository.definition_path(task_id)
            == root / definition.item_directory / "benchmark.yaml"
        )

    assert "cat" in repository.task_ids(BenchmarkKind.COREUTILS)
    assert "algorithm-1" in repository.task_ids(BenchmarkKind.ALGORITHM)
    assert "1" not in repository.task_ids()
