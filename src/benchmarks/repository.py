"""Explicit filesystem-backed benchmark repository access."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from .definition import BenchmarkDefinition, BenchmarkDefinitionError, BenchmarkKind


@dataclass(frozen=True)
class BenchmarkSuite:
    """A stable selection of benchmark task identifiers."""

    suite_id: str
    task_ids: tuple[str, ...]


@dataclass(frozen=True)
class BenchmarkRepository:
    """A checked-out Dafny benchmark repository."""

    root: Path

    @classmethod
    def open(cls, root: Path) -> BenchmarkRepository:
        resolved = root.resolve()
        if not (resolved / "bench").is_dir():
            raise ValueError(f"benchmark root does not contain bench/: {resolved}")
        return cls(root=resolved)

    def definition_path(self, task_id: str) -> Path:
        return self._definitions_by_id()[task_id][0]

    def load_definition(self, task_id: str) -> BenchmarkDefinition:
        return self._definitions_by_id()[task_id][1]

    def definitions(self, kind: BenchmarkKind | None = None) -> tuple[BenchmarkDefinition, ...]:
        definitions = tuple(definition for _, definition in self._definitions_by_id().values())
        if kind is None:
            return definitions
        return tuple(definition for definition in definitions if definition.kind is kind)

    def task_ids(self, kind: BenchmarkKind | None = None) -> tuple[str, ...]:
        entries = self._definitions_by_id()
        if kind is None:
            return tuple(entries)
        return tuple(
            task_id for task_id, (_, definition) in entries.items() if definition.kind is kind
        )

    def load_suite(self, suite_id: str = "default") -> BenchmarkSuite:
        if suite_id != "default":
            raise KeyError(f"unknown benchmark suite: {suite_id}")
        return BenchmarkSuite(suite_id=suite_id, task_ids=self.task_ids())

    def _definitions_by_id(self) -> dict[str, tuple[Path, BenchmarkDefinition]]:
        entries: dict[str, tuple[Path, BenchmarkDefinition]] = {}
        for family_root in (self.root / "bench" / "utils", self.root / "bench" / "algorithm"):
            if not family_root.is_dir():
                continue
            for path in sorted(family_root.glob("*/benchmark.yaml")):
                definition = BenchmarkDefinition.from_yaml_file(path)
                self._validate_definition_location(path, definition)
                if definition.task_id in entries:
                    raise BenchmarkDefinitionError(
                        f"duplicate benchmark task_id {definition.task_id!r}: "
                        f"{entries[definition.task_id][0]} and {path}"
                    )
                entries[definition.task_id] = (path, definition)

        return dict(sorted(entries.items()))

    def _validate_definition_location(
        self,
        path: Path,
        definition: BenchmarkDefinition,
    ) -> None:
        expected_directory = (self.root / definition.item_directory).resolve()
        if not expected_directory.is_relative_to(self.root):
            raise BenchmarkDefinitionError(
                f"benchmark {definition.task_id!r} directory escapes repository root"
            )
        if path.parent.resolve() != expected_directory:
            raise BenchmarkDefinitionError(
                f"benchmark {definition.task_id!r} is in {path.parent}, "
                f"expected {expected_directory}"
            )
