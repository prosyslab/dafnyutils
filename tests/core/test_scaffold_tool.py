from __future__ import annotations

import tomllib
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from posixpath import normpath

import pytest

from benchmarks.definition import BenchmarkKind
from tools import scaffold


@dataclass
class _MemoryFiles:
    root: Path = Path("/scaffold-checkout")
    files: dict[Path, str] = field(default_factory=dict)
    directories: set[Path] = field(default_factory=set)

    def __post_init__(self) -> None:
        template_root = self.root / "tools/benchmark_templates"
        common = (
            "Utility.dfy",
            "UtilityCli.dfy",
            "UtilityCore.dfy",
            "UtilityProof.dfy",
            "UtilitySchema.dfy",
            "UtilitySpec.dfy",
            "CliSupport.dfy",
            "Makefile",
            "dfyconfig.toml",
        )
        for kind, names in (
            ("common", common),
            ("coreutils", ("Description.md", "Tests.py", "benchmark.yaml")),
            ("algorithm", ("Description.md", "Tests.py", "benchmark.yaml", "cases.json")),
        ):
            directory = template_root / kind
            self.directories.add(directory)
            for name in names:
                self.files[directory / name] = f"{kind}: {{{{TASK_ID}}}} {{{{CLASS_NAME}}}}\n"
        for kind in ("coreutils", "algorithm"):
            self.files[template_root / kind / "benchmark.yaml"] += "status: incomplete\n"

    def _mkdir(self, path: Path, *, parents: bool) -> None:
        assert parents
        if path in self.directories or path in self.files:
            raise FileExistsError(path)
        self.directories.add(path)

    def _rename(self, source: Path, destination: Path) -> Path:
        self.files[destination] = self.files.pop(source)
        return destination

    def _write(self, path: Path, text: str, *, encoding: str) -> int:
        assert encoding == "utf-8"
        self.files[path] = text
        return len(text)

    def _read(self, path: Path, *, encoding: str) -> str:
        assert encoding == "utf-8"
        return self.files[path]

    def _copy(self, source: Path, destination: Path) -> Path:
        self.files[destination] = self.files[source]
        return destination

    @contextmanager
    def patched(self, monkeypatch: pytest.MonkeyPatch) -> Iterator[None]:
        # Every filesystem boundary in the generator uses only these memory maps.
        with monkeypatch.context() as patch:
            patch.setattr(Path, "resolve", lambda path: path)
            patch.setattr(
                Path, "exists", lambda path: path in self.files or path in self.directories
            )
            patch.setattr(Path, "is_dir", lambda path: path in self.directories)
            patch.setattr(Path, "is_file", lambda path: path in self.files)
            patch.setattr(
                Path, "mkdir", lambda path, *, parents: self._mkdir(path, parents=parents)
            )
            patch.setattr(Path, "rename", lambda path, destination: self._rename(path, destination))
            patch.setattr(
                Path,
                "write_text",
                lambda path, text, *, encoding: self._write(path, text, encoding=encoding),
            )
            patch.setattr(
                Path,
                "read_text",
                lambda path, *, encoding: self._read(path, encoding=encoding),
            )
            patch.setattr(
                Path,
                "iterdir",
                lambda path: iter(
                    item for item in self.files.keys() | self.directories if item.parent == path
                ),
            )
            patch.setattr(scaffold.shutil, "copyfile", self._copy)
            yield


# Each kind combines shared and kind-specific inputs and specializes every generated name.
@pytest.mark.parametrize(
    ("kind", "task_id", "relative", "class_name", "extra"),
    (
        (BenchmarkKind.COREUTILS, "sample-tool", "utils/sample-tool", "SampleTool", set()),
        (BenchmarkKind.ALGORITHM, "algorithm-123", "algorithm/123", "Algorithm123", {"cases.json"}),
    ),
)
def test_generation_specializes_common_and_kind_templates(
    monkeypatch: pytest.MonkeyPatch,
    kind: BenchmarkKind,
    task_id: str,
    relative: str,
    class_name: str,
    extra: set[str],
) -> None:
    memory = _MemoryFiles()
    original_templates = memory.files.copy()

    with memory.patched(monkeypatch):
        result = scaffold.scaffold_benchmark(root=memory.root, kind=kind, task_id=task_id)

    assert result.task_id == task_id
    assert result.directory == memory.root / "bench" / relative
    assert {path.name for path in result.files} == {
        f"{class_name}{suffix}.dfy" for suffix in ("", "Cli", "Core", "Proof", "Schema", "Spec")
    } | {
        f"{task_id}.md",
        "CliSupport.dfy",
        "Makefile",
        "dfyconfig.toml",
        "Tests.py",
        "benchmark.yaml",
    } | extra
    source_root = result.directory
    if kind is BenchmarkKind.COREUTILS:
        assert {
            path.relative_to(source_root).as_posix()
            for path in result.files
            if path.suffix == ".dfy"
        } == {
            f"Spec/{class_name}Schema.dfy",
            f"Spec/{class_name}Spec.dfy",
            f"Impl/{class_name}.dfy",
            f"Impl/{class_name}Cli.dfy",
            f"Impl/{class_name}Core.dfy",
            "Impl/CliSupport.dfy",
            f"Proof/{class_name}Proof.dfy",
        }
    else:
        assert all(path.parent == source_root for path in result.files)
    assert result.files == tuple(sorted(result.files))
    assert memory.files[result.directory / "Makefile"] == f"common: {task_id} {class_name}\n"
    assert memory.files[result.directory / f"{task_id}.md"] == (
        f"{kind.value}: {task_id} {class_name}\n"
    )
    assert memory.files[result.directory / "benchmark.yaml"] == (
        f"{kind.value}: {task_id} {class_name}\nstatus: incomplete\n"
    )
    assert all("{{" not in memory.files[path] for path in result.files)
    assert all(memory.files[path] == text for path, text in original_templates.items())


# Real templates resolve all generated includes and the CLI entry in either source layout.
@pytest.mark.parametrize("kind", (BenchmarkKind.COREUTILS, BenchmarkKind.ALGORITHM))
def test_template_source_closure_resolves_in_generated_layout(
    monkeypatch: pytest.MonkeyPatch, kind: BenchmarkKind
) -> None:
    memory = _MemoryFiles()
    template_root = Path(__file__).resolve().parents[2] / "tools/benchmark_templates"
    for path in tuple(memory.files):
        relative = path.relative_to(memory.root / "tools/benchmark_templates")
        memory.files[path] = (template_root / relative).read_text(encoding="utf-8")
    task_id = "sample-tool" if kind is BenchmarkKind.COREUTILS else "algorithm-123"
    with memory.patched(monkeypatch):
        result = scaffold.scaffold_benchmark(root=memory.root, kind=kind, task_id=task_id)

    for path in result.files:
        if path.suffix != ".dfy":
            continue
        for line in memory.files[path].splitlines():
            if not line.startswith('include "'):
                continue
            target = Path(normpath(str(path.parent / line.split('"')[1])))
            assert target in memory.files or target.parent == memory.root / "bench/core"
    config = tomllib.loads(memory.files[result.directory / "dfyconfig.toml"])
    assert len(config["includes"]) == 1
    assert result.directory / config["includes"][0] in memory.files


# The command uses the tool's checkout by default and reports the unfinished contribution.
def test_command_uses_tool_repository_default(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    memory = _MemoryFiles()
    monkeypatch.setattr(scaffold, "__file__", str(memory.root / "src/tools/scaffold.py"))

    with memory.patched(monkeypatch):
        status = scaffold.main(["--kind", "coreutils", "--id", "base32"])

    assert status == 0
    assert capsys.readouterr().out == (
        "bench/utils/base32\n"
        "scaffold is incomplete; replace TODO content and source status before validation\n"
    )
    assert memory.root / "bench/utils/base32/Impl/Base32.dfy" in memory.files


# An existing contribution remains byte-for-byte unchanged when generation is refused.
def test_command_refuses_existing_contribution(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    memory = _MemoryFiles()
    directory = memory.root / "bench/utils/base32"
    memory.directories.add(directory)
    memory.files[directory / "base32.md"] = "existing contribution\n"
    original = memory.files.copy()

    with memory.patched(monkeypatch):
        status = scaffold.main(
            ["--root", str(memory.root), "--kind", "coreutils", "--id", "base32"]
        )

    assert status == 1
    assert "benchmark directory already exists" in capsys.readouterr().out
    assert memory.files == original


# Invalid IDs fail before any contribution directory or file is created.
@pytest.mark.parametrize(
    ("kind", "task_id"),
    (("coreutils", "../escape"), ("coreutils", "algorithm-123"), ("algorithm", "sample-tool")),
)
def test_command_rejects_invalid_task_id(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    kind: str,
    task_id: str,
) -> None:
    memory = _MemoryFiles()
    original = (memory.files.copy(), memory.directories.copy())

    with memory.patched(monkeypatch):
        status = scaffold.main(["--root", str(memory.root), "--kind", kind, "--id", task_id])

    assert status == 1
    assert capsys.readouterr().out.startswith("scaffold failed: ")
    assert (memory.files, memory.directories) == original


# Missing template sets fail before generation leaves a partial contribution behind.
@pytest.mark.parametrize("missing_kind", ("common", "coreutils"))
def test_command_reports_missing_templates(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    missing_kind: str,
) -> None:
    memory = _MemoryFiles()
    memory.directories.remove(memory.root / "tools/benchmark_templates" / missing_kind)
    original = (memory.files.copy(), memory.directories.copy())

    with memory.patched(monkeypatch):
        status = scaffold.main(
            ["--root", str(memory.root), "--kind", "coreutils", "--id", "base32"]
        )

    assert status == 1
    assert "benchmark template directory is missing" in capsys.readouterr().out
    assert (memory.files, memory.directories) == original
