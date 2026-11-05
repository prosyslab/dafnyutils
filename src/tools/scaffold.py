"""Create intentionally incomplete benchmark contribution scaffolds."""

from __future__ import annotations

import argparse
import shutil
from dataclasses import dataclass
from pathlib import Path

from benchmarks.definition import (
    BenchmarkKind,
    benchmark_item_directory,
    class_name_for_task_id,
    validate_task_id,
)


@dataclass(frozen=True)
class ScaffoldResult:
    """Describe the generated contribution directory and its files."""

    task_id: str
    directory: Path
    files: tuple[Path, ...]


def _class_name(task_id: str) -> str:
    return class_name_for_task_id(task_id)


def scaffold_benchmark(*, root: Path, kind: BenchmarkKind, task_id: str) -> ScaffoldResult:
    """Copy and specialize templates without replacing an existing contribution."""
    root = root.resolve()
    validate_task_id(task_id)
    directory = _scaffold_directory(root, kind, task_id)
    if not directory.resolve().is_relative_to(root):
        raise ValueError(f"benchmark directory escapes repository root: {directory}")
    if directory.exists():
        raise FileExistsError(f"benchmark directory already exists: {directory}")

    template_root = root / "tools" / "benchmark_templates"
    sources = (template_root / "common", template_root / kind.value)
    for source in sources:
        if not source.is_dir():
            raise FileNotFoundError(f"benchmark template directory is missing: {source}")
    directory.mkdir(parents=True)
    for source in sources:
        for template in sorted(source.iterdir()):
            shutil.copyfile(template, directory / template.name)
    created = _specialize_files(directory, task_id, kind)
    return ScaffoldResult(task_id=task_id, directory=directory, files=created)


def _scaffold_directory(root: Path, kind: BenchmarkKind, task_id: str) -> Path:
    return root / benchmark_item_directory(kind, task_id)


def _specialize_files(directory: Path, task_id: str, kind: BenchmarkKind) -> tuple[Path, ...]:
    class_name = _class_name(task_id)
    separated = kind is BenchmarkKind.COREUTILS
    replacements = {
        "{{TASK_ID}}": task_id,
        "{{CLASS_NAME}}": class_name,
        "{{CORE_PREFIX}}": "../../../core/" if separated else "../../core/",
        "{{SPEC_PREFIX}}": "../Spec/" if separated else "",
        "{{IMPL_PREFIX}}": "../Impl/" if separated else "",
        "{{PROOF_PREFIX}}": "../Proof/" if separated else "",
        "{{ENTRY_PREFIX}}": "Impl/" if separated else "",
    }
    rename_map = {
        "Description.md": f"{task_id}.md",
        "UtilitySchema.dfy": f"{class_name}Schema.dfy",
        "UtilitySpec.dfy": f"{class_name}Spec.dfy",
        "UtilityCore.dfy": f"{class_name}Core.dfy",
        "UtilityProof.dfy": f"{class_name}Proof.dfy",
        "Utility.dfy": f"{class_name}.dfy",
        "UtilityCli.dfy": f"{class_name}Cli.dfy",
    }
    created: list[Path] = []
    for path in sorted(directory.iterdir()):
        if not path.is_file():
            continue
        destination_name = rename_map.get(path.name, path.name)
        destination = directory / destination_name
        if separated and path.suffix == ".dfy":
            if path.stem.endswith(("Schema", "Spec")):
                role = "Spec"
            elif path.stem.endswith("Proof"):
                role = "Proof"
            else:
                role = "Impl"
            target_dir = directory / role
            if not target_dir.exists():
                target_dir.mkdir(parents=True)
            destination = target_dir / destination_name
        if path != destination:
            path = path.rename(destination)
        text = path.read_text(encoding="utf-8")
        for marker, replacement in replacements.items():
            text = text.replace(marker, replacement)
        path.write_text(text, encoding="utf-8")
        created.append(path)
    return tuple(sorted(created))


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parents[2],
        help="benchmark repository root (default: this tool's repository)",
    )
    parser.add_argument(
        "--kind",
        type=BenchmarkKind,
        choices=tuple(kind.value for kind in BenchmarkKind),
        required=True,
    )
    parser.add_argument("--id", required=True, dest="task_id")
    return parser


def main(argv: list[str] | None = None) -> int:
    """Create an incomplete contribution and report expected authoring errors."""
    args = _parser().parse_args(argv)
    try:
        result = scaffold_benchmark(root=args.root, kind=args.kind, task_id=args.task_id)
    except (OSError, ValueError) as exc:
        print(f"scaffold failed: {exc}")
        return 1
    print(result.directory.relative_to(args.root.resolve()).as_posix())
    print("scaffold is incomplete; replace TODO content and source status before validation")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
