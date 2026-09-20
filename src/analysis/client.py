"""Subprocess client for Dafny definition analysis."""

from __future__ import annotations

import json
from collections.abc import Collection
from pathlib import Path
from subprocess import CompletedProcess

from dafny_cli import DAFNY_TOOL_TIMEOUT_SEC, dafny_command, run_dafny_command
from standard_library import DAFNY_STANDARD_LIBRARY_OPTION

from .models import (
    DEFINITION_INFO_LIST,
    DefinitionAnalysisDocument,
    DefinitionInfo,
)


def _run_definition_analysis(
    command: list[str],
    *,
    cwd: Path,
    source_text: str | None = None,
    timeout_seconds: float = DAFNY_TOOL_TIMEOUT_SEC,
) -> CompletedProcess[str]:
    return run_dafny_command(
        command,
        cwd=cwd,
        operation="dafny definition-analysis",
        source_text=source_text,
        timeout_seconds=timeout_seconds,
    )


def definition_analysis_infos_from_paths(
    source_paths: Collection[Path],
    *,
    spans_only: bool = False,
    timeout_seconds: float = DAFNY_TOOL_TIMEOUT_SEC,
) -> list[DefinitionInfo]:
    if not source_paths:
        raise ValueError("definition analysis requires at least one source path")
    sorted_paths = sorted(path.resolve() for path in source_paths)
    command = [
        dafny_command(),
        "definition-analysis",
        "--format",
        "json",
        "--allow-warnings",
        "--suppress-warnings",
        DAFNY_STANDARD_LIBRARY_OPTION,
    ]
    if spans_only:
        command.append("--spans-only")
    else:
        command.extend(("--reads-clauses-on-methods", "--include-statements"))
    command.extend(str(path) for path in sorted_paths)
    completed = _run_definition_analysis(
        command,
        cwd=sorted_paths[0].parent,
        timeout_seconds=timeout_seconds,
    )
    if completed.returncode != 0:
        detail = "\n".join(part for part in (completed.stdout, completed.stderr) if part)
        sources = ", ".join(str(path) for path in sorted_paths)
        raise RuntimeError(f"dafny definition-analysis failed for {sources}:\n{detail}")
    payload = json.loads(completed.stdout)
    _populate_specification_call_text(
        payload,
        {str(path): path.read_text(encoding="utf-8") for path in sorted_paths},
    )
    return DEFINITION_INFO_LIST.validate_python(payload)


def definition_analysis_document_from_paths(
    source_paths: Collection[Path],
    *,
    timeout_seconds: float = DAFNY_TOOL_TIMEOUT_SEC,
    include_semantic_facts: bool = True,
) -> DefinitionAnalysisDocument:
    """Analyze source structure, optionally requesting semantic facts in the same run."""

    if not source_paths:
        raise ValueError("definition analysis requires at least one source path")
    sorted_paths = sorted(path.resolve() for path in source_paths)
    command = [
        dafny_command(),
        "definition-analysis",
        "--format",
        "json",
        "--allow-warnings",
        "--suppress-warnings",
        DAFNY_STANDARD_LIBRARY_OPTION,
        "--reads-clauses-on-methods",
        "--include-statements",
        "--include-source-facts",
    ]
    if include_semantic_facts:
        command.append("--include-semantic-facts")
    command.extend(str(path) for path in sorted_paths)
    completed = _run_definition_analysis(
        command,
        cwd=sorted_paths[0].parent,
        timeout_seconds=timeout_seconds,
    )
    if completed.returncode != 0:
        detail = "\n".join(part for part in (completed.stdout, completed.stderr) if part)
        sources = ", ".join(str(path) for path in sorted_paths)
        raise RuntimeError(f"dafny definition-analysis failed for {sources}:\n{detail}")
    payload = json.loads(completed.stdout)
    _populate_specification_call_text(
        payload,
        {str(path): path.read_text(encoding="utf-8") for path in sorted_paths},
    )
    document = DefinitionAnalysisDocument.model_validate(payload)
    if include_semantic_facts and document.source_facts.semantic_facts is None:
        raise RuntimeError("dafny definition-analysis omitted requested semantic facts")
    return document


def definition_analysis_infos_from_stdin(
    source_text: str,
    *,
    source_dir: Path,
    spans_only: bool = False,
) -> list[DefinitionInfo]:
    command = [
        dafny_command(),
        "definition-analysis",
        "--format",
        "json",
        "--allow-warnings",
        "--suppress-warnings",
        DAFNY_STANDARD_LIBRARY_OPTION,
    ]
    if spans_only:
        command.append("--spans-only")
    else:
        command.append("--reads-clauses-on-methods")
    command.append("--stdin")
    completed = _run_definition_analysis(
        command,
        cwd=source_dir.resolve(),
        source_text=source_text,
    )
    if completed.returncode != 0:
        detail = "\n".join(part for part in (completed.stdout, completed.stderr) if part)
        raise RuntimeError(f"dafny definition-analysis failed for stdin:\n{detail}")
    payload = json.loads(completed.stdout)
    _populate_specification_call_text(payload, {str(Path(source_dir) / "<stdin>"): source_text})
    return DEFINITION_INFO_LIST.validate_python(payload)


def _source_text_for_definition(
    source_path: object,
    sources: dict[str, str],
) -> str | None:
    if not isinstance(source_path, str):
        return None
    source = sources.get(source_path)
    if source is None and len(sources) == 1 and not source_path:
        return next(iter(sources.values()))
    if source is None:
        source_file = Path(source_path)
        if source_file.is_file():
            source = source_file.read_text(encoding="utf-8")
            sources[source_path] = source
    return source


def _populate_specification_call_text(payload: object, sources: dict[str, str]) -> None:
    """Fill omitted contract-call text from source spans emitted by Dafny."""
    if isinstance(payload, list):
        definitions = payload
    elif isinstance(payload, dict):
        definitions = payload.get("definitions", ())
    else:
        return
    for definition in definitions:
        if not isinstance(definition, dict):
            continue
        source = _source_text_for_definition(definition.get("sourcePath", ""), sources)
        if source is None:
            continue
        for field_name in ("directPreconditionCalls", "directPostconditionCalls"):
            for call in definition.get(field_name, ()):
                if not isinstance(call, dict) or ("text" in call and call["text"]):
                    continue
                start, end = call.get("start"), call.get("end")
                if isinstance(start, int) and isinstance(end, int):
                    call["text"] = source.encode("utf-8")[start:end].decode("utf-8")
