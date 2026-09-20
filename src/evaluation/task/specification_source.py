"""Select public Dafny specification declarations and produce empty module placeholders."""

from __future__ import annotations

from pathlib import Path

from analysis.models import DefinitionAnalysisDocument, DefinitionInfo

PLACEHOLDER_FILE_CONTENT = "// Agent-editable scaffold populated inside the sandbox workspace.\n"


def module_placeholder(source: Path, analysis: DefinitionAnalysisDocument) -> str:
    modules = sorted(
        {
            module.name
            for module in analysis.source_facts.modules
            if Path(module.source_path).resolve() == source.resolve()
        }
    )
    if not modules:
        return PLACEHOLDER_FILE_CONTENT
    return "".join(f"module {name} {{}}\n" for name in modules)


def filtered_specification_source(
    source: Path,
    analysis: DefinitionAnalysisDocument,
    retained_symbols: set[str],
) -> str:
    source_bytes = source.read_bytes()
    resolved_source = source.resolve()
    includes = [
        source_bytes[item.start : item.end].decode("utf-8").strip()
        for item in analysis.source_facts.includes
        if Path(item.source_path).resolve() == resolved_source
    ]
    imports_by_module: dict[str, list[str]] = {}
    for item in analysis.source_facts.imports:
        if Path(item.source_path).resolve() != resolved_source:
            continue
        imports_by_module.setdefault(item.module_name, []).append(
            source_bytes[item.start : item.end].decode("utf-8").strip()
        )
    definitions_by_module: dict[str, list[DefinitionInfo]] = {}
    for info in analysis.definitions:
        if (
            Path(info.source_path).resolve() == resolved_source
            and info.full_name in retained_symbols
        ):
            definitions_by_module.setdefault(info.enclosing_name, []).append(info)

    sections = list(dict.fromkeys(includes))
    modules = [
        module
        for module in analysis.source_facts.modules
        if Path(module.source_path).resolve() == resolved_source
    ]
    for module in modules:
        body_parts = list(dict.fromkeys(imports_by_module.get(module.name, ())))
        body_parts.extend(
            source_bytes[info.start : info.end].decode("utf-8").strip()
            for info in sorted(
                definitions_by_module.get(module.name, ()), key=lambda item: item.start
            )
        )
        if body_parts:
            body = "\n\n".join(body_parts)
            sections.append(f"module {module.name} {{\n{body}\n}}")
    if not modules:
        sections.extend(
            source_bytes[info.start : info.end].decode("utf-8").strip()
            for infos in definitions_by_module.values()
            for info in sorted(infos, key=lambda item: item.start)
        )
    if not sections:
        return module_placeholder(source, analysis)
    return "\n\n".join(sections) + "\n"
