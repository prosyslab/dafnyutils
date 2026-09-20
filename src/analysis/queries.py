"""Pure queries over Dafny analysis models."""

from __future__ import annotations

from collections.abc import Collection
from pathlib import Path

from standard_library import is_allowed_dafny_standard_library_symbol

from .models import (
    DafnyDefinitionSemanticFingerprint,
    DafnySourceSemanticFingerprint,
    DefinitionInfo,
    DefinitionKind,
    DefinitionSourceFacts,
)


def source_semantic_fingerprint(
    source_facts: DefinitionSourceFacts,
    source_path: Path,
) -> DafnySourceSemanticFingerprint:
    semantic_facts = source_facts.semantic_facts
    if semantic_facts is None:
        raise ValueError("Dafny source semantic fingerprints are missing")
    resolved = source_path.resolve()
    matches = semantic_facts.sources_by_path.get(resolved, ())
    if len(matches) != 1:
        raise ValueError(f"Dafny source semantic fingerprint is not unique: {source_path}")
    return matches[0]


def definition_semantic_fingerprint(
    source_facts: DefinitionSourceFacts,
    definition: DefinitionInfo,
) -> DafnyDefinitionSemanticFingerprint:
    semantic_facts = source_facts.semantic_facts
    if semantic_facts is None:
        raise ValueError("Dafny definition semantic fingerprints are missing")
    source_path = Path(definition.source_path).resolve()
    matches = semantic_facts.definitions_by_key.get(
        (source_path, definition.full_name, definition.kind),
        (),
    )
    if len(matches) != 1:
        raise ValueError(
            f"Dafny definition semantic fingerprint is not unique: {definition.full_name}"
        )
    return matches[0]


def _definition_infos_by_full_name(
    infos: Collection[DefinitionInfo],
) -> dict[str, DefinitionInfo]:
    by_full_name: dict[str, DefinitionInfo] = {}
    for info in infos:
        if not info.source_path:
            raise RuntimeError(f"definition analysis omitted source path for {info.full_name}")
        if info.full_name in by_full_name:
            raise RuntimeError(f"definition analysis emitted duplicate full name: {info.full_name}")
        by_full_name[info.full_name] = info
    return by_full_name


def spec_dependency_closure(
    infos: Collection[DefinitionInfo],
    *,
    source_paths: Collection[Path],
    spec_entries: Collection[tuple[Path, str]],
) -> tuple[DefinitionInfo, ...]:
    """Resolve configured specification dependency closures or fail closed."""
    allowed_paths = {str(path.resolve()) for path in source_paths}
    resolved_entries = tuple(
        sorted((str(path.resolve()), full_name) for path, full_name in spec_entries)
    )
    if not resolved_entries:
        raise RuntimeError("specification entry set is empty")
    by_full_name = _definition_infos_by_full_name(infos)
    callable_kinds = {
        DefinitionKind.FUNCTION,
        DefinitionKind.PREDICATE,
        DefinitionKind.TWOSTATE_FUNCTION,
        DefinitionKind.TWOSTATE_PREDICATE,
    }
    roots: list[DefinitionInfo] = []
    for source_path, full_name in resolved_entries:
        if source_path not in allowed_paths:
            raise RuntimeError(
                f"specification entry source is outside selected sources: {source_path}"
            )
        root = by_full_name.get(full_name)
        if root is None or root.source_path != source_path or root.kind not in callable_kinds:
            raise RuntimeError(
                "configured specification entry does not resolve to a callable specification "
                f"definition in its source: {full_name}"
            )
        roots.append(root)

    closure: dict[str, DefinitionInfo] = {}
    pending = sorted({root.full_name for root in roots}, reverse=True)
    while pending:
        full_name = pending.pop()
        if full_name in closure:
            continue
        if is_allowed_dafny_standard_library_symbol(full_name):
            continue
        info = by_full_name.get(full_name)
        if info is None:
            raise RuntimeError(f"unresolved definition dependency: {full_name}")
        if info.source_path not in allowed_paths:
            raise RuntimeError(f"definition dependency outside selected sources: {full_name}")
        closure[full_name] = info
        pending.extend(sorted(info.dependencies, reverse=True))
        pending.extend(
            sorted(
                {
                    reference.target_full_name
                    for reference in info.references
                    if reference.target_full_name in by_full_name
                },
                reverse=True,
            )
        )
    return tuple(closure[name] for name in sorted(closure))
