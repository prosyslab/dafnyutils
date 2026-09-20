"""Enforce benchmark Dafny library boundaries and classify expected library diagnostics."""

from __future__ import annotations

from collections.abc import Collection
from pathlib import Path
from typing import Protocol

DAFNY_STANDARD_LIBRARY_OPTION = "--standard-libraries:false"
DAFNY_BENCH_CORE_LIBRARY_DIRECTORY = Path("bench/core")
DAFNY_BENCH_CORE_LIBRARY_OPTION = "--library:bench/core"
DAFNY_ALLOW_WARNINGS_OPTION = "--allow-warnings"

_RAW_LIBRARY_WARNING_PREFIX = "CLI: Warning: The file '"
_RAW_LIBRARY_WARNING_SUFFIX = (
    "' was passed to --library. Verification for that file might have used options "
    "incompatible with the current ones, or might have been skipped entirely. Use a .doo "
    "file to enable Dafny to check that compatible options were used"
)


def dafny_bench_core_library_options(workspace_root: Path) -> tuple[str, ...]:
    """Return the raw core-library options only for a materialized core directory."""

    library_root = workspace_root / DAFNY_BENCH_CORE_LIBRARY_DIRECTORY
    if not library_root.is_dir() or library_root.is_symlink():
        return ()
    try:
        has_source = any(
            path.is_file() and not path.is_symlink() for path in library_root.rglob("*.dfy")
        )
    except OSError:
        return ()
    if not has_source:
        return ()
    return (DAFNY_BENCH_CORE_LIBRARY_OPTION, DAFNY_ALLOW_WARNINGS_OPTION)


def without_expected_dafny_library_warnings(output: str, workspace_root: Path) -> str:
    """Remove only Dafny's raw-library warning for in-boundary core sources."""

    return without_expected_library_warnings(
        output, ((workspace_root / DAFNY_BENCH_CORE_LIBRARY_DIRECTORY).resolve(),)
    )


def without_expected_library_warnings(output: str, libraries: Collection[Path]) -> str:
    """Remove raw-library warnings only for the explicitly selected library paths."""
    retained: list[str] = []
    for line in output.splitlines(keepends=True):
        warning = line.rstrip("\r\n")
        if warning.startswith(_RAW_LIBRARY_WARNING_PREFIX) and warning.endswith(
            _RAW_LIBRARY_WARNING_SUFFIX
        ):
            source_text = warning[
                len(_RAW_LIBRARY_WARNING_PREFIX) : -len(_RAW_LIBRARY_WARNING_SUFFIX)
            ]
            lexical_source = Path(source_text)
            try:
                source = lexical_source.resolve()
            except (OSError, RuntimeError):
                source = Path()
            if (
                source.suffix == ".dfy"
                and any(
                    source == library or source.is_relative_to(library) for library in libraries
                )
                and source.is_file()
                and not lexical_source.is_symlink()
            ):
                continue
        retained.append(line)
    return "".join(retained)


def has_dafny_warning(output: str) -> bool:
    """Return whether Dafny output still contains a warning diagnostic."""

    return any("Warning:" in line for line in output.splitlines())


class DafnyImportFact(Protocol):
    @property
    def resolved_target(self) -> str: ...

    @property
    def has_alias(self) -> bool: ...

    @property
    def opened(self) -> bool: ...

    @property
    def source_path(self) -> str | Path: ...


def is_dafny_standard_library_target(target: str) -> bool:
    return target == "Std" or target.startswith("Std.")


def is_allowed_dafny_standard_library_symbol(full_name: str) -> bool:
    _ = full_name
    return False


def dafny_standard_library_import_errors(
    imports: Collection[DafnyImportFact],
    *,
    selected_source_paths: Collection[str] | None = None,
) -> tuple[str, ...]:
    """Reject every packaged standard-library import using resolved import facts."""

    selected = set(selected_source_paths) if selected_source_paths is not None else None
    errors: list[str] = []
    for item in imports:
        source_path = str(item.source_path)
        if selected is not None and source_path not in selected:
            continue
        if not is_dafny_standard_library_target(item.resolved_target):
            continue
        errors.append("Dafny standard-library import is not allowed: " + item.resolved_target)
    return tuple(dict.fromkeys(errors))
