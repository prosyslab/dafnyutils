from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from analysis.models import DefinitionAnalysisImport
from standard_library import (
    DAFNY_ALLOW_WARNINGS_OPTION,
    DAFNY_BENCH_CORE_LIBRARY_OPTION,
    dafny_bench_core_library_options,
    dafny_standard_library_import_errors,
    has_dafny_warning,
    without_expected_dafny_library_warnings,
)


def _import(
    target: str,
    *,
    has_alias: bool = True,
    opened: bool = False,
) -> DefinitionAnalysisImport:
    return DefinitionAnalysisImport(
        moduleName="Runner",
        alias="Library",
        hasAlias=has_alias,
        resolvedTarget=target,
        resolvedTargetSourcePath="/dafny/Source/DafnyStandardLibraries/src/Std/Module.dfy",
        opened=opened,
        sourcePath="/workspace/Runner.dfy",
        start=10,
        end=40,
    )


def _raw_library_warning(source: Path) -> str:
    return (
        f"CLI: Warning: The file '{source.resolve()}' was passed to --library. "
        "Verification for that file might have used options incompatible with the current ones, "
        "or might have been skipped entirely. Use a .doo file to enable Dafny to check that "
        "compatible options were used\n"
    )


# A materialized core source enables the paired library and warning options.
def test_bench_core_library_options_require_materialized_source(tmp_path: Path) -> None:
    core = tmp_path / "bench/core"
    core.mkdir(parents=True)
    (core / "Support.dfy").write_text("module Support {}\n", encoding="utf-8")

    assert dafny_bench_core_library_options(tmp_path) == (
        DAFNY_BENCH_CORE_LIBRARY_OPTION,
        DAFNY_ALLOW_WARNINGS_OPTION,
    )


# A workspace without a core source retains the prior verifier command shape.
def test_bench_core_library_options_skip_missing_source(tmp_path: Path) -> None:
    assert dafny_bench_core_library_options(tmp_path) == ()


# Dafny's compatibility warning is removable only for a real source inside bench/core.
def test_expected_raw_library_warning_is_removed(tmp_path: Path) -> None:
    core = tmp_path / "bench/core"
    core.mkdir(parents=True)
    source = core / "Support.dfy"
    source.write_text("module Support {}\n", encoding="utf-8")

    assert without_expected_dafny_library_warnings(_raw_library_warning(source), tmp_path) == ""


# A raw-library warning outside bench/core must still fail the verifier gate.
def test_out_of_boundary_raw_library_warning_is_retained(tmp_path: Path) -> None:
    source = tmp_path / "Candidate.dfy"
    source.write_text("module Candidate {}\n", encoding="utf-8")
    warning = _raw_library_warning(source)

    assert without_expected_dafny_library_warnings(warning, tmp_path) == warning
    assert has_dafny_warning(warning)


# A symlink cannot make an external source look like an allowed core-library warning.
def test_symlinked_raw_library_warning_is_retained(tmp_path: Path) -> None:
    outside = tmp_path / "Outside.dfy"
    outside.write_text("module Outside {}\n", encoding="utf-8")
    core = tmp_path / "bench/core"
    core.mkdir(parents=True)
    source = core / "Support.dfy"
    source.symlink_to(outside)
    warning = _raw_library_warning(source)

    assert without_expected_dafny_library_warnings(warning, tmp_path) == warning


# Packaged standard-library modules remain unavailable even through a closed alias.
def test_standard_library_policy_rejects_previously_selected_module() -> None:
    assert dafny_standard_library_import_errors((_import("Std.Collections.Seq"),)) == (
        "Dafny standard-library import is not allowed: Std.Collections.Seq",
    )


# An axiom-dependent module must remain unavailable even through a safe import shape.
def test_standard_library_policy_rejects_frames_module() -> None:
    errors = dafny_standard_library_import_errors((_import("Std.Frames"),))

    assert errors == ("Dafny standard-library import is not allowed: Std.Frames",)


# Import shape cannot re-enable a disabled packaged standard-library module.
def test_standard_library_policy_rejects_implicit_alias() -> None:
    errors = dafny_standard_library_import_errors(
        (_import("Std.Collections.Seq", has_alias=False),)
    )

    assert errors == ("Dafny standard-library import is not allowed: Std.Collections.Seq",)


# Opened imports are covered by the same total packaged-library rejection.
def test_standard_library_policy_rejects_opened_import() -> None:
    errors = dafny_standard_library_import_errors((_import("Std.Collections.Seq", opened=True),))

    assert errors == ("Dafny standard-library import is not allowed: Std.Collections.Seq",)


# Internal top-down facts use Path sources and must still reject the import.
def test_standard_library_policy_formats_path_source() -> None:
    @dataclass(frozen=True)
    class InternalImport:
        resolved_target: str
        has_alias: bool
        opened: bool
        source_path: Path

    errors = dafny_standard_library_import_errors(
        (
            InternalImport(
                resolved_target="Std.Collections.Seq",
                has_alias=False,
                opened=False,
                source_path=Path("bench/utils/toy/ToyCore.dfy"),
            ),
        )
    )

    assert errors == ("Dafny standard-library import is not allowed: Std.Collections.Seq",)


# A selected string path must match an internal Path source before policy validation.
def test_standard_library_policy_filters_path_source_by_selected_string() -> None:
    @dataclass(frozen=True)
    class InternalImport:
        resolved_target: str
        has_alias: bool
        opened: bool
        source_path: Path

    errors = dafny_standard_library_import_errors(
        (
            InternalImport(
                resolved_target="Std.Frames",
                has_alias=True,
                opened=False,
                source_path=Path("bench/utils/toy/ToyCore.dfy"),
            ),
        ),
        selected_source_paths=("bench/utils/toy/ToyCore.dfy",),
    )

    assert errors == ("Dafny standard-library import is not allowed: Std.Frames",)
