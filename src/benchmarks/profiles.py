"""Derive authored benchmark paths, outputs, support files, and required check metadata."""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

from benchmarks.paths import REPO_ROOT

from .checks import required_checks_for_kind
from .definition import BenchmarkKind, benchmark_item_directory, class_name_for_task_id
from .repository import BenchmarkRepository

FUNCTIONAL_CORE_SOURCE = "bench/core/Functional.dfy"

COREUTILS_IMPLEMENTATION_SUPPORT_FILES = (
    "bench/core/World.dfy",
    "bench/core/WorldLookupProof.dfy",
    "bench/core/WorldInsertProof.dfy",
    "bench/core/WorldRemoveProof.dfy",
    "bench/core/WorldRenameProof.dfy",
    "bench/core/WorldFileSystemProof.dfy",
    "bench/core/Utf8.dfy",
    "bench/core/IO.dfy",
    "bench/core/IOContract.dfy",
    "bench/core/SecurityModel.dfy",
    "bench/core/BenchmarkItem.dfy",
    "bench/core/CliTypes.dfy",
    "bench/core/CliModel.dfy",
    "bench/core/CliExtern.dfy",
    "bench/core/IOExtern.cs",
    FUNCTIONAL_CORE_SOURCE,
)
COREUTILS_DAFNY_ANALYSIS_SUPPORT_FILES = tuple(
    path for path in COREUTILS_IMPLEMENTATION_SUPPORT_FILES if path.endswith(".dfy")
)


@dataclass(frozen=True)
class ResolvedDafnyEntry:
    source_path: str
    symbol: str


@dataclass(frozen=True)
class ResolvedOutput:
    kind: str
    path: str
    role: str


@dataclass(frozen=True)
class ResolvedTaskProfile:
    support_files: tuple[str, ...]
    editable_outputs: tuple[str, ...]
    placeholder_outputs: tuple[str, ...]
    required_checks: tuple[str, ...]
    required_outputs: tuple[ResolvedOutput, ...]
    execution_entry: ResolvedDafnyEntry


@dataclass(frozen=True)
class ResolvedBenchmark:
    """Internal values derived from a validated benchmark task identifier."""

    name: str
    class_name: str
    official_doc_node: str | None
    task_label: str | None
    task_domain: str | None
    task_profile: ResolvedTaskProfile = field(init=False)

    @classmethod
    def for_task(cls, task_id: str) -> ResolvedBenchmark:
        class_name = derived_utility_class_name(task_id)
        algorithm = is_algorithm_utility(task_id)
        return cls(
            name=task_id,
            class_name=class_name,
            official_doc_node=None if algorithm else f"{task_id} invocation",
            task_label=f"problem {_algorithm_id(task_id)}" if algorithm else None,
            task_domain="algorithm" if algorithm else None,
        )

    def __post_init__(self) -> None:
        value = self.name
        if re.fullmatch(r"[a-z0-9][a-z0-9-]*", value) is None:
            raise ValueError("benchmark name must be safe for Make targets and path derivation")
        object.__setattr__(self, "task_profile", derived_task_profile(self, self.name))

    @property
    def utility_dir(self) -> str:
        return utility_paths(self, self.name)["utility_dir"]

    @property
    def disabled_checks(self) -> dict[str, str]:
        return {}


@dataclass(frozen=True)
class BenchmarkProject:
    name: str
    project_config: str


def benchmark_projects(root: Path = REPO_ROOT) -> tuple[BenchmarkProject, ...]:
    repository = BenchmarkRepository.open(root)
    return tuple(
        BenchmarkProject(
            name=definition.task_id,
            project_config=definition.project_config_path,
        )
        for definition in repository.definitions()
    )


def required_checks_for_task(
    utility_cfg: ResolvedBenchmark,
) -> tuple[str, ...]:
    return utility_cfg.task_profile.required_checks


def utility_class_name(utility_cfg: ResolvedBenchmark) -> str:
    return utility_cfg.class_name


def is_algorithm_utility(utility_name: str) -> bool:
    return utility_name.startswith("algorithm-")


def coreutils_dafny_analysis_support_files(utility_name: str) -> tuple[str, ...]:
    if is_algorithm_utility(utility_name):
        return (FUNCTIONAL_CORE_SOURCE,)
    return COREUTILS_DAFNY_ANALYSIS_SUPPORT_FILES


def coreutils_dafny_analysis_support_paths(
    utility_name: str,
    root: Path = REPO_ROOT,
) -> tuple[Path, ...]:
    """Resolve the extra Dafny sources an entry-contract analysis must read for a task."""

    return tuple(root / path for path in coreutils_dafny_analysis_support_files(utility_name))


def _algorithm_id(utility_name: str) -> str:
    return utility_name.removeprefix("algorithm-")


def derived_utility_class_name(utility_name: str) -> str:
    return class_name_for_task_id(utility_name)


def derived_dafny_entries(
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
) -> ResolvedDafnyEntry:
    class_name = utility_class_name(utility_cfg)
    if is_algorithm_utility(utility_name):
        return ResolvedDafnyEntry(f"{class_name}.dfy", f"{class_name}.RunCore")
    return ResolvedDafnyEntry(
        f"{class_name}.dfy", f"{class_name}.{class_name}BenchmarkItem.RunCore"
    )


def utility_paths(utility_cfg: ResolvedBenchmark, utility_name: str) -> dict[str, str]:
    if is_algorithm_utility(utility_name):
        utility_dir = benchmark_item_directory(BenchmarkKind.ALGORITHM, utility_name)
        class_name = utility_cfg.class_name
        return {
            "utility_dir": utility_dir,
            "project_config": f"{utility_dir}/dfyconfig.toml",
            "schema": f"{utility_dir}/Schema.dfy",
            "nl_spec": f"{utility_dir}/{utility_name}.md",
            "spec": f"{utility_dir}/Spec.dfy",
            "core": f"{utility_dir}/Core.dfy",
            "proof": f"{utility_dir}/Proof.dfy",
            "wrapper": f"{utility_dir}/{class_name}.dfy",
            "cli": f"{utility_dir}/{class_name}Cli.dfy",
        }

    class_name = utility_class_name(utility_cfg)
    utility_dir = benchmark_item_directory(BenchmarkKind.COREUTILS, utility_name)
    base = f"{utility_dir}/{class_name}"
    return {
        "utility_dir": utility_dir,
        "project_config": f"{utility_dir}/dfyconfig.toml",
        "schema": f"{base}Schema.dfy",
        "nl_spec": f"{utility_dir}/{utility_name}.md",
        "spec": f"{base}Spec.dfy",
        "core": f"{base}Core.dfy",
        "proof": f"{base}Proof.dfy",
        "wrapper": f"{base}.dfy",
        "cli": f"{base}Cli.dfy",
    }


def derived_task_profile(
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
) -> ResolvedTaskProfile:
    paths = utility_paths(utility_cfg, utility_name)
    if is_algorithm_utility(utility_name):
        return _algorithm_task_profile(utility_cfg, utility_name, paths)
    return _coreutils_task_profile(utility_cfg, utility_name, paths)


def _coreutils_task_profile(
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
    paths: dict[str, str],
) -> ResolvedTaskProfile:
    execution_entry = derived_dafny_entries(utility_cfg, utility_name)
    return _task_profile(
        support_files=(*COREUTILS_IMPLEMENTATION_SUPPORT_FILES,),
        required_checks=required_checks_for_kind(BenchmarkKind.COREUTILS),
        required_outputs=_coreutils_required_outputs(
            paths,
            execution_entry=execution_entry,
            class_name=utility_class_name(utility_cfg),
        ),
        placeholder_outputs=(),
        execution_entry=execution_entry,
        editable_outputs=(paths["utility_dir"],),
    )


def _algorithm_task_profile(
    utility_cfg: ResolvedBenchmark,
    utility_name: str,
    paths: dict[str, str],
) -> ResolvedTaskProfile:
    return _task_profile(
        support_files=(
            paths["schema"],
            paths["spec"],
            paths["wrapper"],
            FUNCTIONAL_CORE_SOURCE,
        ),
        required_checks=required_checks_for_kind(BenchmarkKind.ALGORITHM),
        required_outputs=_required_outputs(
            paths,
        ),
        placeholder_outputs=(paths["core"], paths["proof"]),
        execution_entry=derived_dafny_entries(utility_cfg, utility_name),
        editable_outputs=(paths["utility_dir"],),
    )


def _task_profile(
    *,
    support_files: tuple[str, ...],
    required_checks: tuple[str, ...],
    required_outputs: tuple[ResolvedOutput, ...],
    placeholder_outputs: tuple[str, ...],
    execution_entry: ResolvedDafnyEntry,
    editable_outputs: tuple[str, ...],
) -> ResolvedTaskProfile:
    return ResolvedTaskProfile(
        support_files=support_files,
        editable_outputs=editable_outputs,
        placeholder_outputs=placeholder_outputs,
        required_checks=required_checks,
        required_outputs=required_outputs,
        execution_entry=execution_entry,
    )


def _coreutils_required_outputs(
    paths: dict[str, str],
    *,
    execution_entry: ResolvedDafnyEntry,
    class_name: str,
) -> tuple[ResolvedOutput, ...]:
    return (
        ResolvedOutput("build_entry", paths["cli"], f"{class_name}Cli.Main"),
        ResolvedOutput(
            "execution_entry",
            f"{paths['utility_dir']}/{execution_entry.source_path}",
            execution_entry.symbol,
        ),
    )


def _required_outputs(paths: dict[str, str]) -> tuple[ResolvedOutput, ...]:
    return (
        _implementation_output(paths["core"], "proof_editable_core"),
        ResolvedOutput("proof", paths["proof"], "proof_target"),
    )


def _implementation_output(path: str, role: str) -> ResolvedOutput:
    return ResolvedOutput("implementation", path, role)
