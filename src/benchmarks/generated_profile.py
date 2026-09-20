"""Generate public resources, rules, and workspace metadata from one source analysis."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from benchmarks.contracts import (
    analyze_task_entry_contract,
    dafny_entry_contract,
    validate_final_specification_obligation,
)
from benchmarks.definition import BenchmarkDefinition
from benchmarks.profiles import (
    FUNCTIONAL_CORE_SOURCE,
    ResolvedBenchmark,
    is_algorithm_utility,
    utility_paths,
)
from benchmarks.task import TaskProfile
from entry_contract import EntryContractAnalysis


@dataclass(frozen=True)
class GeneratedTaskProfile:
    """A generated public profile together with the analysis used to derive it."""

    profile: TaskProfile
    entry_analysis: EntryContractAnalysis


def generate_task_profile(
    definition: BenchmarkDefinition,
    *,
    repository_root: Path,
    configuration: ResolvedBenchmark | None = None,
) -> GeneratedTaskProfile:
    """Generate one v2 public contract from a checked source analysis."""
    task_id = definition.task_id
    resolved = configuration or ResolvedBenchmark.for_task(task_id)
    if resolved.name != task_id:
        raise ValueError("resolved benchmark id does not match the definition")
    analysis = analyze_task_entry_contract(resolved, task_id, repository_root=repository_root)
    validate_final_specification_obligation(analysis)
    payload = _profile_payload(resolved, definition, analysis=analysis)
    profile = TaskProfile.model_validate_json(json.dumps(payload))
    validate_task_resource_sources(profile, repository_root)
    return GeneratedTaskProfile(profile=profile, entry_analysis=analysis)


def _profile_payload(
    configuration: ResolvedBenchmark,
    definition: BenchmarkDefinition,
    *,
    analysis: EntryContractAnalysis,
) -> dict[str, object]:
    task_id = definition.task_id
    paths = utility_paths(configuration, task_id)
    contract = dafny_entry_contract(configuration, task_id, analysis=analysis)
    formal_paths = sorted({str(item["source_path"]) for item in contract["spec_definitions"]})
    formal_resources = [
        {
            "resource_id": f"formal-{index:03d}",
            "kind": "formal-specification",
            "path": path,
            "description": f"Authoritative Dafny specification source: {path}",
        }
        for index, path in enumerate(formal_paths, start=1)
    ]
    execution_path = str(contract["execution_entry"]["source_path"])
    required_outputs = [
        {
            "kind": "implementation",
            "path": paths["core"],
            "role": "implementation-core",
        },
        {
            "kind": "proof",
            "path": paths["proof"],
            "role": "proof-target",
        },
    ]
    if execution_path not in {output["path"] for output in required_outputs}:
        required_outputs.append(
            {
                "kind": "generated-source",
                "path": execution_path,
                "role": "execution-entry",
            }
        )
    return {
        "schema_version": "benchmark.task-profile.v2",
        "task_id": task_id,
        "title": definition.title,
        "resources": [
            {
                "resource_id": "natural-spec",
                "kind": "natural-specification",
                "path": paths["nl_spec"],
                "description": f"Required behavior for {task_id}",
            },
            *formal_resources,
            {
                "resource_id": "functional-core",
                "kind": "support",
                "path": FUNCTIONAL_CORE_SOURCE,
                "description": (
                    "Shared verified map, filter, scan, and fold declarations; include this "
                    "source and import BenchFunctional to use them"
                ),
            },
        ],
        "public_rules": [
            {
                "rule_id": "specification-integrity",
                "title": "Preserve the specification",
                "description": (
                    "Do not change any declared natural-language or Dafny specification resource."
                ),
            },
            {
                "rule_id": "no-trusted-bypass",
                "title": "Preserve verification trust",
                "description": (
                    "Do not add assume statements, axioms, trusted external bodies, verification "
                    "skips, or equivalent shortcuts."
                ),
            },
            {
                "rule_id": "workspace-boundary",
                "title": "Respect the editable boundary",
                "description": "Only modify paths declared editable by this task contract.",
            },
            *(
                []
                if is_algorithm_utility(task_id)
                else [
                    {
                        "rule_id": "diagnostic-locale",
                        "title": "Use the C diagnostic locale",
                        "description": (
                            "Coreutils behavior is specified and evaluated with LC_ALL=C; "
                            "LANG=C is also supplied. Locale-dependent behavior outside the C "
                            "locale is outside this task contract."
                        ),
                    },
                    {
                        "rule_id": "time-zone",
                        "title": "Use the UTC0 timezone",
                        "description": (
                            "Coreutils behavior is specified and evaluated with TZ=UTC0. "
                            "Timezone-dependent behavior outside UTC0 is outside this task "
                            "contract."
                        ),
                    },
                ]
            ),
        ],
        "public_checks": [
            {
                "check_id": "verify",
                "title": "Build, boundary, and Dafny verification gate",
                "argv": ["./eval_support/verify.sh"],
                "working_directory": None,
            }
        ],
        "dafny": {
            "utility_root": contract["utility_dir"],
            "execution_entry": contract["execution_entry"],
            "spec_entries": contract["spec_entries"],
            "spec_definitions": contract["spec_definitions"],
        },
        "workspace": {
            "editable_paths": [paths["utility_dir"]],
            "required_outputs": required_outputs,
        },
    }


def validate_task_resource_sources(profile: TaskProfile, repository_root: Path) -> None:
    resolved_root = repository_root.resolve()
    for resource in profile.resources:
        source = (repository_root / resource.path).resolve()
        if not source.is_relative_to(resolved_root):
            raise ValueError(f"task resource escapes repository root: {resource.path}")
        if not source.is_file():
            raise FileNotFoundError(f"task resource is missing: {resource.path}")
