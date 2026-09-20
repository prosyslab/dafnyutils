from __future__ import annotations

import hashlib
from pathlib import Path

import pytest

from benchmarks.generated_profile import generate_task_profile
from benchmarks.profiles import coreutils_dafny_analysis_support_files
from benchmarks.repository import BenchmarkRepository
from entry_contract import (
    DafnyEntry,
    EntryContractCheckSession,
    EntryContractManifest,
    EntryContractSchemaVersion,
    EntryValidationFailure,
    create_manifest,
    enumerate_dafny_sources,
    validate_manifest,
    validated_entry_contract,
)


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _workspace(tmp_path: Path) -> tuple[Path, Path, DafnyEntry, tuple[Path, ...]]:
    utility_root = tmp_path / "bench" / "utils" / "toy"
    _write(
        utility_root / "dfyconfig.toml",
        'includes = ["Runtime.dfy"]\n\n[options]\ntarget = "cs"\nno-verify = true\n',
    )
    _write(
        utility_root / "Shared.dfy",
        "module Shared { predicate Nonnegative(value: int) { value >= 0 } }\n",
    )
    _write(
        utility_root / "Pre.dfy",
        """include "Shared.dfy"
module Pre {
  import Shared
  predicate Allowed(value: int) { Shared.Nonnegative(value) }
}
""",
    )
    _write(
        utility_root / "PostA.dfy",
        """include "Shared.dfy"
module PostA {
  import Shared
  predicate SpecA(value: int) { Shared.Nonnegative(value) }
}
""",
    )
    _write(
        utility_root / "PostB.dfy",
        """include "Shared.dfy"
module PostB {
  import Shared
  predicate SpecB(value: int) { Shared.Nonnegative(value) }
}
""",
    )
    _write(
        utility_root / "Helper.dfy",
        "module Helper { lemma Preserve(value: int) ensures value == value {} }\n",
    )
    _write(
        utility_root / "Implementation.dfy",
        """include "Helper.dfy"
include "Pre.dfy"
include "PostA.dfy"
include "PostB.dfy"
module Runner {
  import Helper
  import Pre
  import PostA
  import PostB
  method RunCore(value: int) returns (out: int)
    requires Pre.Allowed(value)
    ensures PostA.SpecA(out) && PostB.SpecB(out)
  {
    Helper.Preserve(value);
    out := value;
  }
}
""",
    )
    runtime = utility_root / "Runtime.dfy"
    _write(runtime, 'include "Implementation.dfy"\nmodule Runtime { method Main() {} }\n')
    execution = DafnyEntry(
        "bench/utils/toy/Implementation.dfy",
        "Runner.RunCore",
    )
    return tmp_path, utility_root, execution, (runtime,)


# Evaluator-owned Dafny tests cannot become candidate specification or implementation inputs.
def test_utility_source_enumeration_excludes_evaluator_tests(tmp_path: Path) -> None:
    _, utility_root, _, _ = _workspace(tmp_path)
    _write(utility_root / "Tests.dfy", "module EvaluatorTests { method Probe() {} }\n")
    _write(utility_root / "nested" / "Tests.dfy", "module CandidateTests {}\n")

    sources = enumerate_dafny_sources(tmp_path, utility_root)

    assert utility_root / "Tests.dfy" not in sources
    assert utility_root / "nested" / "Tests.dfy" in sources
    assert utility_root / "Implementation.dfy" in sources


def _manifest(
    tmp_path: Path,
) -> tuple[tuple[Path, Path, DafnyEntry, tuple[Path, ...]], EntryContractManifest]:
    contract = _workspace(tmp_path)
    return contract, create_manifest(*contract)


# A RunCore with split preconditions and postconditions derives every direct specification root.
def test_entry_contract_derives_split_specification_entries(tmp_path: Path) -> None:
    contract, manifest = _manifest(tmp_path)

    assert manifest.schema_version is EntryContractSchemaVersion.V5
    assert manifest.execution_entry.symbol == "Runner.RunCore"
    assert tuple(entry.symbol for entry in manifest.spec_entries) == (
        "PostA.SpecA",
        "PostB.SpecB",
        "Pre.Allowed",
    )
    symbols = tuple(definition.symbol for definition in manifest.spec_definitions)
    assert symbols.count("Shared.Nonnegative") == 1
    assert {key.split("::", 1)[0] for key in manifest.spec_definition_sha256} == {
        "bench/utils/toy/PostA.dfy",
        "bench/utils/toy/PostB.dfy",
        "bench/utils/toy/Pre.dfy",
        "bench/utils/toy/Shared.dfy",
    }
    assert (
        manifest.project_config_sha256
        == hashlib.sha256((contract[1] / "dfyconfig.toml").read_bytes()).hexdigest()
    )


# Semantic fingerprints must allow body and comment edits outside the locked contract.
def test_entry_contract_allows_candidate_body_and_comment_edits(tmp_path: Path) -> None:
    contract, manifest = _manifest(tmp_path)
    implementation = contract[1] / "Implementation.dfy"
    implementation.write_text(
        implementation.read_text(encoding="utf-8")
        .replace("out := value;", "out := value + 0;")
        .replace(
            "module Runner {",
            "// execution scaffold note\nmodule Runner {",
        )
        .replace(
            "    requires Pre.Allowed(value)",
            "    // public precondition rationale\n    requires Pre.Allowed(value)",
        ),
        encoding="utf-8",
    )
    shared = contract[1] / "Shared.dfy"
    shared.write_text(
        shared.read_text(encoding="utf-8").replace(
            "{ value >= 0 }",
            "{ /* mathematical boundary */ value >= 0 }",
        ),
        encoding="utf-8",
    )
    runtime = contract[3][0]
    runtime.write_text(
        "// command-line support note\n" + runtime.read_text(encoding="utf-8"),
        encoding="utf-8",
    )

    assert validate_manifest(contract[0], contract[1], manifest)


# A changed RunCore specification clause invalidates the derived entry contract.
def test_entry_contract_rejects_run_core_contract_mutation(tmp_path: Path) -> None:
    contract, manifest = _manifest(tmp_path)
    implementation = contract[1] / "Implementation.dfy"
    implementation.write_text(
        implementation.read_text(encoding="utf-8").replace(
            "PostB.SpecB(out)", "PostB.SpecB(out + 0)"
        ),
        encoding="utf-8",
    )

    with pytest.raises(EntryValidationFailure, match="header changed|structured contract changed"):
        validate_manifest(contract[0], contract[1], manifest)


# Every source containing a reachable specification definition is immutable.
def test_entry_contract_rejects_reachable_specification_mutation(tmp_path: Path) -> None:
    contract, manifest = _manifest(tmp_path)
    shared = contract[1] / "Shared.dfy"
    shared.write_text(
        shared.read_text(encoding="utf-8").replace("value >= 0", "value > 0"),
        encoding="utf-8",
    )

    with pytest.raises(EntryValidationFailure, match="specification definition changed"):
        validate_manifest(contract[0], contract[1], manifest)


# The command-line build source remains immutable without becoming an execution entry.
def test_entry_contract_rejects_build_support_source_mutation(tmp_path: Path) -> None:
    contract, manifest = _manifest(tmp_path)
    runtime = contract[3][0]
    runtime.write_text(
        runtime.read_text(encoding="utf-8").replace(
            "method Main() {}",
            "method Main() { print 1; }",
        ),
        encoding="utf-8",
    )

    with pytest.raises(EntryValidationFailure, match="build support source changed"):
        validate_manifest(contract[0], contract[1], manifest)


# A utility-local source added after baseline creation is still part of integrity analysis.
def test_entry_contract_includes_unreferenced_new_file(tmp_path: Path) -> None:
    contract, manifest = _manifest(tmp_path)
    extra = contract[1] / "proofs" / "Extra.dfy"
    _write(extra, "module Extra { lemma Valid() {} }\n")

    sources = validate_manifest(contract[0], contract[1], manifest)

    assert sources.count(extra) == 1


# Verification sources include reachable candidate files but exclude immutable specifications.
def test_entry_contract_derives_reachable_candidate_verification_sources(
    tmp_path: Path,
) -> None:
    contract, manifest = _manifest(tmp_path)

    validated = validated_entry_contract(contract[0], contract[1], manifest)

    assert validated.execution_source == contract[1] / "Implementation.dfy"
    assert validated.verification_sources == (
        contract[1] / "Helper.dfy",
        contract[1] / "Implementation.dfy",
    )


# An include escaping the workspace is rejected before verification.
def test_entry_contract_rejects_include_escape(tmp_path: Path) -> None:
    contract, manifest = _manifest(tmp_path / "workspace")
    _write(tmp_path / "Outside.dfy", "module Outside {}\n")
    _write(contract[1] / "Escaping.dfy", 'include "../../../../Outside.dfy"\nmodule Escaping {}\n')

    with pytest.raises(EntryValidationFailure, match="outside the workspace"):
        validate_manifest(contract[0], contract[1], manifest)


# A candidate cannot resolve any packaged standard-library module before verification.
def test_entry_contract_rejects_standard_library_import(tmp_path: Path) -> None:
    contract, manifest = _manifest(tmp_path)
    implementation = contract[1] / "Implementation.dfy"
    implementation.write_text(
        implementation.read_text(encoding="utf-8").replace(
            "module Runner {",
            "module Runner {\n  import Frames = Std.Frames",
        ),
        encoding="utf-8",
    )

    with pytest.raises(EntryValidationFailure, match="module Std does not exist"):
        validate_manifest(contract[0], contract[1], manifest)


# A contract result can be reused only while the raw candidate source snapshot is unchanged.
def test_entry_contract_session_rejects_raw_source_change(tmp_path: Path) -> None:
    contract, manifest = _manifest(tmp_path)
    session = EntryContractCheckSession(contract[0], contract[1], manifest)

    validated = session.validate()
    assert session.validate() is validated

    included_source = contract[1] / "Shared.dfy"
    included_source.write_text(
        "// included source spacing change\n" + included_source.read_text(encoding="utf-8"),
        encoding="utf-8",
    )
    with pytest.raises(EntryValidationFailure, match="source snapshot changed"):
        session.validate()


# A contract session binds an external include's lexical path and resolved target.
def test_entry_contract_session_rejects_external_include_retarget(tmp_path: Path) -> None:
    contract = _workspace(tmp_path)
    support_root = tmp_path / "bench" / "core"
    target_a = support_root / "SupportA.dfy"
    target_b = support_root / "SupportB.dfy"
    include_link = support_root / "Support.dfy"
    external_support = support_root / "SupportRoot.dfy"
    _write(target_a, "module SupportA { predicate Valid() { true } }\n")
    _write(target_b, "module SupportB { predicate Valid() { true } }\n")
    include_link.symlink_to(target_a.name)
    _write(external_support, 'include "Support.dfy"\nmodule SupportRoot {}\n')
    manifest = create_manifest(*contract[:3], (contract[3][0], external_support))
    session = EntryContractCheckSession(contract[0], contract[1], manifest)

    session.validate()
    include_link.unlink()
    include_link.symlink_to(target_b.name)

    with pytest.raises(EntryValidationFailure, match="source snapshot changed"):
        session.validate()


# An explicitly analyzed support module can provide a specification without an include edge.
def test_entry_contract_retains_explicit_external_support_specification(tmp_path: Path) -> None:
    utility_root = tmp_path / "bench/utils/toy"
    _write(
        utility_root / "dfyconfig.toml",
        '[options]\ntarget = "cs"\nno-verify = true\n',
    )
    support = tmp_path / "bench/core/ExternalSpec.dfy"
    _write(
        support,
        "module ExternalSpec { predicate Valid(value: int) { value >= 0 } }\n",
    )
    _write(
        utility_root / "Implementation.dfy",
        """module Runner {
  import Spec = ExternalSpec
  method RunCore(value: int) returns (out: int)
    ensures Spec.Valid(out)
  {
    out := value;
  }
}
""",
    )

    manifest = create_manifest(
        tmp_path,
        utility_root,
        DafnyEntry("bench/utils/toy/Implementation.dfy", "Runner.RunCore"),
        (support,),
    )

    assert tuple(definition.symbol for definition in manifest.spec_definitions) == (
        "ExternalSpec.Valid",
    )


# The generated chmod contract spans every source containing its reachable definitions.
def test_chmod_entry_contract_records_split_specification_sources() -> None:
    root = Path(__file__).parents[2]
    manifest = create_manifest(
        root,
        root / "bench" / "utils" / "chmod",
        DafnyEntry(
            "bench/utils/chmod/Chmod.dfy",
            "Chmod.ChmodBenchmarkItem.RunCore",
        ),
        (
            root / "bench/utils/chmod/ChmodCli.dfy",
            *(root / path for path in coreutils_dafny_analysis_support_files("chmod")),
        ),
    )

    assert tuple(entry.symbol for entry in manifest.spec_entries) == ("ChmodRecursiveSpec.Spec",)
    definition = BenchmarkRepository.open(root).load_definition("chmod")
    generated = generate_task_profile(definition, repository_root=root).profile
    assert tuple(
        (definition.source_path, definition.symbol, definition.kind)
        for definition in manifest.spec_definitions
    ) == tuple(
        (definition.source_path, definition.symbol, definition.kind)
        for definition in generated.dafny.spec_definitions
    )
    assert {key.split("::", 1)[0] for key in manifest.spec_definition_sha256} == {
        "bench/core/IO.dfy",
        "bench/core/IOContract.dfy",
        "bench/core/Utf8.dfy",
        "bench/core/World.dfy",
        "bench/core/WorldLookupProof.dfy",
        "bench/utils/chmod/ChmodQuoteSpec.dfy",
        "bench/utils/chmod/ChmodRecursiveSpec.dfy",
        "bench/utils/chmod/ChmodSchema.dfy",
        "bench/utils/chmod/ChmodSpec.dfy",
    }
