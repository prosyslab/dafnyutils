from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

import analysis.client as analysis_client
import dafny_cli as dafny_cli
from analysis.client import (
    definition_analysis_document_from_paths,
    definition_analysis_infos_from_paths,
    definition_analysis_infos_from_stdin,
)
from analysis.kinds import DefinitionKind
from analysis.models import (
    DEFINITION_INFO_LIST,
    DafnyFingerprintRegion,
    DafnyFingerprintSpan,
    DefinitionAttribute,
    DefinitionFormal,
    DefinitionInfo,
)
from analysis.queries import (
    spec_dependency_closure,
)
from analysis.source_fingerprints import dafny_source_fingerprints


def _raise_definition_analysis_timeout(*_args, **kwargs):  # noqa: ANN003
    assert kwargs["timeout"] == 300
    raise subprocess.TimeoutExpired(("dafny", "definition-analysis"), timeout=300)


# Every declaration-analysis input form must share the same bounded timeout failure.
def test_definition_analysis_reports_timeout(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = tmp_path / "Slow.dfy"
    source.write_text("method Slow() {}\n", encoding="utf-8")

    monkeypatch.setattr(
        dafny_cli.subprocess,
        "run",
        _raise_definition_analysis_timeout,
    )

    calls = (
        lambda: definition_analysis_document_from_paths((source,)),
        lambda: definition_analysis_infos_from_paths((source,)),
        lambda: definition_analysis_infos_from_stdin(
            "method Slow() {}\n",
            source_dir=tmp_path,
        ),
    )
    for call in calls:
        with pytest.raises(
            RuntimeError,
            match="definition-analysis timed out after 300 seconds",
        ):
            call()


# Semantic facts must be returned by the single definition-analysis subprocess when requested.
def test_definition_analysis_document_requests_semantic_facts_in_one_run(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = tmp_path / "SingleRun.dfy"
    source.write_text("method Run() {}\n", encoding="utf-8")
    calls: list[list[str]] = []

    def run(command: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
        calls.append(command)
        return subprocess.CompletedProcess(
            command,
            0,
            stdout=json.dumps(
                {
                    "definitions": [],
                    "sourceFacts": {
                        "modules": [],
                        "imports": [],
                        "includes": [],
                        "semanticFacts": {"sources": [], "definitions": []},
                    },
                }
            ),
            stderr="",
        )

    monkeypatch.setattr(analysis_client, "_run_definition_analysis", run)

    document = definition_analysis_document_from_paths((source,))

    assert document.source_facts.semantic_facts is not None
    assert len(calls) == 1
    assert "--include-semantic-facts" in calls[0]
    assert "source-fingerprint" not in calls[0]


# Combined semantic facts must match standalone token hashes for every source and definition region.
def test_definition_analysis_semantic_facts_match_source_fingerprint(
    tmp_path: Path,
) -> None:
    included = tmp_path / "Library.dfy"
    included.write_text(
        """module Library {
  // UTF-8 comment: café 설명
  predicate Accepted(value: int) { value >= 0 }
}
""",
        encoding="utf-8",
    )
    source = tmp_path / "Runner.dfy"
    source.write_text(
        """include "Library.dfy"
module Runner {
  import opened Lib = Library
  const Limit: int := 1
  function {:isolate_assertions} Plain(value: int): int { value + Limit }
  function Bodyless(value: int): int
  method Execute(value: int) returns (result: int)
    requires value >= 0
    ensures Lib.Accepted(result)
  {
    result := Plain(value);
  }
}
""",
        encoding="utf-8",
    )

    analyzed = definition_analysis_document_from_paths((source, included))
    semantic_facts = analyzed.source_facts.semantic_facts
    assert semantic_facts is not None

    regions: list[DafnyFingerprintRegion] = []
    source_region_ids: dict[str, tuple[str, str, str]] = {}
    definition_region_ids: dict[tuple[str, str, str], tuple[str, str, str]] = {}

    def add_region(
        source_path: str,
        *,
        included_span: tuple[int, int] | None = None,
        excluded_spans: tuple[tuple[int, int], ...] = (),
    ) -> str:
        region_id = f"region-{len(regions)}"
        regions.append(
            DafnyFingerprintRegion(
                id=region_id,
                sourcePath=source_path,
                includedSpan=(
                    None
                    if included_span is None
                    else DafnyFingerprintSpan(
                        start=included_span[0],
                        end=included_span[1],
                    )
                ),
                excludedSpans=tuple(
                    DafnyFingerprintSpan(start=start, end=end) for start, end in excluded_spans
                ),
            )
        )
        return region_id

    definitions_by_source: dict[str, list[DefinitionInfo]] = {
        str(path.resolve()): [] for path in (included, source)
    }
    for definition in analyzed.definitions:
        definitions_by_source[definition.source_path].append(definition)
    wiring_by_source: dict[str, list[tuple[int, int]]] = {
        str(path.resolve()): [] for path in (included, source)
    }
    for include in analyzed.source_facts.includes:
        wiring_by_source[include.source_path].append((include.start, include.end))
    for imported in analyzed.source_facts.imports:
        wiring_by_source[imported.source_path].append((imported.start, imported.end))

    for source_path in sorted(definitions_by_source):
        definitions = definitions_by_source[source_path]
        declaration_spans = tuple((item.start, item.end) for item in definitions)
        wiring_spans = tuple(wiring_by_source[source_path])
        source_region_ids[source_path] = (
            add_region(source_path),
            add_region(source_path, excluded_spans=declaration_spans),
            add_region(source_path, excluded_spans=declaration_spans + wiring_spans),
        )

    for definition in analyzed.definitions:
        contract_end = definition.body_start or definition.end
        removable_attributes = tuple(
            (attribute.start, attribute.end)
            for attribute in definition.attributes
            if (
                attribute.name == "isolate_assertions"
                and not attribute.arguments
                and definition.start <= attribute.start < attribute.end <= contract_end
            )
        )
        body_start = definition.body_start or definition.start
        definition_region_ids[
            (definition.source_path, definition.full_name, definition.kind.value)
        ] = (
            add_region(
                definition.source_path,
                included_span=(definition.start, definition.end),
            ),
            add_region(
                definition.source_path,
                included_span=(definition.start, contract_end),
                excluded_spans=removable_attributes,
            ),
            add_region(
                definition.source_path,
                included_span=(body_start, definition.end),
            ),
        )

    fingerprints = dafny_source_fingerprints(tuple(regions), cwd=tmp_path)
    for source_fingerprint in semantic_facts.sources:
        full, declaration, scaffold = source_region_ids[source_fingerprint.source_path]
        assert fingerprints[full] == source_fingerprint.full_sha256
        assert fingerprints[declaration] == source_fingerprint.declaration_scaffold_sha256
        assert fingerprints[scaffold] == source_fingerprint.scaffold_sha256
    for definition_fingerprint in semantic_facts.definitions:
        declaration, contract, body = definition_region_ids[
            (
                definition_fingerprint.source_path,
                definition_fingerprint.full_name,
                definition_fingerprint.kind.value,
            )
        ]
        assert fingerprints[declaration] == definition_fingerprint.declaration_sha256
        assert fingerprints[contract] == definition_fingerprint.contract_sha256
        assert fingerprints[body] == definition_fingerprint.body_sha256


# Declaration analysis reports exact verifier-control attributes without flattening arguments.
def test_definition_analysis_reports_declaration_attributes(tmp_path: Path) -> None:
    source = "method {:isolate_assertions} {:verify false} RunCore() {}"

    info = definition_analysis_infos_from_stdin(source, source_dir=tmp_path)[0]

    assert info.attributes == (
        DefinitionAttribute(
            name="isolate_assertions",
            arguments=(),
            start=7,
            end=28,
        ),
        DefinitionAttribute(
            name="verify",
            arguments=("false",),
            start=29,
            end=44,
        ),
    )


# Include availability must remain scoped to the source that owns the directive.
def test_definition_analysis_reports_included_modules_per_source(tmp_path: Path) -> None:
    shared = tmp_path / "shared"
    entry = tmp_path / "entry"
    shared.mkdir()
    entry.mkdir()
    (shared / "Library.dfy").write_text(
        "module Library { method Use() {} }\n",
        encoding="utf-8",
    )
    with_include = entry / "WithInclude.dfy"
    with_include.write_text(
        'include "../shared/Library.dfy"\n'
        "module WithInclude { import Library method Run() { Library.Use(); } }\n",
        encoding="utf-8",
    )
    without_include = entry / "WithoutInclude.dfy"
    without_include.write_text(
        "module WithoutInclude { import Library method Run() { Library.Use(); } }\n",
        encoding="utf-8",
    )

    definitions = definition_analysis_infos_from_paths((with_include, without_include))
    by_name = {definition.full_name: definition for definition in definitions}

    assert by_name["WithInclude.Run"].local_included_modules == ("Library",)
    assert by_name["WithInclude.Run"].imported_modules == ("Library",)
    assert by_name["WithoutInclude.Run"].local_included_modules == ()
    assert by_name["WithoutInclude.Run"].imported_modules == ("Library",)


# Standard-input contract headers must preserve trivia and place generated axioms correctly.
def test_definition_analysis_from_stdin_reports_contract_headers(tmp_path: Path) -> None:
    infos = definition_analysis_infos_from_stdin(
        """
predicate Standard(value: int) { value >= 0 }
predicate\t/* documented */
  Tabbed(value: int) { value >= 0 }
ghost predicate Ghost(value: int) { value >= 0 }
opaque function Opaque(value: int): int { value }
""",
        source_dir=tmp_path,
    )
    by_name = {info.name: info for info in infos}

    assert by_name["Standard"].contract_header_without_axiom == ("predicate Standard(value: int)")
    assert by_name["Standard"].contract_header_with_axiom == (
        "predicate {:axiom} Standard(value: int)"
    )
    assert by_name["Tabbed"].contract_header_without_axiom == (
        "predicate\t/* documented */\n  Tabbed(value: int)"
    )
    assert by_name["Tabbed"].contract_header_with_axiom == (
        "predicate\t/* documented */\n  {:axiom} Tabbed(value: int)"
    )
    assert by_name["Ghost"].contract_header_with_axiom == (
        "ghost predicate {:axiom} Ghost(value: int)"
    )
    assert by_name["Opaque"].contract_header_with_axiom == (
        "opaque function {:axiom} Opaque(value: int): int"
    )


# Document analysis resolves nested includes but emits facts only for the selected root source.
def test_definition_analysis_document_reports_selected_source_and_function_contracts(
    tmp_path: Path,
) -> None:
    leaf = tmp_path / "Leaf.dfy"
    leaf.write_text(
        "module Leaf { predicate {:axiom} Trusted(value: int) }\n",
        encoding="utf-8",
    )
    middle = tmp_path / "Middle.dfy"
    middle.write_text(
        'include "Leaf.dfy"\nmodule Middle { import opened LeafAlias = Leaf }\n',
        encoding="utf-8",
    )
    root = tmp_path / "Root.dfy"
    root.write_text(
        """include "Middle.dfy"
module Root {
  function Next(value: int): (result: int) { value }
  predicate {:axiom} Trusted(value: int)
}
""",
        encoding="utf-8",
    )

    document = definition_analysis_document_from_paths((root,))

    assert {module.name for module in document.source_facts.modules} == {"Root"}
    assert document.source_facts.imports == ()
    assert {
        (Path(item.source_path).name, Path(item.target_path).name)
        for item in document.source_facts.includes
    } == {("Root.dfy", "Middle.dfy")}
    assert {item.full_name for item in document.definitions} == {"Root.Next", "Root.Trusted"}
    next_function = next(item for item in document.definitions if item.full_name == "Root.Next")
    assert next_function.return_details == (
        DefinitionFormal(name="result", type="int", ghost=False),
    )
    trusted = next(item for item in document.definitions if item.full_name == "Root.Trusted")
    assert trusted.contract_header_without_axiom == "predicate Trusted(value: int)"
    assert trusted.contract_header_with_axiom == "predicate {:axiom} Trusted(value: int)"


# Source-fact mode exposes resolved source structure and callable contracts in one document.
def test_definition_analysis_document_reports_resolved_source_facts_and_contract_details(
    tmp_path: Path,
) -> None:
    included = tmp_path / "Library.dfy"
    included.write_text(
        "module Library { predicate Accepted(value: int) { value >= 0 } }\n",
        encoding="utf-8",
    )
    source = tmp_path / "Runner.dfy"
    source.write_text(
        """include "Library.dfy"
module Runner {
  import opened Lib = Library

  method Probe<T>(ghost before: int, after: int) returns (ghost proof: int, result: int)
    requires before >= 0
    reads *
    modifies {}
    decreases after
    ensures Lib.Accepted(result)
    ensures Lib.Accepted(after + 1)
  {
    result := after;
  }
}
""",
        encoding="utf-8",
    )

    analyzed = definition_analysis_document_from_paths((source,))
    document = analyzed.model_dump(by_alias=True, mode="json")
    assert analyzed.source_facts.model_dump(
        by_alias=True,
        mode="json",
        exclude={"semantic_facts"},
    ) == {
        "modules": [
            {
                "name": "Runner",
                "sourcePath": str(source.resolve()),
                "bodyStart": source.read_bytes().index(b"{"),
                "bodyEnd": len(source.read_bytes().rstrip()) - 1,
            },
        ],
        "imports": [
            {
                "moduleName": "Runner",
                "alias": "Lib",
                "hasAlias": True,
                "resolvedTarget": "Library",
                "resolvedTargetSourcePath": str(included.resolve()),
                "opened": True,
                "sourcePath": str(source.resolve()),
                "start": source.read_bytes().index(b"import opened"),
                "end": source.read_bytes().index(b"import opened")
                + len(b"import opened Lib = Library"),
            }
        ],
        "includes": [
            {
                "sourcePath": str(source.resolve()),
                "targetPath": str(included.resolve()),
                "start": 0,
                "end": len(b'include "Library.dfy"'),
            }
        ],
    }
    probe = next(item for item in document["definitions"] if item["fullName"] == "Runner.Probe")
    assert probe["parameterDetails"] == [
        {"name": "before", "type": "int", "ghost": True},
        {"name": "after", "type": "int", "ghost": False},
    ]
    assert probe["returnDetails"] == [
        {"name": "proof", "type": "int", "ghost": True},
        {"name": "result", "type": "int", "ghost": False},
    ]
    assert probe["reads"] == ["*"]
    assert probe["modifies"] == ["{}"]
    assert probe["decreases"] == ["after"]
    assert probe["typeParameters"] == ["T"]
    assert probe["directPostconditionCalls"] == [
        {
            "targetFullName": "Library.Accepted",
            "start": source.read_bytes().index(b"Lib.Accepted(result)"),
            "end": source.read_bytes().index(b"Lib.Accepted(result)")
            + len(b"Lib.Accepted(result)"),
            "text": "Lib.Accepted(result)",
            "arguments": ["result"],
        },
        {
            "targetFullName": "Library.Accepted",
            "start": source.read_bytes().index(b"Lib.Accepted(after + 1)"),
            "end": source.read_bytes().index(b"Lib.Accepted(after + 1)")
            + len(b"Lib.Accepted(after + 1)"),
            "text": "Lib.Accepted(after + 1)",
            "arguments": [None],
        },
    ]
    assert "{:axiom}" not in probe["contractHeaderWithoutAxiom"]
    assert "{:axiom}" in probe["contractHeaderWithAxiom"]


# Opaque rewriting hides its synthetic reveal while retaining source-authored axiom metadata.
def test_definition_analysis_excludes_opaque_reveal_but_retains_axiom_flag(
    tmp_path: Path,
) -> None:
    infos = {
        info.full_name: info
        for info in definition_analysis_infos_from_stdin(
            """module TrustSurface {
  opaque predicate ValidVisitCore(value: int) { value >= 0 }
  predicate {:axiom} Trusted(value: int)
}
""",
            source_dir=tmp_path,
        )
    }

    assert set(infos) == {
        "TrustSurface.ValidVisitCore",
        "TrustSurface.Trusted",
    }
    assert not infos["TrustSurface.ValidVisitCore"].has_axiom_attribute
    assert not infos["TrustSurface.ValidVisitCore"].has_verify_false_attribute
    assert infos["TrustSurface.Trusted"].has_axiom_attribute


# An expect statement is verifier-trusted and must use the existing assumption signal.
def test_definition_analysis_reports_expect_as_trusted_assumption(tmp_path: Path) -> None:
    info = definition_analysis_infos_from_stdin(
        """module TrustSurface {
  method Invalid() {
    expect false;
  }
}
""",
        source_dir=tmp_path,
    )[0]

    assert info.has_assume_statement


def test_definition_analysis_uses_utf8_byte_offsets_after_non_ascii_text(
    tmp_path: Path,
) -> None:
    source = """
module ToySpec {
  // Version text: Torbjörn appears before declarations.
  function ErrnoText(): string { "x" }

  predicate Later() { true }
}
"""

    declarations = {
        info.name: info
        for info in definition_analysis_infos_from_stdin(
            source,
            source_dir=tmp_path,
            spans_only=True,
        )
        if info.kind in {DefinitionKind.FUNCTION, DefinitionKind.PREDICATE}
    }

    source_bytes = source.encode("utf-8")
    errno = declarations["ErrnoText"]
    later = declarations["Later"]
    assert source_bytes[errno.start : errno.end].decode().startswith("function ErrnoText")
    assert source_bytes[later.start : later.end].decode().startswith("predicate Later")
    assert declarations["ErrnoText"].kind == DefinitionKind.FUNCTION
    assert declarations["ErrnoText"].kind == "function"


# Resolved references identify local functions, constants, datatypes, and constructors by byte span.
def test_definition_analysis_reports_resolved_definition_reference_spans(
    tmp_path: Path,
) -> None:
    source = """
module Refs {
  const Limit: int := 2
  datatype Choice = Empty | Value(item: int)

  function Id(choice: Choice): Choice {
    choice
  }

  function Use(): Choice {
    Id(Value(Limit))
  }

  function Inspect(choice: Choice): int {
    match choice
    case Empty => 0
    case Value(item) => item
  }
}
"""

    infos = definition_analysis_infos_from_stdin(source, source_dir=tmp_path)
    limit = next(item for item in infos if item.name == "Limit")
    assert limit.kind == "constant"
    assert source.encode("utf-8")[limit.start : limit.end].decode().rstrip() == (
        "const Limit: int := 2"
    )
    use = next(item for item in infos if item.name == "Use")
    references = [
        (
            reference.target_full_name,
            reference.target_module,
            reference.target_kind,
            reference.is_pattern,
            source.encode("utf-8")[reference.start : reference.end].decode("utf-8"),
        )
        for reference in use.references
    ]

    assert references == [
        ("Refs.Choice", "Refs", "datatype", False, "Choice"),
        ("Refs.Id", "Refs", "function", False, "Id"),
        ("Refs.Choice.Value", "Refs", "constructor", False, "Value"),
        ("Refs.Limit", "Refs", "constant", False, "Limit"),
    ]
    inspect = next(item for item in infos if item.name == "Inspect")
    assert [
        (
            reference.target_kind,
            reference.is_pattern,
            source.encode("utf-8")[reference.start : reference.end].decode("utf-8"),
        )
        for reference in inspect.references
    ] == [
        ("datatype", False, "Choice"),
        ("constructor", True, "Empty"),
        ("constructor", True, "Value"),
    ]


# A configured Spec source selects its own closure even when another module has the same names.
def test_spec_dependency_closure_uses_the_selected_source_file(tmp_path: Path) -> None:
    alpha_source = tmp_path / "Alpha.dfy"
    alpha_source.write_text(
        """
module Alpha {
  datatype State = State(value: int)
  predicate Spec(state: State) { state.value == 0 }
}
""",
        encoding="utf-8",
    )
    beta_source = tmp_path / "Beta.dfy"
    beta_source.write_text(
        """

module Beta {
  datatype State = State(value: bool)
  predicate Spec(state: State) { state.value }
}
""",
        encoding="utf-8",
    )

    infos = definition_analysis_infos_from_paths((alpha_source, beta_source))
    closure = spec_dependency_closure(
        infos,
        source_paths=(alpha_source, beta_source),
        spec_entries=((alpha_source, "Alpha.Spec"),),
    )

    assert [info.full_name for info in closure] == ["Alpha.Spec", "Alpha.State"]


# Packaged standard-library dependencies fail analysis when the benchmark disables them.
def test_definition_analysis_rejects_standard_library_dependency(
    tmp_path: Path,
) -> None:
    source = tmp_path / "UsesSeq.dfy"
    source.write_text(
        """
module UsesSeq {
  import Seq = Std.Collections.Seq
  predicate Spec(values: seq<int>) { 0 in Seq.ToSet(values) <==> 0 in values }
}
""",
        encoding="utf-8",
    )

    with pytest.raises(RuntimeError, match="definition-analysis failed"):
        definition_analysis_infos_from_paths((source,))


# An unresolved local include must fail analysis instead of falling back to the full source tree.
def test_definition_analysis_rejects_unresolved_local_include(tmp_path: Path) -> None:
    source = tmp_path / "MissingInclude.dfy"
    source.write_text(
        """
include "NotPresent.dfy"
module MissingInclude {
  predicate Spec() { true }
}
""",
        encoding="utf-8",
    )

    with pytest.raises(RuntimeError, match="definition-analysis failed"):
        definition_analysis_infos_from_paths((source,))


# A twostate Spec reaches recursive helper declarations through Dafny-resolved call edges.
def test_spec_dependency_closure_retains_twostate_recursive_helpers(tmp_path: Path) -> None:
    source = tmp_path / "Recursive.dfy"
    source.write_text(
        """
module Recursive {
  function Countdown(n: int): int
    decreases n
  {
    if n <= 0 then 0 else Countdown(n - 1)
  }

  twostate predicate Spec(n: int) {
    Countdown(n) >= 0
  }
}
""",
        encoding="utf-8",
    )

    infos = definition_analysis_infos_from_paths((source,))
    closure = spec_dependency_closure(
        infos,
        source_paths=(source,),
        spec_entries=((source, "Recursive.Spec"),),
    )

    assert [info.full_name for info in closure] == ["Recursive.Countdown", "Recursive.Spec"]


# Resolved member assignments must distinguish erased ghost-field writes from runtime writes.
def test_definition_analysis_reports_member_assignment_ghostness(tmp_path: Path) -> None:
    source = """
module Runtime {
  class BenchIO {
    ghost var stdout: seq<int>
    var exitCode: int
  }

  method Reset(io: BenchIO)
    modifies io
  {
    io.stdout := [];
    io.exitCode := 0;
  }
}
"""

    reset = next(
        info
        for info in definition_analysis_infos_from_stdin(source, source_dir=tmp_path)
        if info.full_name == "Runtime.Reset"
    )
    assignment_sources = [
        source.encode("utf-8")[assignment.start : assignment.end].decode("utf-8")
        for assignment in reset.member_assignments
    ]

    assert assignment_sources == ["io.stdout := [];", "io.exitCode := 0;"]
    assert [
        (
            assignment.target_full_name,
            assignment.receiver_type,
            assignment.target_is_ghost,
        )
        for assignment in reset.member_assignments
    ] == [
        ("Runtime.BenchIO.stdout", "BenchIO", True),
        ("Runtime.BenchIO.exitCode", "BenchIO", False),
    ]


def _direct_postcondition_callees(source_dir: Path) -> dict[str, tuple[str, ...]]:
    source = """
module ConfiguredSpec {
  predicate Spec(value: int) { value >= 0 }
}

module Runner {
  import ConfiguredSpec

  predicate Spec(value: int) { value >= 0 }
  predicate LocalAlias(value: int) { ConfiguredSpec.Spec(value) }

  method RequiresOnly(value: int)
    requires Spec(value)
    ensures true
  {}

  method Local(value: int)
    ensures (LocalAlias(value))
  {}

  method Configured(value: int)
    ensures ConfiguredSpec.Spec(value)
  {}

  method Nested(value: int)
    ensures ConfiguredSpec.Spec(value) || true
  {}
}
"""
    return {
        info.name: info.direct_postcondition_callees
        for info in definition_analysis_infos_from_stdin(source, source_dir=source_dir)
        if info.name in {"RequiresOnly", "Local", "Configured", "Nested"}
    }


# One resolved document should distinguish requires from every supported ensures call shape.
def test_definition_analysis_resolves_direct_postcondition_callees(tmp_path: Path) -> None:
    assert _direct_postcondition_callees(tmp_path) == {
        "RequiresOnly": (),
        "Local": ("Runner.LocalAlias",),
        "Configured": ("ConfiguredSpec.Spec",),
        "Nested": ("ConfiguredSpec.Spec",),
    }


# Dafny reports twostate predicates as their own definition kind in JSON output.
def test_definition_info_accepts_twostate_predicate_kind() -> None:
    definitions = DEFINITION_INFO_LIST.validate_python(
        [
            {
                "name": "Stable",
                "fullName": "ToySpec.Stable",
                "kind": "twostate predicate",
                "enclosingName": "ToySpec",
                "line": 3,
                "column": 3,
                "start": 10,
                "bodyStart": 42,
                "end": 50,
                "ghost": True,
                "hasByMethod": False,
                "hasLoop": False,
                "worldRelated": False,
                "declarationKind": "twostate predicate",
                "recursive": False,
                "recursiveGroup": [],
                "callees": [],
                "references": [],
                "returns": [],
                "returnNames": [],
                "requires": [],
                "ensures": [],
                "modifies": [],
            }
        ]
    )

    assert definitions[0].kind == DefinitionKind.TWOSTATE_PREDICATE
