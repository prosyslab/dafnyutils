"""Coverage for evaluator-owned Dafny TRX verification."""

from __future__ import annotations

import subprocess
import xml.etree.ElementTree as ElementTree
from pathlib import Path

import pytest

import entry_contract as contract_checker
import verification as verification_checker
from dafny_cli import dafny_command
from entry_contract import DafnyEntry, EntryContractCheckSession, create_manifest
from verification import _trx_counts, run

REPO_ROOT = Path(__file__).parents[2]


def _write_source(tmp_path: Path, program: str, *, name: str = "Entry.dfy") -> Path:
    source = tmp_path / name
    source.write_text(program, encoding="utf-8")
    return source


def _write_contract(
    tmp_path: Path,
    *,
    proof_body: str = "assert true;",
) -> tuple[Path, Path, Path, Path]:
    core = tmp_path / "bench" / "core"
    core.mkdir(parents=True)
    _write_source(core, "module Support {}\n", name="Support.dfy")
    utility_root = tmp_path / "bench" / "utils" / "toy"
    utility_root.mkdir(parents=True)
    (utility_root / "dfyconfig.toml").write_text(
        'includes = ["Entry.dfy"]\n\n[options]\ntarget = "cs"\nno-verify = true\n',
        encoding="utf-8",
    )
    _write_source(
        utility_root,
        "module Proof { const EBUSY: int := 16 lemma Included() { " + proof_body + " } }\n",
        name="Proof.dfy",
    )
    _write_source(
        utility_root,
        "module Spec { predicate Ok() { true } }\n",
        name="Spec.dfy",
    )
    entry_source = _write_source(
        utility_root,
        """include "Proof.dfy"
include "Spec.dfy"
module Runner {
  import Spec
  method RunCore()
    ensures Spec.Ok()
  {
    assert true;
  }
}
""",
    )
    manifest = create_manifest(
        tmp_path,
        utility_root,
        DafnyEntry("bench/utils/toy/Entry.dfy", "Runner.RunCore"),
    )
    manifest_path = tmp_path / "entry_contract.json"
    manifest_path.write_text(manifest.model_dump_json(indent=2) + "\n", encoding="utf-8")
    return tmp_path, utility_root, manifest_path, entry_source


# Sequential verification announces every target and the active file before running its proof.
def test_run_verifies_reachable_candidate_sources_sequentially(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    workspace_root, utility_root, manifest_path, entry_source = _write_contract(tmp_path)
    commands: list[list[str]] = []

    def pass_verification(
        command: list[str], **_kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        output = capsys.readouterr().out
        if not commands:
            assert output.splitlines() == [
                "Verification targets (2 files):",
                "  bench/utils/toy/Entry.dfy",
                "  bench/utils/toy/Proof.dfy",
                "[1/2] Verifying bench/utils/toy/Entry.dfy",
            ]
        else:
            assert output.splitlines() == [
                "[1/2] Completed bench/utils/toy/Entry.dfy: total=1 failed=0",
                "[2/2] Verifying bench/utils/toy/Proof.dfy",
            ]
        commands.append(command)
        report_option = command[command.index("--log-format") + 1]
        report_path = Path(report_option.split("LogFileName=", 1)[1])
        report_path.write_text(
            '<TestRun><Results><UnitTestResult outcome="Passed" /></Results></TestRun>',
            encoding="utf-8",
        )
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(verification_checker, "_run_verification_command", pass_verification)

    assert run(workspace_root, utility_root, manifest_path, dafny_command()) == 0
    assert capsys.readouterr().out.splitlines() == [
        "[2/2] Completed bench/utils/toy/Proof.dfy: total=1 failed=0",
        "DAFNY_VERIFICATION_OUTCOME=verified phase=verify",
        "DAFNY_VERIFICATION_RESULT total=2 failed=0",
    ]
    assert all("--standard-libraries:false" in command for command in commands)
    assert all("--library:bench/core" in command for command in commands)
    assert all("--allow-warnings" in command for command in commands)
    assert [command[3] for command in commands] == [str(entry_source)] * 2
    assert [
        option for command in commands for option in command if option.startswith("--filter-")
    ] == [
        "--filter-position=bench/utils/toy/Entry.dfy",
        "--filter-position=bench/utils/toy/Proof.dfy",
    ]
    assert all("--isolate-assertions" in command for command in commands)
    assert all("--verification-time-limit:30" in command for command in commands)


# Final verification must reject warnings that do not come from its core library boundary.
def test_run_rejects_non_library_warning(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    workspace_root, utility_root, manifest_path, _ = _write_contract(tmp_path)

    def warning_verification(
        command: list[str], **_kwargs: object
    ) -> subprocess.CompletedProcess[bytes]:
        return subprocess.CompletedProcess(
            command,
            0,
            stdout=b"Entry.dfy(1,1): Warning: candidate warning\n",
            stderr=b"",
        )

    monkeypatch.setattr(
        verification_checker,
        "_run_verification_command",
        warning_verification,
    )

    assert run(workspace_root, utility_root, manifest_path, dafny_command()) == 1
    output = capsys.readouterr()
    assert "candidate warning" in output.out
    assert "DAFNY_VERIFICATION_OUTCOME=verification_failure phase=verify" in output.out
    assert "[1/2] Verifying bench/utils/toy/Entry.dfy" in output.out
    assert "Completed" not in output.out
    assert "[2/2] Verifying" not in output.out


# Build, proof-layout, and verification phases reuse one checked contract in one process.
def test_run_full_session_reuses_contract_analysis(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    workspace_root, utility_root, manifest_path, _ = _write_contract(tmp_path)
    manifest = create_manifest(
        workspace_root,
        utility_root,
        DafnyEntry("bench/utils/toy/Entry.dfy", "Runner.RunCore"),
    )
    session = EntryContractCheckSession(workspace_root, utility_root, manifest)
    analysis_calls = 0
    original_validate = contract_checker.validated_entry_contract

    def count_validation(*args: object, **kwargs: object):  # noqa: ANN001
        nonlocal analysis_calls
        analysis_calls += 1
        return original_validate(*args, **kwargs)

    def pass_build(
        command: tuple[str, ...] | list[str], **_kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(command, 0)

    def pass_verification(
        command: list[str], **_kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        report_option = command[command.index("--log-format") + 1]
        report_path = Path(report_option.split("LogFileName=", 1)[1])
        report_path.write_text(
            '<TestRun><Results><UnitTestResult outcome="Passed" /></Results></TestRun>',
            encoding="utf-8",
        )
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(contract_checker, "validated_entry_contract", count_validation)
    monkeypatch.setattr(verification_checker, "_run_build_command", pass_build)
    monkeypatch.setattr(verification_checker, "_run_verification_command", pass_verification)

    assert verification_checker.run_full_session(session, dafny_command(), ("build",)) == 0
    assert analysis_calls == 1


# A source edit during the build phase must fail the proof-layout boundary before verification.
def test_run_full_session_rejects_build_source_mutation(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    capfd,
) -> None:
    workspace_root, utility_root, manifest_path, _ = _write_contract(tmp_path)
    manifest = create_manifest(
        workspace_root,
        utility_root,
        DafnyEntry("bench/utils/toy/Entry.dfy", "Runner.RunCore"),
    )
    session = EntryContractCheckSession(workspace_root, utility_root, manifest)

    def mutate_build(
        command: tuple[str, ...] | list[str], **_kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        proof = utility_root / "Proof.dfy"
        proof.write_text(
            "// build phase edit\n" + proof.read_text(encoding="utf-8"), encoding="utf-8"
        )
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(verification_checker, "_run_build_command", mutate_build)

    assert verification_checker.run_full_session(session, dafny_command(), ("build",)) == 1
    output = capfd.readouterr().out
    assert output.count("DAFNY_VERIFICATION_OUTCOME=infrastructure_failure phase=proof_layout") == 1


# An abstract constant must remain a rejected external contract rather than a zero-obligation value.
def test_run_rejects_abstract_constant(tmp_path: Path, capfd) -> None:
    workspace_root, utility_root, manifest_path, _ = _write_contract(tmp_path)
    proof = utility_root / "Proof.dfy"
    proof.write_text(
        "module Proof { const Abstract: int lemma Included() {} }\n",
        encoding="utf-8",
    )
    manifest = create_manifest(
        workspace_root,
        utility_root,
        DafnyEntry("bench/utils/toy/Entry.dfy", "Runner.RunCore"),
    )
    manifest_path.write_text(manifest.model_dump_json(indent=2) + "\n", encoding="utf-8")

    assert run(workspace_root, utility_root, manifest_path, dafny_command()) == 1
    output = capfd.readouterr().out
    assert output.count("DAFNY_VERIFICATION_OUTCOME=verification_failure phase=verify") == 1
    assert "DAFNY_VERIFICATION_RESULT" not in output


# An unproved condition in the include closure should fail without a success marker.
def test_run_rejects_failed_included_verification_condition(tmp_path: Path, capfd) -> None:
    workspace_root, utility_root, manifest_path, _ = _write_contract(
        tmp_path,
        proof_body="assert false;",
    )

    assert run(workspace_root, utility_root, manifest_path, dafny_command()) == 1
    output = capfd.readouterr().out
    assert output.count("DAFNY_VERIFICATION_OUTCOME=verification_failure phase=verify") == 1
    assert "DAFNY_VERIFICATION_RESULT" not in output
    assert "[1/2] Completed bench/utils/toy/Entry.dfy:" in output
    assert "[2/2] Verifying bench/utils/toy/Proof.dfy" in output
    assert "[2/2] Completed" not in output


# A bodyless declaration should not pass merely because Dafny reports zero errors.
def test_run_rejects_real_bodyless_declaration(tmp_path: Path, capfd) -> None:
    workspace_root, utility_root, manifest_path, _ = _write_contract(tmp_path)
    (utility_root / "Proof.dfy").write_text(
        "module Proof { lemma Included()\n  ensures false\n }\n",
        encoding="utf-8",
    )

    assert run(workspace_root, utility_root, manifest_path, dafny_command()) == 1
    output = capfd.readouterr().out
    assert output.count("DAFNY_VERIFICATION_OUTCOME=verification_failure phase=verify") == 1
    assert "DAFNY_VERIFICATION_RESULT" not in output


# A missing trusted entry contract must emit one evidence-infrastructure outcome.
def test_run_classifies_missing_manifest_as_evidence_infrastructure(
    tmp_path: Path,
    capfd,
) -> None:
    workspace_root, utility_root, manifest_path, _ = _write_contract(tmp_path)
    manifest_path.unlink()

    assert run(workspace_root, utility_root, manifest_path, dafny_command()) == 1
    output = capfd.readouterr().out
    assert output.count("DAFNY_VERIFICATION_OUTCOME=infrastructure_failure phase=evidence") == 1
    assert output.count("DAFNY_VERIFICATION_OUTCOME") == 1


# Missing or malformed TRX evidence must be rejected by the report parser.
def test_trx_counts_rejects_invalid_report(tmp_path: Path) -> None:
    report = tmp_path / "malformed.trx"
    report.write_text("<TestRun><Results>", encoding="utf-8")

    with pytest.raises(ElementTree.ParseError):
        _trx_counts(report)
    with pytest.raises(OSError):
        _trx_counts(tmp_path / "missing.trx")
