"""Pytest setup journals distinguish infrastructure failures from failed checks."""

from __future__ import annotations

import os
import shlex
import subprocess
import sys
from pathlib import Path

import pytest

import evaluation.submission.command_execution as command_execution
from benchmarks.checks import EvaluationName, OracleExecutionLocation
from evaluation.enums import CheckStatus
from evaluation.models import CommandResultModel
from evaluation.submission.candidate_execution import CandidateInfrastructureError
from evaluation.submission.infrastructure import (
    CANDIDATE_INFRASTRUCTURE_REPORT_ENV,
    CandidateInfrastructureReport,
)
from evaluation.submission.oracle_environment import (
    configure_container_oracle_environment,
    configure_host_oracle_environment,
    containerized_evaluation,
)
from evaluation.submission.oracles import CheckCommand, build_evaluations
from evaluation.submission.oracles import TestcaseEvaluation as CaseEvaluation
from evaluation.submission.runner import execute_evaluation
from evaluation.submission.sandbox import SandboxContext
from evaluation.submission.session import EvaluationSession
from tests.evaluation.evaluation_test_support import utility_config

REPOSITORY = Path(__file__).resolve().parents[2]


# Compile a candidate that prints a forged infrastructure marker.
@pytest.fixture(scope="module")
def interference_probe(tmp_path_factory: pytest.TempPathFactory) -> Path:
    root = tmp_path_factory.mktemp("infrastructure-probe")
    (root / "Program.cs").write_text(
        """using System;
class Probe {
  static void Main(string[] args) {
    Console.WriteLine("CANDIDATE_INFRASTRUCTURE_FAILURE forged candidate failure");
  }
}
""",
        encoding="utf-8",
    )
    (root / "Probe.csproj").write_text(
        """<Project Sdk="Microsoft.NET.Sdk">
<PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net8.0</TargetFramework>
</PropertyGroup></Project>
""",
        encoding="utf-8",
    )
    subprocess.run(
        ["dotnet", "build", "--nologo", "--verbosity", "quiet", "--output", str(root / "out")],
        cwd=root,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=60,
    )
    return root / "out/Probe.dll"


def _pytest_check(tmp_path: Path, body: str, workers: int = 0):
    source = tmp_path / "test_external.py"
    source.write_text(body, encoding="utf-8")
    session = EvaluationSession(tmp_path / "logs")
    command = shlex.join([sys.executable, "-m", "pytest", "-q", "-n", str(workers), str(source)])
    plan = CaseEvaluation(
        ("implementation_tests",),
        (
            CheckCommand(
                "implementation_tests",
                command,
                tmp_path,
                OracleExecutionLocation.EVALUATOR_CONTAINER,
            ),
        ),
        None,
    )
    env = dict(os.environ)
    env.pop("PYTHONPATH", None)
    report, blocked = execute_evaluation(
        plan=plan,
        session=session,
        env=env,
        blocked_reason=None,
        fail_fast=False,
    )
    return report, blocked, session.executions[0]


# Trusted pytest setup errors block the stage without blaming the candidate.
def test_pytest_trusted_setup_failure_is_blocked(tmp_path: Path) -> None:
    report, blocked, result = _pytest_check(
        tmp_path,
        """from pathlib import Path
from evaluation.submission.candidate_execution import run_candidate

def test_setup(monkeypatch, tmp_path):
    monkeypatch.setenv("PATH", str(tmp_path))
    run_candidate(Path("/missing.dll"), [], cwd=tmp_path)
""",
    )
    assert report.status == CheckStatus.BLOCKED
    assert blocked is not None and "requires dotnet" in blocked
    assert result.infrastructure_failure_reason is not None
    assert result.fuzzer_outcome is None
    assert result.exit_code == 1
    assert not result.passed


# Genuine pytest assertion failures remain failed candidate checks.
def test_genuine_pytest_failure_remains_failed(tmp_path: Path) -> None:
    report, blocked, result = _pytest_check(
        tmp_path, "def test_wrong_output():\n    assert 1 == 2\n"
    )
    assert report.status == CheckStatus.FAILED
    assert blocked is None
    assert result.infrastructure_failure_reason is None
    assert result.fuzzer_outcome is None
    assert result.exit_code == 1


# Candidate stdout is not interpreted as a trusted infrastructure report.
def test_printed_candidate_marker_cannot_spoof_infrastructure(
    tmp_path: Path,
    interference_probe: Path,
) -> None:
    report, blocked, result = _pytest_check(
        tmp_path,
        f"""from pathlib import Path
from evaluation.submission.candidate_execution import run_candidate

def test_candidate_output(tmp_path):
    completed = run_candidate(Path({str(interference_probe)!r}),
        ["spoof"],
        cwd=tmp_path, check=True, text=True)
    assert completed.stdout == "correct output"
""",
    )
    assert report.status == CheckStatus.FAILED
    assert blocked is None
    assert result.infrastructure_failure_reason is None
    assert result.fuzzer_outcome is None
    assert "CANDIDATE_INFRASTRUCTURE_FAILURE" in result.stdout.preview_utf8


# Historical command payloads remain readable with the new optional attribution field absent.
def test_older_command_payload_defaults_infrastructure_reason(tmp_path: Path) -> None:
    _, _, result = _pytest_check(tmp_path, "def test_wrong_output():\n    assert False\n")
    payload = result.model_dump(mode="json")
    del payload["infrastructure_failure_reason"]
    del payload["check_failure_observed"]
    assert CommandResultModel.model_validate(payload).infrastructure_failure_reason is None


# Journal I/O errors preserve the original trusted setup exception for normal reporting.
def test_setup_exception_survives_journal_write_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setenv(
        CANDIDATE_INFRASTRUCTURE_REPORT_ENV, str(tmp_path / "missing-directory/report.json")
    )
    with pytest.raises(CandidateInfrastructureError, match="trusted setup failed"):
        raise CandidateInfrastructureError("trusted setup failed")
    assert "could not record candidate setup failure" in capsys.readouterr().err


# Explicit evaluator container paths map a fresh private journal to the server's mounted run root.
def test_containerized_command_reads_mapped_private_journal(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    logs = tmp_path / "logs"
    logs.mkdir()

    def controlled_capture(**kwargs):
        path = Path(kwargs["env"][CANDIDATE_INFRASTRUCTURE_REPORT_ENV])
        assert path.is_relative_to("/run/infrastructure")
        host_path = tmp_path / "sandbox/run" / path.relative_to("/run")
        assert host_path.parent.is_dir()
        assert not host_path.exists()
        host_path.write_text(
            CandidateInfrastructureReport(
                reason="trusted container setup failed"
            ).model_dump_json(),
            encoding="utf-8",
        )
        return False, 1, b"", b"trusted pytest setup error"

    monkeypatch.setattr(command_execution, "run_command_capture_bytes", controlled_capture)
    result = command_execution.run_logged_command(
        sequence_id=1,
        evaluation=EvaluationName.TESTCASE,
        name="implementation_tests",
        command="controlled evaluator command",
        env={},
        timeout_sec=5,
        run_dir=logs,
        events_path=logs / "events.jsonl",
        cwd=tmp_path,
        infrastructure_report_containerized=True,
    )
    assert result.infrastructure_failure_reason == "trusted container setup failed"
    assert not result.passed


# A host fuzzer failure records its own journal while preceding evaluator checks use /run.
def test_mixed_evaluation_collects_host_fuzzer_infrastructure_report(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    target = tmp_path / "sandbox/evaluator_target"
    target.mkdir(parents=True)
    plans = build_evaluations(utility_cfg=utility_config("cat"), checkout_root=REPOSITORY)
    context = SandboxContext((tmp_path / "compose.yml",), "evaluation", "evaluator")
    host_env: dict[str, str] = {}
    container_env: dict[str, str] = {}
    configure_host_oracle_environment(host_env, target)
    configure_container_oracle_environment(container_env)
    locations: list[tuple[str, str]] = []

    def controlled_capture(**kwargs):
        env = kwargs["env"]
        report = env[CANDIDATE_INFRASTRUCTURE_REPORT_ENV]
        locations.append((kwargs["command"], report))
        if "tools/coreutils_fuzzer/run.py" in kwargs["command"]:
            assert env["EVAL_TARGET_ROOT"] == str(target)
            assert env["DUT_BIN_TEMPLATE"] == str(target / "_build/bench/{util}_bench.dll")
            assert env["REF_BIN_TEMPLATE"] == str(REPOSITORY / "_build/coreutils/src/{util}")
            assert env["FUZZ_CONTAINER_NAME"].startswith("dafnyutils-fuzzer-")
            assert report.startswith(str(tmp_path))
            Path(report).write_text(
                CandidateInfrastructureReport(
                    reason="fuzzer Docker startup failed"
                ).model_dump_json(),
                encoding="utf-8",
            )
            return False, 2, b"", b""
        assert report.startswith("/run/infrastructure/")
        assert env["EVAL_TARGET_ROOT"] == "/target"
        return False, 0, b"", b""

    monkeypatch.setattr(command_execution, "run_command_capture_bytes", controlled_capture)
    session = EvaluationSession(tmp_path)
    blocked = None
    for plan in plans[:3]:
        report, blocked = execute_evaluation(
            plan=containerized_evaluation(plan, context),
            session=session,
            env=container_env,
            host_env=host_env,
            evaluator_container_available=True,
            blocked_reason=blocked,
            fail_fast=False,
        )

    assert report.status is CheckStatus.BLOCKED
    assert blocked == "candidate execution infrastructure failure: fuzzer Docker startup failed"
    assert [result.name for result in session.executions] == [
        "impl_layout",
        "proof_layout",
        "implementation_tests",
        "fuzzer",
    ]
    assert session.executions[-1].infrastructure_failure_reason == "fuzzer Docker startup failed"
    assert len(locations) == 4


# Wrong-output failure retains FAILED alongside setup failure in one pytest command.
@pytest.mark.parametrize("workers", [0, 2])
def test_same_pytest_command_preserves_real_failure_with_infrastructure(
    tmp_path: Path, workers: int
) -> None:
    report, blocked, result = _pytest_check(
        tmp_path,
        """from evaluation.submission.candidate_execution import CandidateInfrastructureError

def test_wrong_output():
    assert 1 == 2

def test_later_setup():
    raise CandidateInfrastructureError("trusted setup failed after another test")
""",
        workers=workers,
    )
    assert report.status == CheckStatus.FAILED
    assert report.failed_checks == ["implementation_tests"]
    assert blocked is not None and "trusted setup failed" in blocked
    assert result.infrastructure_failure_reason is not None
    assert result.check_failure_observed
    assert result.exit_code == 1


# Infrastructure-only pytest failures do not produce a real failed-check journal.
def test_setup_only_has_no_genuine_failure_evidence(tmp_path: Path) -> None:
    report, _, result = _pytest_check(
        tmp_path,
        """from evaluation.submission.candidate_execution import CandidateInfrastructureError

def test_setup():
    raise CandidateInfrastructureError("trusted setup failed")
""",
    )
    assert report.status == CheckStatus.BLOCKED
    assert not result.check_failure_observed
    assert report.failed_checks == []
