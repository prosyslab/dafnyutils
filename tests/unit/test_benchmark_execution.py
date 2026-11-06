"""Check runtime dispatch with in-memory process and filesystem boundaries."""

from __future__ import annotations

import io
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import cast
from unittest.mock import MagicMock, Mock

import pytest

import tools.execution as candidate_execution
import tools.infrastructure as infrastructure
import tools.pytest_infrastructure as pytest_infrastructure
import tools.test_support as benchmark_test_support
from tools.environment import EVAL_BENCH_EXECUTION_KIND_ENV
from tools.execution import (
    CandidateExecutionKind,
    CandidateInfrastructureError,
    run_candidate,
)


@dataclass
class _CandidateBoundaries:
    resolve: Mock
    which: Mock
    run: Mock
    record_failure: Mock


@pytest.fixture
def boundaries(monkeypatch: pytest.MonkeyPatch) -> _CandidateBoundaries:
    resolution = Mock(return_value=Path("/resolved/program.dll"))

    def resolve(path: Path, *, strict: bool = False) -> Path:
        return resolution(path, strict=strict)

    discovery = Mock(return_value="/runtime/dotnet")
    process = Mock(return_value=subprocess.CompletedProcess([], 7, b"output", b"error"))
    failure = Mock()
    monkeypatch.setattr(Path, "resolve", resolve)
    monkeypatch.setattr(candidate_execution.shutil, "which", discovery)
    monkeypatch.setattr(candidate_execution.subprocess, "run", process)
    monkeypatch.setattr(candidate_execution, "record_candidate_infrastructure_failure", failure)
    monkeypatch.setattr(benchmark_test_support.os, "environ", {})
    return _CandidateBoundaries(resolution, discovery, process, failure)


# The omitted kind preserves Dotnet dispatch and every default subprocess option.
def test_default_dispatch_preserves_dotnet_options(boundaries: _CandidateBoundaries) -> None:
    candidate = Path("/submitted/program")
    cwd = Path("/work")

    result = run_candidate(candidate, ["--flag", "two words"], cwd=cwd)

    boundaries.which.assert_called_once_with("dotnet")
    boundaries.resolve.assert_called_once_with(candidate, strict=True)
    boundaries.run.assert_called_once_with(
        ["/runtime/dotnet", "/resolved/program.dll", "--flag", "two words"],
        cwd=cwd,
        env=None,
        input=None,
        stdin=None,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        check=False,
        timeout=60,
        preexec_fn=None,
    )
    assert result is boundaries.run.return_value


# Both runtimes forward explicit process options without interpreting the filename.
@pytest.mark.parametrize("kind", tuple(CandidateExecutionKind))
def test_explicit_dispatch_preserves_process_options(
    boundaries: _CandidateBoundaries, kind: CandidateExecutionKind
) -> None:
    candidate = Path("/submitted/program.dll")
    cwd = Path("/work")
    env = {"CUSTOM": "value"}
    stdin = io.StringIO("input")
    stdout = io.StringIO()
    preexec = Mock()

    result = run_candidate(
        candidate,
        ["--", "argument"],
        cwd=cwd,
        execution_kind=kind,
        env=env,
        input=None,
        stdin=stdin,
        stdout=stdout,
        stderr=subprocess.STDOUT,
        text=True,
        check=True,
        timeout=3.25,
        preexec_fn=preexec,
    )

    prefix = ["/runtime/dotnet"] if kind == CandidateExecutionKind.DOTNET else []
    boundaries.run.assert_called_once_with(
        [*prefix, "/resolved/program.dll", "--", "argument"],
        cwd=cwd,
        env=env,
        input=None,
        stdin=stdin,
        stdout=stdout,
        stderr=subprocess.STDOUT,
        text=True,
        check=True,
        timeout=3.25,
        preexec_fn=preexec,
    )
    boundaries.resolve.assert_called_once_with(candidate, strict=True)
    if kind == CandidateExecutionKind.NATIVE:
        boundaries.which.assert_not_called()
    else:
        boundaries.which.assert_called_once_with("dotnet")
    assert result is boundaries.run.return_value
    preexec.assert_not_called()


# A missing Dotnet runtime remains an infrastructure error before candidate resolution.
def test_missing_dotnet_records_infrastructure_failure(boundaries: _CandidateBoundaries) -> None:
    boundaries.which.return_value = None

    with pytest.raises(CandidateInfrastructureError, match="candidate execution requires dotnet"):
        run_candidate(Path("/submitted/program"), [], cwd=Path("/work"))

    boundaries.record_failure.assert_called_once_with("candidate execution requires dotnet")
    boundaries.resolve.assert_not_called()
    boundaries.run.assert_not_called()


# Direct helpers honor the trusted process kind rather than a child's environment.
def test_direct_dispatch_uses_trusted_native_setting(boundaries: _CandidateBoundaries) -> None:
    candidate_execution.os.environ[EVAL_BENCH_EXECUTION_KIND_ENV] = "native"

    run_candidate(
        Path("/submitted/program"),
        [],
        cwd=Path("/work"),
        env={EVAL_BENCH_EXECUTION_KIND_ENV: "dotnet"},
    )

    assert boundaries.run.call_args.args[0] == ["/resolved/program.dll"]
    boundaries.which.assert_not_called()


# An explicit runtime remains authoritative when the process selects another kind.
def test_explicit_kind_overrides_trusted_process_setting(boundaries: _CandidateBoundaries) -> None:
    candidate_execution.os.environ[EVAL_BENCH_EXECUTION_KIND_ENV] = "native"

    run_candidate(
        Path("/submitted/program"),
        [],
        cwd=Path("/work"),
        execution_kind=CandidateExecutionKind.DOTNET,
    )

    assert boundaries.run.call_args.args[0] == ["/runtime/dotnet", "/resolved/program.dll"]


# Invalid trusted runtime settings fail before any candidate or process access.
def test_direct_dispatch_rejects_invalid_process_kind(boundaries: _CandidateBoundaries) -> None:
    candidate_execution.os.environ[EVAL_BENCH_EXECUTION_KIND_ENV] = "unknown"

    with pytest.raises(ValueError, match="not a valid CandidateExecutionKind"):
        run_candidate(Path("/submitted/program"), [], cwd=Path("/work"))

    boundaries.resolve.assert_not_called()
    boundaries.which.assert_not_called()
    boundaries.run.assert_not_called()


# An unknown direct runtime choice fails before path lookup or process creation.
def test_unknown_kind_is_rejected(boundaries: _CandidateBoundaries) -> None:
    with pytest.raises(ValueError, match="not a valid CandidateExecutionKind"):
        run_candidate(
            Path("/submitted/program"),
            [],
            cwd=Path("/work"),
            execution_kind=cast(CandidateExecutionKind, "unknown"),
        )

    boundaries.which.assert_not_called()
    boundaries.resolve.assert_not_called()
    boundaries.run.assert_not_called()
    boundaries.record_failure.assert_not_called()


# A missing candidate propagates its path error without a runtime fallback.
@pytest.mark.parametrize("kind", tuple(CandidateExecutionKind))
def test_missing_candidate_is_not_launched(
    boundaries: _CandidateBoundaries, kind: CandidateExecutionKind
) -> None:
    boundaries.resolve.side_effect = FileNotFoundError("missing candidate")

    with pytest.raises(FileNotFoundError, match="missing candidate"):
        run_candidate(Path("/submitted/program"), [], cwd=Path("/work"), execution_kind=kind)

    boundaries.run.assert_not_called()
    boundaries.record_failure.assert_not_called()


# The shared helper selects only the trusted process setting and preserves byte streams.
@pytest.mark.parametrize("configured_kind", (None, "dotnet", "native"))
def test_shared_helper_dispatches_trusted_kind(
    boundaries: _CandidateBoundaries, configured_kind: str | None
) -> None:
    if configured_kind is not None:
        benchmark_test_support.os.environ[EVAL_BENCH_EXECUTION_KIND_ENV] = configured_kind
    candidate = Path("/submitted/program")
    cwd = Path("/work")
    env = {EVAL_BENCH_EXECUTION_KIND_ENV: "dotnet" if configured_kind == "native" else "native"}

    result = benchmark_test_support.run_bench_utility(
        candidate, ["argument"], cwd, input_data=b"input", env=env
    )

    prefix = [] if configured_kind == "native" else ["/runtime/dotnet"]
    boundaries.run.assert_called_once_with(
        [*prefix, "/resolved/program.dll", "argument"],
        cwd=cwd,
        env=env,
        input=b"input",
        stdin=None,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        check=False,
        timeout=benchmark_test_support.BENCH_COMMAND_TIMEOUT_SEC,
        preexec_fn=None,
    )
    assert result == (b"output", b"error", 7)


# An omitted helper environment still uses the deterministic parity environment.
def test_shared_helper_uses_parity_environment(
    boundaries: _CandidateBoundaries, monkeypatch: pytest.MonkeyPatch
) -> None:
    env = {"LANG": "C"}
    parity = Mock(return_value=env)
    monkeypatch.setattr(benchmark_test_support, "parity_env", parity)

    benchmark_test_support.run_bench_utility(Path("/submitted/program"), [], Path("/work"))

    parity.assert_called_once_with()
    assert boundaries.run.call_args.kwargs["env"] is env


# Invalid trusted settings cannot silently choose a runtime or launch a process.
@pytest.mark.parametrize("configured_kind", ("", "unknown", "native.exe"))
def test_shared_helper_rejects_unknown_kind(
    boundaries: _CandidateBoundaries, configured_kind: str
) -> None:
    benchmark_test_support.os.environ[EVAL_BENCH_EXECUTION_KIND_ENV] = configured_kind

    with pytest.raises(ValueError, match="not a valid CandidateExecutionKind"):
        benchmark_test_support.run_bench_utility(Path("/submitted/program"), [], Path("/work"))

    boundaries.which.assert_not_called()
    boundaries.resolve.assert_not_called()
    boundaries.run.assert_not_called()


@dataclass
class _JournalBoundaries:
    create: Mock
    output: MagicMock
    replace: Mock
    unlink: Mock
    mkdir: Mock


@pytest.fixture
def journal(monkeypatch: pytest.MonkeyPatch) -> _JournalBoundaries:
    output = MagicMock()
    output.name = "/reports/.infrastructure-journal"
    context = MagicMock()
    context.__enter__.return_value = output
    create = Mock(return_value=context)
    replace = Mock()
    unlink = Mock()
    mkdir = Mock()
    monkeypatch.setattr(
        infrastructure.os,
        "environ",
        {infrastructure.CANDIDATE_INFRASTRUCTURE_REPORT_ENV: "/reports/setup.json"},
    )
    monkeypatch.setattr(infrastructure.tempfile, "NamedTemporaryFile", create)
    monkeypatch.setattr(Path, "replace", replace)
    monkeypatch.setattr(Path, "unlink", unlink)
    monkeypatch.setattr(Path, "mkdir", mkdir)
    return _JournalBoundaries(create, output, replace, unlink, mkdir)


# Setup failures keep the same JSON record and atomic publication contract.
def test_setup_failure_publishes_reason_journal(journal: _JournalBoundaries) -> None:
    infrastructure.record_candidate_infrastructure_failure("missing dotnet")

    journal.create.assert_called_once_with(
        mode="w",
        encoding="utf-8",
        prefix=".infrastructure-",
        dir=Path("/reports"),
        delete=False,
    )
    journal.output.write.assert_called_once_with('{"reason":"missing dotnet"}\n')
    journal.replace.assert_called_once_with(Path("/reports/setup.json"))
    journal.unlink.assert_called_once_with(missing_ok=True)
    journal.mkdir.assert_not_called()


# Journal creation errors preserve the original infrastructure exception.
def test_setup_failure_survives_unwritable_journal(
    journal: _JournalBoundaries,
    capsys: pytest.CaptureFixture[str],
) -> None:
    journal.create.side_effect = OSError("permission denied")

    error = CandidateInfrastructureError("missing dotnet")

    assert str(error) == "missing dotnet"
    assert capsys.readouterr().err == (
        "could not record candidate setup failure: permission denied\n"
    )
    journal.replace.assert_not_called()
    journal.unlink.assert_not_called()


# Ordinary check failures receive independent evidence beside the setup journal.
def test_check_failure_uses_separate_journal_directory(journal: _JournalBoundaries) -> None:
    infrastructure.record_check_failure()

    journal.mkdir.assert_called_once_with(exist_ok=True)
    journal.create.assert_called_once_with(
        mode="w",
        encoding="utf-8",
        prefix="failure-",
        dir=Path("/reports/check-failures"),
        delete=False,
    )
    journal.output.write.assert_called_once_with("failed\n")
    journal.replace.assert_not_called()
    journal.unlink.assert_not_called()


# An unset reporting destination leaves execution independent of journal storage.
def test_setup_failure_without_destination_performs_no_io(
    journal: _JournalBoundaries,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.delenv(infrastructure.CANDIDATE_INFRASTRUCTURE_REPORT_ENV)

    infrastructure.record_candidate_infrastructure_failure("missing dotnet")

    journal.create.assert_not_called()
    journal.mkdir.assert_not_called()


# The pytest hook records a real assertion failure independently of setup evidence.
def test_pytest_plugin_records_failed_assertion(monkeypatch: pytest.MonkeyPatch) -> None:
    record = Mock()
    monkeypatch.setattr(pytest_infrastructure, "record_check_failure", record)
    call = Mock(excinfo=Mock(value=AssertionError("different output")))
    outcome = Mock()
    outcome.get_result.return_value.failed = True
    hook = pytest_infrastructure.pytest_runtest_makereport(Mock(), call)
    next(hook)

    with pytest.raises(StopIteration):
        hook.send(outcome)

    record.assert_called_once_with()


# A recorded setup exception is classified separately from an assertion failure.
def test_pytest_plugin_preserves_setup_failure_classification(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = Mock()
    monkeypatch.setattr(pytest_infrastructure, "record_check_failure", record)
    monkeypatch.setattr(candidate_execution, "record_candidate_infrastructure_failure", Mock())
    call = Mock(excinfo=Mock(value=CandidateInfrastructureError("missing dotnet")))
    outcome = Mock()
    outcome.get_result.return_value.failed = True
    hook = pytest_infrastructure.pytest_runtest_makereport(Mock(), call)
    next(hook)

    with pytest.raises(StopIteration):
        hook.send(outcome)

    record.assert_not_called()
