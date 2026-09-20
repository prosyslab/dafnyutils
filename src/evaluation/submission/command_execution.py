"""Run benchmark checks while recording execution evidence."""

from __future__ import annotations

import tempfile
import time
from pathlib import Path
from typing import Any

from benchmarks.checks import EvaluationName
from evaluation.environment import (
    EVAL_REPO_ROOT_ENV,
    EVAL_TARGET_ROOT_ENV,
    EVAL_WORKSPACE_DIR_ENV,
)
from evaluation.models import (
    CommandCompletedEventModel,
    CommandResultModel,
    CommandStartedEventModel,
    OutputDigestModel,
)
from evaluation.runtime import (
    append_jsonl,
    iso,
    output_metadata,
    run_command_capture_bytes,
    safe_log_name,
    utc_now,
)
from evaluation.submission.infrastructure import (
    CANDIDATE_INFRASTRUCTURE_REPORT_ENV,
    CandidateInfrastructureReport,
)
from evaluation.submission.output_adapters import (
    command_passed,
    parse_dafny_verification,
    parse_fuzzer_outcome,
)

_TRACE_ENV_KEYS = (
    "HOME",
    "PWD",
    "TMPDIR",
    "DOTNET_GCHeapHardLimit",
    "COMPlus_GCHeapHardLimit",
    EVAL_REPO_ROOT_ENV,
    EVAL_TARGET_ROOT_ENV,
    EVAL_WORKSPACE_DIR_ENV,
)


def _trace_env_subset(env: dict[str, str]) -> dict[str, str]:
    return {key: env[key] for key in _TRACE_ENV_KEYS if key in env}


def _log_paths(run_dir: Path, sequence_id: int, name: str) -> tuple[Path, Path, Path]:
    command_name = safe_log_name(name)
    return (
        run_dir / f"{sequence_id:02d}_{command_name}.stdout.log",
        run_dir / f"{sequence_id:02d}_{command_name}.stderr.log",
        run_dir / f"{sequence_id:02d}_{command_name}.command.sh",
    )


def _command_trace_context(
    *,
    sequence_id: int,
    evaluation: EvaluationName,
    name: str,
    command: str,
    command_script_path: Path,
    timeout_sec: int | None,
    cwd: Path,
    cwd_label: str,
    env: dict[str, str],
) -> dict[str, Any]:
    return {
        "sequence_id": sequence_id,
        "evaluation": evaluation,
        "name": name,
        "command": command,
        "command_script": str(command_script_path),
        "timeout_sec": timeout_sec,
        "cwd": str(cwd),
        "cwd_label": cwd_label,
        "env": _trace_env_subset(env),
    }


def _run_command(
    *,
    sequence_id: int,
    evaluation: EvaluationName,
    name: str,
    command: str,
    env: dict[str, str],
    timeout_sec: int | None,
    run_dir: Path,
    events_path: Path,
    cwd: Path,
    cwd_label: str,
    live_stdout: bool,
    live_stderr: bool,
    infrastructure_report_containerized: bool,
) -> CommandResultModel:
    infrastructure_root = run_dir.parent / "sandbox/run/infrastructure"
    infrastructure_root.mkdir(parents=True, exist_ok=True)
    journal_directory = Path(
        tempfile.mkdtemp(prefix=f"{sequence_id:02d}-", dir=infrastructure_root)
    )
    journal = journal_directory / "report.json"
    report_path = (
        Path("/run/infrastructure") / journal_directory.name / journal.name
        if infrastructure_report_containerized
        else journal
    )
    plugins = [plugin for plugin in env.get("PYTEST_PLUGINS", "").split(",") if plugin]
    if "evaluation.submission.pytest_infrastructure" not in plugins:
        plugins.append("evaluation.submission.pytest_infrastructure")
    env = {
        **env,
        CANDIDATE_INFRASTRUCTURE_REPORT_ENV: str(report_path),
        "PYTEST_PLUGINS": ",".join(plugins),
    }
    started_at_dt = utc_now()
    started_at = iso(started_at_dt)
    t0 = time.perf_counter()
    stdout_path, stderr_path, command_script_path = _log_paths(run_dir, sequence_id, name)
    command_script_path.write_text(
        "#!/usr/bin/env bash\nset -euo pipefail\n\n" + command + "\n",
        encoding="utf-8",
    )
    command_trace_path = run_dir / "command_trace.jsonl"
    trace_context = _command_trace_context(
        sequence_id=sequence_id,
        evaluation=evaluation,
        name=name,
        command=command,
        command_script_path=command_script_path,
        timeout_sec=timeout_sec,
        cwd=cwd,
        cwd_label=cwd_label,
        env=env,
    )

    append_jsonl(
        events_path,
        CommandStartedEventModel(
            sequence_id=sequence_id,
            evaluation=evaluation,
            name=name,
            started_at=started_at,
            timeout_sec=timeout_sec,
            command=command,
            command_script=str(command_script_path),
            cwd=cwd_label,
        ),
    )

    timed_out, exit_code, stdout_bytes, stderr_bytes = run_command_capture_bytes(
        command=command,
        env=env,
        timeout_sec=timeout_sec,
        cwd=cwd,
        live_stdout=live_stdout,
        live_stderr=live_stderr,
        trace_path=command_trace_path,
        trace_context=trace_context,
        stdout_path=stdout_path,
        stderr_path=stderr_path,
    )

    duration_sec = time.perf_counter() - t0
    completed_at_dt = utc_now()
    completed_at = iso(completed_at_dt)
    stdout_info = output_metadata(stdout_bytes)
    stderr_info = output_metadata(stderr_bytes)
    dafny_evidence = parse_dafny_verification(
        name=name,
        timed_out=timed_out,
        exit_code=exit_code,
        stdout_bytes=stdout_bytes,
        stderr_bytes=stderr_bytes,
    )
    fuzzer_evidence = parse_fuzzer_outcome(
        name=name,
        stdout_bytes=stdout_bytes,
        stderr_bytes=stderr_bytes,
        timed_out=timed_out,
        exit_code=exit_code,
    )
    infrastructure_reason = (
        CandidateInfrastructureReport.model_validate_json(
            journal.read_text(encoding="utf-8")
        ).reason
        if journal.is_file()
        else None
    )
    passed = command_passed(
        name=name,
        timed_out=timed_out,
        exit_code=exit_code,
        stdout_bytes=stdout_bytes,
        stderr_bytes=stderr_bytes,
        dafny_evidence=dafny_evidence,
    )

    passed = passed and infrastructure_reason is None

    append_jsonl(
        events_path,
        CommandCompletedEventModel(
            sequence_id=sequence_id,
            evaluation=evaluation,
            name=name,
            completed_at=completed_at,
            duration_sec=duration_sec,
            timed_out=timed_out,
            exit_code=exit_code,
            passed=passed,
            stdout_log=str(stdout_path),
            stderr_log=str(stderr_path),
            stdout=OutputDigestModel(
                bytes=stdout_info.bytes,
                line_count=stdout_info.line_count,
                sha256=stdout_info.sha256,
            ),
            stderr=OutputDigestModel(
                bytes=stderr_info.bytes,
                line_count=stderr_info.line_count,
                sha256=stderr_info.sha256,
            ),
            cwd=cwd_label,
        ),
    )

    return CommandResultModel(
        evaluation=evaluation,
        name=name,
        command=command,
        cwd=cwd_label,
        started_at=started_at,
        completed_at=completed_at,
        duration_sec=duration_sec,
        timeout_sec=timeout_sec,
        timed_out=timed_out,
        exit_code=exit_code,
        passed=passed,
        command_script=str(command_script_path),
        stdout_log=str(stdout_path),
        stderr_log=str(stderr_path),
        stdout=stdout_info,
        stderr=stderr_info,
        dafny_verification_outcome=dafny_evidence.outcome,
        dafny_verification_phase=dafny_evidence.phase,
        infrastructure_failure_reason=infrastructure_reason,
        check_failure_observed=any((journal_directory / "check-failures").glob("failure-*")),
        fuzzer_outcome=fuzzer_evidence.outcome,
        fuzzer_marker=fuzzer_evidence.marker,
        fuzzer_seed=fuzzer_evidence.seed,
        fuzzer_iteration=fuzzer_evidence.iteration,
        fuzzer_repro_path=fuzzer_evidence.repro_path,
    )


def run_logged_command(
    *,
    sequence_id: int,
    evaluation: EvaluationName,
    name: str,
    command: str,
    env: dict[str, str],
    timeout_sec: int | None,
    run_dir: Path,
    events_path: Path,
    cwd: Path,
    live_stdout: bool = False,
    live_stderr: bool = False,
    infrastructure_report_containerized: bool = False,
) -> CommandResultModel:
    return _run_command(
        sequence_id=sequence_id,
        evaluation=evaluation,
        name=name,
        command=command,
        env=env,
        timeout_sec=timeout_sec,
        run_dir=run_dir,
        events_path=events_path,
        cwd=cwd,
        cwd_label=str(cwd),
        live_stdout=live_stdout,
        live_stderr=live_stderr,
        infrastructure_report_containerized=infrastructure_report_containerized,
    )
