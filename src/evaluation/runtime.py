"""Capture evaluation process output and record timestamps, digests, and command traces."""

from __future__ import annotations

import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from pydantic import BaseModel

from benchmarks.paths import REPO_ROOT
from evaluation.models import (
    OutputMetadataModel,
)
from runtime.process import StreamObserver
from runtime.process import run_process_capture_bytes as capture_process_bytes

DAFNY_VERIFY_MEMORY_LIMIT_BYTES = 10 * 1024 * 1024 * 1024
DAFNY_VERIFY_DOTNET_HEAP_LIMIT = hex(DAFNY_VERIFY_MEMORY_LIMIT_BYTES)


def model_json(payload: BaseModel) -> dict[str, Any]:
    return payload.model_dump(mode="json", exclude_none=True)


def utc_now() -> datetime:
    return datetime.now(timezone.utc)


def iso(dt: datetime) -> str:
    return dt.isoformat(timespec="seconds")


def append_jsonl_dict(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(payload, sort_keys=True) + "\n")


def _append_command_trace_event(
    trace_path: Path | None,
    *,
    event: str,
    trace_context: dict[str, Any],
    extra: dict[str, Any] | None = None,
) -> None:
    if trace_path is None:
        return

    payload = {
        "event": event,
        "at": iso(utc_now()),
        **trace_context,
    }
    if extra is not None:
        payload.update(extra)
    append_jsonl_dict(trace_path, payload)


def safe_log_name(name: str) -> str:
    out = []
    for ch in name:
        if ch.isalnum() or ch in {"-", "_"}:
            out.append(ch)
        else:
            out.append("-")
    return "".join(out)


def sha256_hex(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def count_text_lines(payload: bytes) -> int:
    if not payload:
        return 0
    count = payload.count(b"\n")
    if payload.endswith(b"\n"):
        return count
    return count + 1


def utf8_preview(payload: bytes, *, max_chars: int = 4000) -> str:
    text = payload.decode("utf-8", errors="replace")
    if len(text) <= max_chars:
        return text
    head = max_chars // 2
    tail = max_chars - head
    return text[:head] + "\n...<truncated preview>...\n" + text[-tail:]


def output_metadata(payload: bytes) -> OutputMetadataModel:
    return OutputMetadataModel(
        bytes=len(payload),
        line_count=count_text_lines(payload),
        sha256=sha256_hex(payload),
        preview_utf8=utf8_preview(payload),
    )


def run_command_capture_bytes(
    *,
    command: str,
    env: dict[str, str],
    timeout_sec: int | None,
    cwd: Path | None = None,
    live_stdout: bool,
    live_stderr: bool,
    stdout_observer: StreamObserver | None = None,
    stderr_observer: StreamObserver | None = None,
    trace_path: Path | None = None,
    trace_context: dict[str, Any] | None = None,
    stdout_path: Path | None = None,
    stderr_path: Path | None = None,
) -> tuple[bool, int | None, bytes, bytes]:
    command_trace_context = dict(trace_context or {})

    _append_command_trace_event(
        trace_path,
        event="command_spawn_requested",
        trace_context=command_trace_context,
    )
    try:
        captured = capture_process_bytes(
            ["bash", "-lc", command],
            cwd=cwd if cwd is not None else REPO_ROOT,
            env=env,
            timeout_sec=timeout_sec,
            stdout_path=stdout_path,
            stderr_path=stderr_path,
            stdout_observer=stdout_observer,
            stderr_observer=stderr_observer,
            on_started=lambda process, pgid: _append_command_trace_event(
                trace_path,
                event="command_process_started",
                trace_context=command_trace_context,
                extra={"pid": process.pid, "process_group_id": pgid},
            ),
        )
    except (OSError, RuntimeError) as exc:
        _append_command_trace_event(
            trace_path,
            event="command_spawn_failed",
            trace_context=command_trace_context,
            extra={"error_type": type(exc).__name__, "error": str(exc)},
        )
        raise

    _append_command_trace_event(
        trace_path,
        event="command_process_completed",
        trace_context=command_trace_context,
        extra={
            "pid": captured.pid,
            "timed_out": captured.timed_out,
            "exit_code": captured.returncode,
        },
    )
    return captured.timed_out, captured.returncode, captured.stdout, captured.stderr


_SECRET_ENV_KEY_RE = re.compile(
    r"(^|_)(KEY|TOKEN|SECRET|PASSWORD|PASSWD|PASS|PWD|CREDENTIAL|AUTH|COOKIE)(_|$)",
    re.IGNORECASE,
)


def looks_secret_env_key(name: str) -> bool:
    return bool(_SECRET_ENV_KEY_RE.search(name))


def append_jsonl(path: Path, payload: BaseModel) -> None:
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(model_json(payload), sort_keys=True) + "\n")
