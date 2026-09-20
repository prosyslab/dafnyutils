"""Capture subprocess output while preserving process-tree cancellation semantics."""

from __future__ import annotations

import os
import signal
import subprocess
import threading
import time
from collections.abc import Buffer
from contextlib import suppress
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, cast


@dataclass(frozen=True)
class CapturedProcess:
    returncode: int | None
    stdout: bytes
    stderr: bytes
    timed_out: bool
    pid: int | None
    process_group_id: int | None
    cancelled: bool = False


StreamObserver = Callable[[bytes], None]
ProcessStartedObserver = Callable[[subprocess.Popen[bytes], int | None], None]

# How long a cancellable wait sleeps between process-exit checks.
_CANCEL_POLL_INTERVAL_SEC = 0.5


def run_process_capture_bytes(
    argv: list[str],
    *,
    env: dict[str, str],
    cwd: Path | None = None,
    timeout_sec: float | None = None,
    stdout_path: Path | None = None,
    stderr_path: Path | None = None,
    stdout_observer: StreamObserver | None = None,
    stderr_observer: StreamObserver | None = None,
    on_started: ProcessStartedObserver | None = None,
    start_new_session: bool = True,
    timeout_stderr_text: str | None = None,
    cancel_event: threading.Event | None = None,
    cancellation_stderr_text: str | None = None,
) -> CapturedProcess:
    stdout_chunks: list[bytes] = []
    stderr_chunks: list[bytes] = []
    stdout_file = _open_tee(stdout_path)
    stderr_file = _open_tee(stderr_path)
    try:
        if cancel_event is not None and cancel_event.is_set():
            if cancellation_stderr_text:
                _append_text(
                    stderr_chunks,
                    stderr_file,
                    stderr_observer,
                    cancellation_stderr_text,
                )
            return CapturedProcess(
                returncode=None,
                stdout=b"",
                stderr=b"".join(stderr_chunks),
                timed_out=False,
                cancelled=True,
                pid=None,
                process_group_id=None,
            )
        process = subprocess.Popen(
            argv,
            cwd=cwd,
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=False,
            start_new_session=start_new_session,
        )
        process_group_id = _process_group_id(process)
        if on_started is not None:
            on_started(process, process_group_id)
        if process.stdout is None or process.stderr is None:
            _terminate_process_tree(process)
            raise RuntimeError("Failed to initialize subprocess pipes")

        stdout_thread = _start_collector(
            process.stdout,
            chunks=stdout_chunks,
            tee_file=stdout_file,
            observer=stdout_observer,
            name="process-stdout-collector",
        )
        stderr_thread = _start_collector(
            process.stderr,
            chunks=stderr_chunks,
            tee_file=stderr_file,
            observer=stderr_observer,
            name="process-stderr-collector",
        )

        try:
            returncode, timed_out, cancelled = _wait_for_process(
                process,
                timeout_sec=timeout_sec,
                cancel_event=cancel_event,
            )
        except BaseException:
            _terminate_process_tree(process)
            raise
        finally:
            stdout_thread.join()
            stderr_thread.join()

        if timed_out and timeout_stderr_text:
            _append_text(stderr_chunks, stderr_file, stderr_observer, timeout_stderr_text)
        if cancelled and cancellation_stderr_text:
            _append_text(
                stderr_chunks,
                stderr_file,
                stderr_observer,
                cancellation_stderr_text,
            )
        return CapturedProcess(
            returncode=returncode,
            stdout=b"".join(stdout_chunks),
            stderr=b"".join(stderr_chunks),
            timed_out=timed_out,
            cancelled=cancelled,
            pid=process.pid,
            process_group_id=process_group_id,
        )
    finally:
        _close_observer(stdout_observer)
        _close_observer(stderr_observer)
        _close_file(stdout_file)
        _close_file(stderr_file)


def _open_tee(path: Path | None) -> Any | None:
    if path is None:
        return None
    path.parent.mkdir(parents=True, exist_ok=True)
    return path.open("wb")


def _close_file(file_obj: Any | None) -> None:
    if file_obj is not None:
        file_obj.close()


def _start_collector(
    stream: Any,
    *,
    chunks: list[bytes],
    tee_file: Any | None,
    observer: StreamObserver | None,
    name: str,
) -> threading.Thread:
    thread = threading.Thread(
        target=_collect_stream,
        kwargs={
            "stream": stream,
            "chunks": chunks,
            "tee_file": tee_file,
            "observer": observer,
        },
        name=name,
        daemon=True,
    )
    thread.start()
    return thread


def _collect_stream(
    *,
    stream: Any,
    chunks: list[bytes],
    tee_file: Any | None,
    observer: StreamObserver | None,
) -> None:
    try:
        while True:
            chunk = _read_stream_chunk(stream)
            if not chunk:
                break
            _record_chunk(chunk, chunks=chunks, tee_file=tee_file, observer=observer)
    finally:
        stream.close()


def _read_stream_chunk(stream: Any) -> bytes:
    read1 = getattr(stream, "read1", None)
    if callable(read1):
        chunk = read1(4096)
    else:
        chunk = stream.read(4096)
    return chunk if isinstance(chunk, bytes) else bytes(cast(Buffer, chunk))


def _record_chunk(
    chunk: bytes,
    *,
    chunks: list[bytes],
    tee_file: Any | None,
    observer: StreamObserver | None,
) -> None:
    chunks.append(chunk)
    if tee_file is not None:
        tee_file.write(chunk)
        tee_file.flush()
    _feed_observer(observer, chunk)


def _append_text(
    stderr_chunks: list[bytes],
    stderr_file: Any | None,
    stderr_observer: StreamObserver | None,
    text: str,
) -> None:
    payload = b"".join(stderr_chunks)
    if payload and not payload.endswith(b"\n"):
        _record_chunk(b"\n", chunks=stderr_chunks, tee_file=stderr_file, observer=stderr_observer)
    _record_chunk(
        text.encode("utf-8"),
        chunks=stderr_chunks,
        tee_file=stderr_file,
        observer=stderr_observer,
    )


def _wait_for_process(
    process: subprocess.Popen[bytes],
    *,
    timeout_sec: float | None,
    cancel_event: threading.Event | None,
) -> tuple[int | None, bool, bool]:
    if cancel_event is None:
        try:
            return process.wait(timeout=timeout_sec), False, False
        except subprocess.TimeoutExpired:
            return _terminate_process_tree(process), True, False

    deadline = None if timeout_sec is None else time.monotonic() + timeout_sec
    while True:
        returncode = process.poll()
        if returncode is not None:
            return returncode, False, False
        remaining = None if deadline is None else deadline - time.monotonic()
        if remaining is not None and remaining <= 0:
            return _terminate_process_tree(process), True, False
        interval = (
            _CANCEL_POLL_INTERVAL_SEC
            if remaining is None
            else min(_CANCEL_POLL_INTERVAL_SEC, remaining)
        )
        # Sleep on the event rather than the process: cancellation wakes immediately, and
        # the exit check costs one non-blocking waitpid per interval instead of a spin.
        if cancel_event.wait(timeout=interval):
            return _terminate_process_tree(process), False, True


def _feed_observer(observer: StreamObserver | None, chunk: bytes) -> None:
    if observer is None:
        return
    observer(chunk)


def _close_observer(observer: StreamObserver | None) -> None:
    if observer is None:
        return
    close = getattr(observer, "close", None)
    if callable(close):
        close()


def _process_group_id(process: subprocess.Popen[bytes]) -> int | None:
    if not hasattr(os, "getpgid"):
        return None
    try:
        return os.getpgid(process.pid)
    except (OSError, ProcessLookupError):
        return None


def _terminate_process_tree(process: subprocess.Popen[bytes]) -> int | None:
    pgid = _process_group_id(process)
    if pgid is not None and hasattr(os, "killpg"):
        try:
            os.killpg(pgid, signal.SIGKILL)
        except (OSError, ProcessLookupError):
            _kill_process(process)
    else:
        _kill_process(process)
    return process.wait()


def _kill_process(process: subprocess.Popen[bytes]) -> None:
    with suppress(OSError, ProcessLookupError):
        process.kill()
