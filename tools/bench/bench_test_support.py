"""Provide shared subprocess and verifier helpers for benchmark parity tests."""

from __future__ import annotations

import os
import subprocess
from enum import StrEnum
from pathlib import Path
from typing import Callable, Sequence, TypeVar

from dafny_cli import dafny_command
from evaluation.environment import (
    EVAL_BENCH_BUILD_SCRIPT_ENV,
    EVAL_BENCH_DLL_ENV,
    EVAL_COREUTILS_BIN_ENV,
    EVAL_REPO_ROOT_ENV,
    EVAL_TARGET_ROOT_ENV,
)
from evaluation.submission.candidate_execution import run_candidate
from standard_library import DAFNY_STANDARD_LIBRARY_OPTION

BENCH_COMMAND_TIMEOUT_SEC = 60
_SUBPROCESS_OUTPUT_TAIL_CHARS = 12_000
_DEFAULT_DAFNY_VERIFY_DOTNET_HEAP_LIMIT = hex(10 * 1024 * 1024 * 1024)
_DAFNY_VERIFY_FLAGS = (
    DAFNY_STANDARD_LIBRARY_OPTION,
    "--allow-external-contracts",
    "--dont-verify-dependencies",
)
GNULIB_DIRNAME_CLI_PATHS = (
    ".",
    "..",
    "//d",
    "a\\",
    "a\\b",
    "\\",
    "\\/\\",
    "\\\\/",
    "\\//",
    "//\\",
    "c:",
    "c:/",
    "c://",
    "c:/d",
    "c://d",
    "c:/d/",
    "c:/d/f",
    "c:d",
    "c:d/",
    "c:d/f",
    "a:b:c",
    "a/b:c",
    "a/b:c/",
    "1:",
    "1:/",
    "/:",
    "/:/",
)

StreamT = TypeVar("StreamT", bytes, str)


class StreamMode(StrEnum):
    EXACT = "exact"
    PRESENCE = "presence"
    IGNORE = "ignore"


Normalizer = Callable[[StreamT], StreamT]


def _resolve_repo_path(root: Path, raw_path: str) -> Path:
    candidate = Path(raw_path)
    if candidate.is_absolute():
        return candidate
    return root / candidate


def repo_root(default_root: Path) -> Path:
    override = os.environ.get(EVAL_REPO_ROOT_ENV)
    return _resolve_repo_path(default_root, override).resolve() if override else default_root


def evaluation_target_root(default_root: Path) -> Path:
    override = os.environ.get(EVAL_TARGET_ROOT_ENV)
    return _resolve_repo_path(default_root, override).resolve() if override else default_root


def bench_dll_path(root: Path, default: Path) -> Path:
    override = os.environ.get(EVAL_BENCH_DLL_ENV)
    if not override:
        return default
    return _resolve_repo_path(root, override)


def coreutils_binary_path(root: Path, default: Path) -> Path:
    override = os.environ.get(EVAL_COREUTILS_BIN_ENV)
    if override:
        return _resolve_repo_path(root, override)
    return default


def run_checked_subprocess(
    command: Sequence[str],
    *,
    cwd: Path | str,
    env: dict[str, str] | None = None,
    label: str | None = None,
) -> subprocess.CompletedProcess[str]:
    completed = subprocess.run(
        list(command),
        cwd=cwd,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=env,
    )
    if completed.returncode != 0:
        raise AssertionError(_subprocess_failure_message(completed, cwd=cwd, label=label))
    return completed


def gnulib_digest_large_payload() -> bytes:
    payload = bytearray()
    for i in range(0x400000):
        value = i * (i - 1) * (i - 5)
        payload.append((value >> 6) & 0xFF)
        payload.append(((i % 499) + (i % 101)) & 0xFF)
    return bytes(payload)


def _subprocess_failure_message(
    completed: subprocess.CompletedProcess[str],
    *,
    cwd: Path | str,
    label: str | None,
) -> str:
    title = f"{label} failed" if label else "subprocess failed"
    return "\n".join(
        [
            title,
            f"command: {_format_command(completed.args)}",
            f"cwd: {cwd}",
            f"returncode: {completed.returncode}",
            "stdout:",
            _tail_text(completed.stdout),
            "stderr:",
            _tail_text(completed.stderr),
        ]
    )


def _format_command(args: object) -> str:
    if isinstance(args, (list, tuple)):
        return " ".join(str(arg) for arg in args)
    return str(args)


def _tail_text(text: str | None) -> str:
    if not text:
        return "<empty>"
    if len(text) <= _SUBPROCESS_OUTPUT_TAIL_CHARS:
        return text.rstrip()
    return "<truncated>\n" + text[-_SUBPROCESS_OUTPUT_TAIL_CHARS:].rstrip()


def run_override_build(root: Path) -> bool:
    override = os.environ.get(EVAL_BENCH_BUILD_SCRIPT_ENV)
    if not override:
        return False

    env = os.environ.copy()
    _ = env.setdefault("DOTNET_ROOT", "/usr/share/dotnet")
    _ = run_checked_subprocess(
        [str(_resolve_repo_path(root, override))],
        cwd=root,
        env=env,
        label="override bench build",
    )
    return True


def parity_env() -> dict[str, str]:
    env = os.environ.copy()
    env.setdefault("DOTNET_ROOT", "/usr/share/dotnet")
    env.setdefault("NUGET_PACKAGES", "/home/vscode/.nuget/packages")
    env.setdefault("RestoreSources", env["NUGET_PACKAGES"])
    env.setdefault("RestoreIgnoreFailedSources", "true")
    env["LC_ALL"] = "C"
    env["LANG"] = "C"
    env["TZ"] = "UTC0"
    env["TERM"] = "dumb"
    env["NO_COLOR"] = "1"
    env["CLICOLOR_FORCE"] = "0"
    env["FORCE_COLOR"] = "0"
    return env


def build_bench_utility(root: Path, util: str) -> None:
    if run_override_build(root):
        return
    env = os.environ.copy()
    _ = env.setdefault("DOTNET_ROOT", "/usr/share/dotnet")
    _ = run_checked_subprocess(
        ["make", "build", f"TASK={util}"],
        cwd=root,
        env=env,
        label=f"build {util}",
    )


def build_coreutils_utility(root: Path, util: str) -> None:
    _ = run_checked_subprocess(
        ["make", "build-coreutils"],
        cwd=root,
        label="build-coreutils",
    )


def latest_bench_utility_source_mtime(root: Path, util: str) -> float:
    sources = [
        root / "bench" / "core" / "IO.dfy",
        root / "bench" / "core" / "IOExtern.cs",
    ]
    sources.extend((root / "bench" / "core").glob("*.dfy"))
    sources.extend((root / "bench" / "utils" / util).glob("*.dfy"))
    newest = 0.0
    for source in sources:
        try:
            newest = max(newest, source.stat().st_mtime)
        except FileNotFoundError:
            continue
    return newest


def run_bench_utility(
    bench_dll: Path,
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
    env: dict[str, str] | None = None,
) -> tuple[bytes, bytes, int]:
    completed = run_candidate(
        bench_dll,
        args,
        cwd=cwd,
        check=False,
        input=input_data,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=env or parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def run_coreutils_utility(
    binary: Path,
    util: str,
    args: list[str],
    cwd: Path,
    *,
    input_data: bytes = b"",
    env: dict[str, str] | None = None,
) -> tuple[bytes, bytes, int]:
    completed = subprocess.run(
        [util, *args],
        executable=str(binary),
        cwd=cwd,
        check=False,
        input=input_data,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
        env=env or parity_env(),
        timeout=BENCH_COMMAND_TIMEOUT_SEC,
    )
    return completed.stdout, completed.stderr, completed.returncode


def run_dafny_verify(target: Path, extra_flags: Sequence[str] = ()) -> None:
    env = os.environ.copy()
    dafny = dafny_command()
    env["TMPDIR"] = "/tmp"
    _ = env.setdefault("DOTNET_ROOT", "/usr/share/dotnet")
    heap_limit = env.setdefault(
        "DOTNET_GCHeapHardLimit",
        _DEFAULT_DAFNY_VERIFY_DOTNET_HEAP_LIMIT,
    )
    _ = env.setdefault("COMPlus_GCHeapHardLimit", heap_limit)
    _ = run_checked_subprocess(
        [dafny, "verify", str(target), *_DAFNY_VERIFY_FLAGS, *extra_flags],
        cwd="/tmp",
        env=env,
        label=f"dafny verify {target}",
    )


def _normalize_stream(
    stream: StreamT,
    normalizer: Normalizer[StreamT] | None,
) -> StreamT:
    if normalizer is None:
        return stream
    return normalizer(stream)


def _assert_stream_matches(
    reference: StreamT,
    bench: StreamT,
    *,
    mode: StreamMode,
    normalizer: Normalizer[StreamT] | None = None,
) -> None:
    normalized_reference = _normalize_stream(reference, normalizer)
    normalized_bench = _normalize_stream(bench, normalizer)
    if mode == StreamMode.IGNORE:
        return
    if mode == StreamMode.EXACT:
        assert normalized_bench == normalized_reference
        return
    assert bool(normalized_bench) == bool(normalized_reference)


def assert_result_matches_reference(
    ref_result: tuple[StreamT, StreamT, int],
    bench_result: tuple[StreamT, StreamT, int],
    *,
    stdout_mode: StreamMode = StreamMode.EXACT,
    stderr_mode: StreamMode = StreamMode.EXACT,
    ignore_stderr_when_exit_nonzero: bool = True,
    stdout_normalizer: Normalizer[StreamT] | None = None,
    stderr_normalizer: Normalizer[StreamT] | None = None,
) -> None:
    assert bench_result[2] == ref_result[2]
    effective_stderr_mode = stderr_mode
    if ignore_stderr_when_exit_nonzero and ref_result[2] != 0:
        effective_stderr_mode = StreamMode.IGNORE
    _assert_stream_matches(
        ref_result[0],
        bench_result[0],
        mode=stdout_mode,
        normalizer=stdout_normalizer,
    )
    _assert_stream_matches(
        ref_result[1],
        bench_result[1],
        mode=effective_stderr_mode,
        normalizer=stderr_normalizer,
    )


def assert_requested_message_behavior(
    ref_result: tuple[StreamT, StreamT, int],
    bench_result: tuple[StreamT, StreamT, int],
) -> None:
    assert_result_matches_reference(
        ref_result,
        bench_result,
        stdout_mode=StreamMode.PRESENCE,
        stderr_mode=StreamMode.PRESENCE,
    )
