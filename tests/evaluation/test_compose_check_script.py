"""Exercise the packaged Compose check wrapper with an isolated Docker substitute."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

from evaluation.submission.container_mounts import build_docker_compose_check_command
from evaluation.submission.infrastructure import CANDIDATE_INFRASTRUCTURE_REPORT_ENV


def _run_check(
    tmp_path: Path,
    *,
    env_overrides: dict[str, str] | None = None,
    command: str = "printf 'candidate check'",
) -> subprocess.CompletedProcess[str]:
    fake_bin = tmp_path / "bin"
    fake_bin.mkdir()
    docker = fake_bin / "docker"
    docker.write_text(
        """#!/usr/bin/env bash
case "$1" in
  inspect) exit "${FAKE_INSPECT_STATUS:-1}" ;;
  compose)
    printf '%s\\n' "$@" > "$FAKE_COMPOSE_ARGS"
    printf 'compose progress\\n'
    exit "${FAKE_RUN_STATUS:-0}" ;;
  logs)
    printf 'check stdout\\n'
    printf 'check stderr\\n' >&2
    exit "${FAKE_LOGS_STATUS:-0}" ;;
  rm)
    printf '%s\\n' "$@" > "$FAKE_RM_ARGS"
    if [[ "${FAKE_RM_STATUS:-0}" -ne 0 ]]; then
      printf 'remove failed\\n' >&2
    fi
    exit "${FAKE_RM_STATUS:-0}" ;;
esac
exit 99
""",
        encoding="utf-8",
    )
    docker.chmod(0o755)
    capture_root = tmp_path / "capture"
    capture_root.mkdir()
    env = {
        **os.environ,
        "PATH": f"{fake_bin}:{os.environ['PATH']}",
        "TMPDIR": str(capture_root),
        "FAKE_COMPOSE_ARGS": str(tmp_path / "compose-args"),
        "FAKE_RM_ARGS": str(tmp_path / "rm-args"),
        **(env_overrides or {}),
    }
    invocation = build_docker_compose_check_command(
        compose_files=(tmp_path / "first compose.yml", tmp_path / "second's compose.yml"),
        service="evaluator",
        command=command,
        project_name="evaluation project",
        container_name="evaluation-container",
    )
    return subprocess.run(
        invocation,
        shell=True,
        executable="/bin/bash",
        cwd=tmp_path,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )


# A successful evaluator check passes each Compose argument intact and returns only check output.
def test_compose_check_preserves_arguments_and_check_output(tmp_path: Path) -> None:
    command = "printf 'quoted $HOME'; echo \"second argument\""
    completed = _run_check(tmp_path, command=command)

    assert completed.returncode == 0
    assert completed.stdout == "check stdout\n"
    assert completed.stderr == "check stderr\n"
    assert (tmp_path / "compose-args").read_text(encoding="utf-8").splitlines() == [
        "compose",
        "-p",
        "evaluation project",
        "-f",
        str(tmp_path / "first compose.yml"),
        "-f",
        str(tmp_path / "second's compose.yml"),
        "run",
        "--no-TTY",
        "--interactive=false",
        "--env",
        CANDIDATE_INFRASTRUCTURE_REPORT_ENV,
        "--env",
        "PYTEST_PLUGINS",
        "--name",
        "evaluation-container",
        "evaluator",
        "bash",
        "-lc",
        command,
    ]
    assert (tmp_path / "rm-args").read_text(encoding="utf-8").splitlines() == [
        "rm",
        "-f",
        "evaluation-container",
    ]
    assert list((tmp_path / "capture").iterdir()) == []


# A failed check keeps its exit code and check output after the container is removed.
def test_compose_check_preserves_failed_run_status(tmp_path: Path) -> None:
    completed = _run_check(tmp_path, env_overrides={"FAKE_RUN_STATUS": "7"})

    assert completed.returncode == 7
    assert completed.stdout == "check stdout\n"
    assert completed.stderr == "check stderr\n"
    assert (tmp_path / "rm-args").is_file()


# Docker log retrieval failure reports Compose diagnostics and its own status.
def test_compose_check_reports_log_failure(tmp_path: Path) -> None:
    completed = _run_check(tmp_path, env_overrides={"FAKE_LOGS_STATUS": "8"})

    assert completed.returncode == 8
    assert completed.stdout == ""
    assert "[docker compose] compose progress" in completed.stderr
    assert "[docker logs] check stderr" in completed.stderr
    assert (tmp_path / "rm-args").is_file()


# Container removal failure must take precedence over a successful check.
def test_compose_check_reports_removal_failure(tmp_path: Path) -> None:
    completed = _run_check(tmp_path, env_overrides={"FAKE_RM_STATUS": "9"})

    assert completed.returncode == 9
    assert completed.stdout == ""
    assert completed.stderr == "[docker rm] remove failed\n"


# A pre-existing evaluator container must not be overwritten or removed.
def test_compose_check_refuses_existing_container(tmp_path: Path) -> None:
    completed = _run_check(tmp_path, env_overrides={"FAKE_INSPECT_STATUS": "0"})

    assert completed.returncode == 1
    assert "evaluator container already exists: evaluation-container" in completed.stderr
    assert not (tmp_path / "compose-args").exists()
    assert not (tmp_path / "rm-args").exists()
