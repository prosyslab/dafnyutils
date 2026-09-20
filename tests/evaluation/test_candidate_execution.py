"""Real compiled probes for direct candidate subprocess behavior."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest

import evaluation.submission.candidate_execution as candidate_execution
from evaluation.submission.candidate_execution import (
    CandidateInfrastructureError,
    run_candidate,
)

_PROBE_SOURCE = """
using System;
using System.IO;
using System.Runtime.InteropServices;
using System.Threading;

class Probe {
  [DllImport("libc")] static extern IntPtr signal(int sig, IntPtr handler);
  [DllImport("libc")] static extern int raise(int sig);
  static int Main(string[] args) {
    if (args[0] == "sigpipe") { signal(13, IntPtr.Zero); raise(13); return 0; }
    if (args[0] == "exit141") { return 141; }
    if (args[0] == "io") {
      Console.Error.Write("stderr");
      Console.WriteLine(Directory.GetCurrentDirectory());
      Console.WriteLine(Environment.GetEnvironmentVariable("PROBE_VALUE"));
      Console.WriteLine(args[1]);
      Console.Out.Flush();
      Console.OpenStandardInput().CopyTo(Console.OpenStandardOutput());
      File.WriteAllText("made", "case-effect");
      return 7;
    }
    if (args[0] == "sleep") { Thread.Sleep(5000); return 0; }
    Console.Write("descriptor-output");
    return 0;
  }
}
"""


# Compile a controlled .NET program using local framework references without new packages.
@pytest.fixture(scope="session")
def candidate_probe(tmp_path_factory: pytest.TempPathFactory) -> Path:
    build = tmp_path_factory.mktemp("candidate-process-probe")
    (build / "Program.cs").write_text(_PROBE_SOURCE, encoding="utf-8")
    (build / "Probe.csproj").write_text(
        """<Project Sdk="Microsoft.NET.Sdk">
<PropertyGroup><OutputType>Exe</OutputType><TargetFramework>net8.0</TargetFramework>
</PropertyGroup></Project>
""",
        encoding="utf-8",
    )
    completed = subprocess.run(
        ["dotnet", "build", "--nologo", "--verbosity", "quiet", "--output", str(build / "out")],
        cwd=build,
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=60,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr
    return build / "out/Probe.dll"


# Writable fixtures preserve cwd, environment, argv, raw streams, exit status and umask.
def test_candidate_preserves_subprocess_observations(candidate_probe: Path, tmp_path: Path) -> None:
    env = {**os.environ, "PROBE_VALUE": "selected-env"}
    literal = "$(touch should-not-expand)"

    completed = run_candidate(
        candidate_probe,
        ["io", literal],
        cwd=tmp_path,
        input=b"raw\x00\xff",
        env=env,
        preexec_fn=lambda: os.umask(0o077),
    )

    assert completed.returncode == 7
    assert completed.stderr == b"stderr"
    assert completed.stdout == f"{tmp_path}\nselected-env\n{literal}\n".encode() + b"raw\x00\xff"
    assert (tmp_path / "made").read_text(encoding="utf-8") == "case-effect"
    assert (tmp_path / "made").stat().st_mode & 0o777 == 0o600
    assert not (tmp_path / "should-not-expand").exists()


# An inherited stdout fixture descriptor remains the candidate's observable output target.
def test_candidate_preserves_stdout_file_descriptor(candidate_probe: Path, tmp_path: Path) -> None:
    output = tmp_path / "stdout"
    with output.open("wb") as stream:
        completed = run_candidate(candidate_probe, ["output"], cwd=tmp_path, stdout=stream)

    assert completed.returncode == 0, completed.stderr
    assert output.read_bytes() == b"descriptor-output"


# Text-mode checked execution exposes the candidate's failure rather than changing its exit.
def test_candidate_preserves_checked_text_failure(candidate_probe: Path, tmp_path: Path) -> None:
    with pytest.raises(subprocess.CalledProcessError) as raised:
        run_candidate(candidate_probe, ["io", "argument"], cwd=tmp_path, text=True, check=True)

    assert raised.value.returncode == 7
    assert raised.value.stderr == "stderr"
    assert str(tmp_path) in raised.value.stdout


# A candidate timeout terminates the direct process and remains a subprocess timeout error.
def test_candidate_preserves_timeout(candidate_probe: Path, tmp_path: Path) -> None:
    with pytest.raises(subprocess.TimeoutExpired):
        run_candidate(candidate_probe, ["sleep"], cwd=tmp_path, timeout=0.5)


# Missing .NET tooling reports infrastructure failure before the program runs.
def test_candidate_reports_missing_dotnet(
    candidate_probe: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("PATH", "")
    with pytest.raises(CandidateInfrastructureError, match="requires dotnet"):
        run_candidate(candidate_probe, ["io", "unused"], cwd=tmp_path)

    assert not (tmp_path / "made").exists()


# A genuine SIGPIPE remains signal termination rather than the shell-compatible exit141.
def test_candidate_sigpipe_preserves_signal(candidate_probe: Path, tmp_path: Path) -> None:
    result = run_candidate(candidate_probe, ["sigpipe"], cwd=tmp_path)
    assert result.returncode == -13


# A normal exit141 remains a normal exit distinct from signal13.
def test_candidate_normal_exit141_remains_exit(candidate_probe: Path, tmp_path: Path) -> None:
    result = run_candidate(candidate_probe, ["exit141"], cwd=tmp_path)
    assert result.returncode == 141


# A genuine trusted-runtime exec failure raises its OS error rather than a candidate exit127.
def test_runtime_exec_error_is_preserved(
    candidate_probe: Path, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runtime = tmp_path / "runtime"
    runtime.mkdir()
    executable = runtime / "dotnet"
    executable.write_text("not executable", encoding="utf-8")
    executable.chmod(0o444)
    monkeypatch.setattr(candidate_execution.shutil, "which", lambda _: str(executable))
    case = tmp_path / "case"
    case.mkdir()
    with pytest.raises(PermissionError):
        run_candidate(candidate_probe, ["exit141"], cwd=case)
