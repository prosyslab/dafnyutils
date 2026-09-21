"""Exercise the native boundary for the shared stream and filesystem models."""

from __future__ import annotations

import os
import stat
import subprocess
import textwrap
from pathlib import Path

import pytest

from dafny_cli import dafny_command
from evaluation.submission.candidate_execution import run_candidate

ROOT = Path(__file__).resolve().parents[2]
IO_SOURCE = ROOT / "bench" / "core" / "IO.dfy"
IO_EXTERN = ROOT / "bench" / "core" / "IOExtern.cs"

PROBE_SOURCE = f"""
include "{IO_SOURCE.as_posix()}"

module StreamFilesystemProbe {{
  import BenchIO
  import BW = BenchWorld

  method Finish(ok: bool, err: int)
  {{
    if ok && err == 0 {{
      BenchIO.Exit(0);
    }} else {{
      BenchIO.Exit(10);
    }}
  }}

  method {{:main}} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {{
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    if |effectiveArgs| != 1 &&
       !(|effectiveArgs| == 2 && effectiveArgs[0] == "mkdir") {{
      BenchIO.Exit(90);
      return;
    }}

    var io := BenchIO.Process();
    var operation := effectiveArgs[0];
    if operation == "read-file" {{
      var data, err := io.ReadFileWithOutcome("input");
      io.AppendStdout(data);
      Finish(err == 0, err);
    }} else if operation == "read-empty-path" {{
      var data, err := io.ReadFileWithOutcome("");
      if data == [] && err != 0 {{
        BenchIO.Exit(0);
      }} else {{
        BenchIO.Exit(10);
      }}
    }} else if operation == "read-stdin" {{
      var data, err := io.ReadStdinWithOutcome();
      var committed, writeErr := io.WriteStdoutWithOutcome(data);
      Finish(err == 0 && writeErr == 0 && committed == |data|, err + writeErr);
    }} else if operation == "write-stdout" {{
      var committed, err := io.WriteStdoutWithOutcome("stream-output");
      Finish(committed == |"stream-output"| && err == 0, err);
    }} else if operation == "write-stdout-error" {{
      var committed, err := io.WriteStdoutWithOutcome("stream-output");
      if committed < |"stream-output"| && err != 0 {{
        BenchIO.Exit(0);
      }} else {{
        BenchIO.Exit(10);
      }}
    }} else if operation == "write-stderr" {{
      var committed, err := io.WriteStderrWithOutcome("stream-error");
      Finish(committed == |"stream-error"| && err == 0, err);
    }} else if operation == "mkdir" {{
      var path := if |effectiveArgs| == 2 then effectiveArgs[1] else "made";
      var ok, err := io.CreateDirectory(path, 0x1e8 as bv32);
      Finish(ok, err);
    }} else if operation == "rmdir" {{
      var ok, err := io.RemoveDirectory("empty");
      Finish(ok, err);
    }} else if operation == "rmdir-nonempty" {{
      var ok, err := io.RemoveDirectory("nonempty");
      if !ok && err != 0 {{
        BenchIO.Exit(0);
      }} else {{
        BenchIO.Exit(10);
      }}
    }} else if operation == "hardlink" {{
      var ok, err := io.CreateHardLink("source", "hard");
      Finish(ok, err);
    }} else if operation == "unlink" {{
      var ok, err := io.UnlinkPath("victim");
      Finish(ok, err);
    }} else if operation == "unlink-directory" {{
      var ok, err := io.UnlinkPath("directory");
      if !ok && err != 0 {{
        BenchIO.Exit(0);
      }} else {{
        BenchIO.Exit(10);
      }}
    }} else if operation == "truncate" {{
      var ok, err := io.TruncateFile("source", 3);
      Finish(ok, err);
    }} else if operation == "fifo" {{
      var ok, err := io.CreateSpecialNode("pipe", BW.FifoNode, 0x180 as bv32, 0, 0);
      Finish(ok, err);
    }} else if operation == "sync" {{
      var ok, err := io.Sync(BW.PathSyncTarget("source"), BW.SyncDataAndMetadata);
      Finish(ok, err);
    }} else {{
      BenchIO.Exit(91);
    }}
  }}
}}
"""


def _build_probe(build_dir: Path) -> Path:
    source = build_dir / "StreamFilesystemProbe.dfy"
    output = build_dir / "stream_filesystem_probe.dll"
    source.write_text(textwrap.dedent(PROBE_SOURCE).strip() + "\n", encoding="utf-8")
    env = os.environ.copy()
    env["TMPDIR"] = "/tmp"
    env.setdefault("DOTNET_ROOT", "/usr/share/dotnet")
    env.setdefault("NUGET_PACKAGES", "/home/vscode/.nuget/packages")
    env.setdefault("RestoreSources", env["NUGET_PACKAGES"])
    env.setdefault("RestoreIgnoreFailedSources", "true")
    completed = subprocess.run(
        [
            dafny_command(),
            "build",
            "--no-verify",
            "--target:cs",
            "--output",
            str(output),
            str(source),
            str(IO_EXTERN),
        ],
        cwd=build_dir,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=120,
        check=False,
    )
    assert completed.returncode == 0, completed.stdout
    return output


# The shared probe is compiled once so each test isolates one observable syscall scenario.
@pytest.fixture(scope="session")
def stream_filesystem_probe(tmp_path_factory: pytest.TempPathFactory) -> Path:
    return _build_probe(tmp_path_factory.mktemp("stream-filesystem-probe"))


def _run_probe(
    probe: Path,
    operation: str,
    cwd: Path,
    *,
    input_data: bytes = b"",
    directory_path: str | None = None,
) -> subprocess.CompletedProcess[bytes]:
    return run_candidate(
        probe,
        [operation] if directory_path is None else [operation, directory_path],
        cwd=cwd,
        input=input_data,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
        check=False,
    )


# A successful trusted file read returns the complete raw byte stream and zero errno.
def test_read_file_with_outcome_returns_bytes(
    stream_filesystem_probe: Path, tmp_path: Path
) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    (tmp_path / "input").write_bytes(b"a\x00b\xff")

    completed = _run_probe(stream_filesystem_probe, "read-file", tmp_path)

    assert completed.returncode == 0, completed.stderr
    assert completed.stdout == b"a\x00b\xff"


# A failed trusted file read retains an empty prefix and reports a nonzero errno.
def test_read_file_with_outcome_reports_missing_file(
    stream_filesystem_probe: Path, tmp_path: Path
) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    completed = _run_probe(stream_filesystem_probe, "read-file", tmp_path)

    assert completed.returncode == 10
    assert completed.stdout == b""


# An empty public path is rejected before reaching the native ABI.
def test_read_file_with_outcome_rejects_empty_path(
    stream_filesystem_probe: Path, tmp_path: Path
) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    completed = _run_probe(stream_filesystem_probe, "read-empty-path", tmp_path)

    assert completed.returncode == 0, completed.stderr
    assert completed.stdout == b""


# The trusted stdin read consumes and reproduces all raw bytes on success.
def test_read_stdin_with_outcome_consumes_raw_bytes(
    stream_filesystem_probe: Path, tmp_path: Path
) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    completed = _run_probe(
        stream_filesystem_probe,
        "read-stdin",
        tmp_path,
        input_data=b"stdin\x00\xff",
    )

    assert completed.returncode == 0, completed.stderr
    assert completed.stdout == b"stdin\x00\xff"


# A nonblocking stdin error retains bytes consumed before the terminal errno.
def test_read_stdin_with_outcome_preserves_partial_prefix(
    stream_filesystem_probe: Path, tmp_path: Path
) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    read_fd, write_fd = os.pipe()
    os.set_blocking(read_fd, False)
    os.write(write_fd, b"partial")
    try:
        with os.fdopen(read_fd, "rb", closefd=True) as read_stream:
            completed = run_candidate(
                stream_filesystem_probe,
                ["read-stdin"],
                cwd=tmp_path,
                stdin=read_stream,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=30,
                check=False,
            )
    finally:
        os.close(write_fd)

    assert completed.returncode == 10
    assert completed.stdout == b"partial"


# The trusted stdout write reports that its full requested prefix was committed.
def test_write_stdout_with_outcome_reports_committed_prefix(
    stream_filesystem_probe: Path, tmp_path: Path
) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    completed = _run_probe(stream_filesystem_probe, "write-stdout", tmp_path)

    assert completed.returncode == 0, completed.stderr
    assert completed.stdout == b"stream-output"


# A trusted stdout write reports a nonzero errno when the target cannot accept bytes.
def test_write_stdout_with_outcome_reports_output_error(
    stream_filesystem_probe: Path, tmp_path: Path
) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    with Path("/dev/full").open("wb") as full:
        completed = run_candidate(
            stream_filesystem_probe,
            ["write-stdout-error"],
            cwd=tmp_path,
            stdout=full,
            stderr=subprocess.PIPE,
            timeout=30,
            check=False,
        )

    assert completed.returncode == 0, completed.stderr


# The trusted stderr write reports and commits its complete requested prefix.
def test_write_stderr_with_outcome_reports_committed_prefix(
    stream_filesystem_probe: Path, tmp_path: Path
) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    completed = _run_probe(stream_filesystem_probe, "write-stderr", tmp_path)

    assert completed.returncode == 0
    assert completed.stdout == b""
    assert completed.stderr == b"stream-error"


# The directory effect creates one directory with the requested operation.
def test_create_directory_effect(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    completed = _run_probe(stream_filesystem_probe, "mkdir", tmp_path)

    assert completed.returncode == 0, completed.stderr
    assert (tmp_path / "made").is_dir()


# Trailing separators still create the named directory.
def test_create_directory_trailing_slash(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local directory contract regression
    completed = _run_probe(stream_filesystem_probe, "mkdir", tmp_path, directory_path="made///")

    assert completed.returncode == 0, completed.stderr
    assert (tmp_path / "made").is_dir()
    assert list((tmp_path / "made").iterdir()) == []


# A symlink in the parent path resolves before inserting the new directory.
def test_create_directory_symlink_parent(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local directory contract regression
    (tmp_path / "real").mkdir()
    (tmp_path / "alias").symlink_to("real", target_is_directory=True)
    os.utime(tmp_path / "alias", ns=(1_000_000_000, 1_000_000_000), follow_symlinks=False)
    link_before = (tmp_path / "alias").lstat()
    (tmp_path / "untouched").write_bytes(b"preserve me")
    before = (tmp_path / "untouched").stat()

    completed = _run_probe(stream_filesystem_probe, "mkdir", tmp_path, directory_path="alias/made/")

    assert completed.returncode == 0, completed.stderr
    assert (tmp_path / "real" / "made").is_dir()
    link_after = (tmp_path / "alias").lstat()
    assert (link_after.st_ino, link_after.st_mode, link_after.st_mtime_ns) == (
        link_before.st_ino,
        link_before.st_mode,
        link_before.st_mtime_ns,
    )
    assert (tmp_path / "alias").readlink() == Path("real")
    assert (tmp_path / "untouched").read_bytes() == b"preserve me"
    after = (tmp_path / "untouched").stat()
    assert (after.st_ino, after.st_mode, after.st_mtime_ns) == (
        before.st_ino,
        before.st_mode,
        before.st_mtime_ns,
    )


# Dot-dot must be resolved after a symlink rather than lexically normalized first.
def test_create_directory_symlink_dotdot(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local directory contract regression
    (tmp_path / "real" / "child").mkdir(parents=True)
    (tmp_path / "alias").symlink_to("real/child", target_is_directory=True)

    completed = _run_probe(
        stream_filesystem_probe, "mkdir", tmp_path, directory_path="alias/../made"
    )

    assert completed.returncode == 0, completed.stderr
    assert (tmp_path / "real" / "made").is_dir()
    assert not (tmp_path / "made").exists()


# Existing directories report failure without removing their contents.
def test_create_directory_existing_target(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local directory contract regression
    (tmp_path / "made").mkdir()
    (tmp_path / "made" / "keep").write_bytes(b"keep")

    completed = _run_probe(stream_filesystem_probe, "mkdir", tmp_path)

    assert completed.returncode == 10
    assert (tmp_path / "made" / "keep").read_bytes() == b"keep"


# A terminal symlink must not be followed to create its missing target.
def test_create_directory_terminal_symlink(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local directory contract regression
    (tmp_path / "made").symlink_to("missing", target_is_directory=True)

    completed = _run_probe(stream_filesystem_probe, "mkdir", tmp_path, directory_path="made/")

    assert completed.returncode == 10
    assert (tmp_path / "made").is_symlink()
    assert not (tmp_path / "missing").exists()


# A missing parent must not be created by the one-directory API.
def test_create_directory_missing_parent(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local directory contract regression
    completed = _run_probe(
        stream_filesystem_probe, "mkdir", tmp_path, directory_path="missing/made"
    )

    assert completed.returncode == 10
    assert not (tmp_path / "missing").exists()


# A regular file cannot serve as a directory parent.
def test_create_directory_file_parent(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local directory contract regression
    (tmp_path / "parent").write_bytes(b"keep")

    completed = _run_probe(stream_filesystem_probe, "mkdir", tmp_path, directory_path="parent/made")

    assert completed.returncode == 10
    assert (tmp_path / "parent").read_bytes() == b"keep"


# The directory removal effect removes one existing empty directory.
def test_remove_directory_effect(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    (tmp_path / "empty").mkdir()

    completed = _run_probe(stream_filesystem_probe, "rmdir", tmp_path)

    assert completed.returncode == 0, completed.stderr
    assert not (tmp_path / "empty").exists()


# The directory removal effect reports failure and preserves a nonempty directory.
def test_remove_nonempty_directory_reports_error(
    stream_filesystem_probe: Path, tmp_path: Path
) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    (tmp_path / "nonempty").mkdir()
    (tmp_path / "nonempty" / "child").write_bytes(b"occupied")

    completed = _run_probe(stream_filesystem_probe, "rmdir-nonempty", tmp_path)

    assert completed.returncode == 0, completed.stderr
    assert (tmp_path / "nonempty" / "child").read_bytes() == b"occupied"


# The hard-link effect creates a second directory entry for the same inode.
def test_create_hard_link_effect(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    (tmp_path / "source").write_bytes(b"linked")

    completed = _run_probe(stream_filesystem_probe, "hardlink", tmp_path)

    assert completed.returncode == 0, completed.stderr
    assert (tmp_path / "source").stat().st_ino == (tmp_path / "hard").stat().st_ino


# The exact unlink effect removes a non-directory entry.
def test_unlink_path_effect(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    (tmp_path / "victim").write_bytes(b"remove")

    completed = _run_probe(stream_filesystem_probe, "unlink", tmp_path)

    assert completed.returncode == 0, completed.stderr
    assert not (tmp_path / "victim").exists()


# Exact unlink rejects a directory instead of deriving success from a later lookup.
def test_unlink_path_rejects_directory(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    (tmp_path / "directory").mkdir()

    completed = _run_probe(stream_filesystem_probe, "unlink-directory", tmp_path)

    assert completed.returncode == 0, completed.stderr
    assert (tmp_path / "directory").is_dir()


# The truncate effect resizes a regular file without replacing its prefix.
def test_truncate_file_effect(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    (tmp_path / "source").write_bytes(b"abcdef")

    completed = _run_probe(stream_filesystem_probe, "truncate", tmp_path)

    assert completed.returncode == 0, completed.stderr
    assert (tmp_path / "source").read_bytes() == b"abc"


# The special-node effect creates a FIFO with the requested node kind.
def test_create_fifo_effect(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    completed = _run_probe(stream_filesystem_probe, "fifo", tmp_path)

    assert completed.returncode == 0, completed.stderr
    assert stat.S_ISFIFO((tmp_path / "pipe").stat().st_mode)


# The synchronization effect successfully flushes one regular-file target.
def test_sync_file_effect(stream_filesystem_probe: Path, tmp_path: Path) -> None:
    # upstream: none - repository-local stream and filesystem model regression
    (tmp_path / "source").write_bytes(b"sync")

    completed = _run_probe(stream_filesystem_probe, "sync", tmp_path)

    assert completed.returncode == 0, completed.stderr
