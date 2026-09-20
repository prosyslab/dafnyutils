"""Check that modeled IO state is observable but not client-mutable."""

from __future__ import annotations

import os
import subprocess
import textwrap
from dataclasses import dataclass
from pathlib import Path

import pytest

from dafny_cli import dafny_command

ROOT = Path(__file__).resolve().parents[2]
IO_SOURCE = ROOT / "bench" / "core" / "IO.dfy"
VERIFY_FLAGS = (
    "--standard-libraries:false",
    "--allow-external-contracts",
    "--dont-verify-dependencies",
    "--cores:1",
    "--verification-time-limit:30",
)


@dataclass(frozen=True)
class ProbeCase:
    name: str
    body: str
    expected_returncode: int
    diagnostic: str


NEGATIVE_CASES = (
    ProbeCase(
        name="second_process_constructor",
        body="""
        module Probe {
          import B = BenchIO

          method Attack() {
            var secondary := new B.IO();
            secondary.AppendStdout("X");
          }
        }
        """,
        expected_returncode=2,
        diagnostic="does not have an anonymous constructor",
    ),
    ProbeCase(
        name="unreachable_process_initializer",
        body="""
        module Probe {
          import B = BenchIO

          method Attack() {
            var secondary := new B.IO.Init();
          }
        }
        """,
        expected_returncode=4,
        diagnostic="a precondition for this call could not be proved",
    ),
    ProbeCase(
        name="reaccessed_process_unframed_write",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(primary: B.IO)
            requires primary == B.Process()
            ensures primary.stdout() == old(primary.stdout())
          {
            var secondary := B.Process();
            secondary.AppendStdout("X");
          }
        }
        """,
        expected_returncode=4,
        diagnostic="modified object in call could not be proved",
    ),
    ProbeCase(
        name="reaccessed_process_unframed_stream_write",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(primary: B.IO)
            requires primary == B.Process()
            ensures primary.stdout() == old(primary.stdout())
          {
            var secondary := B.Process();
            var committed, err := secondary.WriteStdoutWithOutcome("X");
          }
        }
        """,
        expected_returncode=4,
        diagnostic="modified object in call could not be proved",
    ),
    ProbeCase(
        name="reaccessed_process_hidden_output",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(primary: B.IO)
            requires primary == B.Process()
            modifies primary.stdoutRegion
            ensures primary.stdout() == old(primary.stdout())
          {
            var secondary := B.Process();
            secondary.AppendStdout("X");
          }
        }
        """,
        expected_returncode=4,
        diagnostic="a postcondition could not be proved",
    ),
    ProbeCase(
        name="process_region_freshness",
        body="""
        module Probe {
          import B = BenchIO

          method Attack() {
            var secondary := B.Process();
            assert fresh(secondary.stdoutRegion);
          }
        }
        """,
        expected_returncode=4,
        diagnostic="assertion could not be proved",
    ),
    ProbeCase(
        name="forged_stream_region_capability",
        body="""
        module Probe {
          import B = BenchIO

          method Attack()
          {
            var region := 42 as B.TrustedStreamsRegion;
          }
        }
        """,
        expected_returncode=2,
        diagnostic="must be from an expression of a compatible type",
    ),
    ProbeCase(
        name="trusted_stream_region_value_write",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(io: B.IO)
            modifies io.trustedStreamsRegion
          {
            io.trustedStreamsRegion.value := io.trustedStreams();
          }
        }
        """,
        expected_returncode=2,
        diagnostic="member 'value' has not been imported",
    ),
    ProbeCase(
        name="stream_region_reference_replacement",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(io: B.IO, other: B.IO)
          {
            io.trustedStreamsRegion := other.trustedStreamsRegion;
          }
        }
        """,
        expected_returncode=2,
        diagnostic="LHS of assignment must denote a mutable field",
    ),
    ProbeCase(
        name="legacy_field_write",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(io: B.IO)
          {
            io.stdout := [];
          }
        }
        """,
        expected_returncode=2,
        diagnostic="LHS of assignment must denote a mutable field",
    ),
    ProbeCase(
        name="observer_write",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(io: B.IO)
          {
            io.stdout() := [];
          }
        }
        """,
        expected_returncode=2,
        diagnostic="LHS of assignment must denote a mutable variable or field",
    ),
    ProbeCase(
        name="region_value_write",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(io: B.IO)
            modifies io.stdoutRegion
          {
            io.stdoutRegion.value := [];
          }
        }
        """,
        expected_returncode=2,
        diagnostic="member 'value' has not been imported",
    ),
    ProbeCase(
        name="aliased_region_value_write",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(io: B.IO)
            modifies io.stdoutRegion
          {
            var region := io.stdoutRegion;
            region.value := [];
          }
        }
        """,
        expected_returncode=2,
        diagnostic="member 'value' has not been imported",
    ),
    ProbeCase(
        name="region_reference_replacement",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(io: B.IO, other: B.IO)
          {
            io.stdoutRegion := other.stdoutRegion;
          }
        }
        """,
        expected_returncode=2,
        diagnostic="LHS of assignment must denote a mutable field",
    ),
    ProbeCase(
        name="forged_postcondition",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(io: B.IO)
            modifies io.stdoutRegion
            ensures io.stdout() == old(io.stdout()) + "forged"
          {
          }
        }
        """,
        expected_returncode=4,
        diagnostic="a postcondition could not be proved",
    ),
    ProbeCase(
        name="wrong_region_permission",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(io: B.IO)
            modifies io.stdoutRegion
          {
            var data := io.ReadStdinAll();
          }
        }
        """,
        expected_returncode=4,
        diagnostic="modified object in call could not be proved",
    ),
    ProbeCase(
        name="cross_region_alias",
        body="""
        module Probe {
          import B = BenchIO

          method Attack(io: B.IO)
          {
            var region: B.StdoutRegion := io.fsRegion;
          }
        }
        """,
        expected_returncode=2,
        diagnostic="not assignable to LHS",
    ),
    ProbeCase(
        name="private_region_constructor",
        body="""
        module Probe {
          import B = BenchIO

          method Attack()
          {
            ghost var region := new B.StdoutRegion.Init([]);
          }
        }
        """,
        expected_returncode=2,
        diagnostic="member 'Init' has not been imported",
    ),
    ProbeCase(
        name="undeclared_internal_export",
        body="""
        module Probe {
          import B = BenchIO`Internal
        }
        """,
        expected_returncode=2,
        diagnostic="no export set 'Internal'",
    ),
    ProbeCase(
        name="refinement_original_handle",
        body="""
        module Refined refines BenchIO {
          import Original = BenchIO

          method Attack(io: Original.IO)
            modifies io.stdoutRegion
          {
            io.stdoutRegion.value := [];
          }
        }
        """,
        expected_returncode=2,
        diagnostic="member 'value' has not been imported",
    ),
    ProbeCase(
        name="refinement_copy_interop",
        body="""
        module Refined refines BenchIO {
          export Exploit extends BenchIO
            provides AttackCopy

          method AttackCopy(io: IO)
            modifies io.stdoutRegion
          {
            io.stdoutRegion.value := [];
          }
        }

        module Probe {
          import Original = BenchIO
          import Copy = Refined`Exploit

          method Attack(io: Original.IO)
            modifies io.stdoutRegion
          {
            Copy.AttackCopy(io);
          }
        }
        """,
        expected_returncode=2,
        diagnostic="incorrect argument type",
    ),
)


def _source(body: str) -> str:
    return f'include "{IO_SOURCE.as_posix()}"\n\n{textwrap.dedent(body).strip()}\n'


def _verify(tmp_path: Path, name: str, body: str) -> subprocess.CompletedProcess[str]:
    source = tmp_path / f"{name}.dfy"
    source.write_text(_source(body), encoding="utf-8")
    env = os.environ.copy()
    env["TMPDIR"] = "/tmp"
    env.setdefault("DOTNET_ROOT", "/usr/share/dotnet")
    env.setdefault("DOTNET_GCHeapHardLimit", hex(10 * 1024 * 1024 * 1024))
    env.setdefault("COMPlus_GCHeapHardLimit", env["DOTNET_GCHeapHardLimit"])
    return subprocess.run(
        [dafny_command(), "verify", str(source), *VERIFY_FLAGS],
        cwd=tmp_path,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=60,
        check=False,
    )


# Each prohibited access route must fail for its expected compiler/verifier reason.
@pytest.mark.parametrize("case", NEGATIVE_CASES, ids=lambda case: case.name)
def test_io_state_mutation_is_rejected(tmp_path: Path, case: ProbeCase) -> None:
    completed = _verify(tmp_path, case.name, case.body)

    assert completed.returncode == case.expected_returncode, completed.stdout
    assert case.diagnostic in completed.stdout


# Reaccessing the process shares every region and accounts for output in the same frame.
def test_process_reaccess_preserves_identity_and_tracks_output(tmp_path: Path) -> None:
    completed = _verify(
        tmp_path,
        "process_reaccess",
        """
        module Probe {
          import B = BenchIO

          method Append(primary: B.IO, data: B.BenchWorld.Bytes)
            requires primary == B.Process()
            modifies primary.stdoutRegion
            ensures primary.stdout() == old(primary.stdout()) + data
          {
            var secondary := B.Process();
            assert primary == secondary;
            assert primary.Footprint() == secondary.Footprint();
            secondary.AppendStdout(data);
          }
        }
        """,
    )

    assert completed.returncode == 0, completed.stdout
    assert "0 errors" in completed.stdout


# The stdout capability updates stdout while disjoint region frames preserve stdin and fs.
def test_append_stdout_preserves_disjoint_state(tmp_path: Path) -> None:
    completed = _verify(
        tmp_path,
        "append_stdout",
        """
        module Probe {
          import B = BenchIO

          method Append(io: B.IO, data: B.BenchWorld.Bytes)
            modifies io.stdoutRegion
            ensures io.stdout() == old(io.stdout()) + data
            ensures io.stdin() == old(io.stdin())
            ensures io.fs() == old(io.fs())
          {
            io.AppendStdout(data);
          }
        }
        """,
    )

    assert completed.returncode == 0, completed.stdout
    assert "0 errors" in completed.stdout


# The stdin capability returns and consumes stdin while preserving stdout and fs.
def test_read_stdin_preserves_disjoint_state(tmp_path: Path) -> None:
    completed = _verify(
        tmp_path,
        "read_stdin",
        """
        module Probe {
          import B = BenchIO

          method Read(io: B.IO) returns (data: B.BenchWorld.Bytes)
            modifies io.stdinRegion
            ensures data == old(io.stdin())
            ensures io.stdin() == []
            ensures io.stdout() == old(io.stdout())
            ensures io.fs() == old(io.fs())
          {
            data := io.ReadStdinAll();
          }
        }
        """,
    )

    assert completed.returncode == 0, completed.stdout
    assert "0 errors" in completed.stdout


# Distinct concrete region types imply distinct heap objects for separate IO components.
def test_region_types_are_disjoint(tmp_path: Path) -> None:
    completed = _verify(
        tmp_path,
        "region_disjointness",
        """
        module Probe {
          import B = BenchIO

          lemma Distinct(io: B.IO)
            ensures (io.stdoutRegion as object) != (io.stdinRegion as object)
          {
          }
        }
        """,
    )

    assert completed.returncode == 0, completed.stdout
    assert "0 errors" in completed.stdout
