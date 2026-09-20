"""Verification coverage for the shared stdlib-off functional support module."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

from dafny_cli import dafny_command

ROOT = Path(__file__).resolve().parents[2]
FUNCTIONAL = ROOT / "bench" / "core" / "Functional.dfy"


# A candidate can include and use BenchFunctional while packaged libraries stay disabled.
def test_functional_core_resolves_and_verifies_without_standard_libraries(tmp_path: Path) -> None:
    # upstream: none - repository-local Dafny verification check
    source = tmp_path / "FunctionalSmoke.dfy"
    source.write_text(
        f'''include "{FUNCTIONAL.as_posix()}"

module FunctionalSmoke {{
  import Functional = BenchFunctional

  function Increment(value: int): int {{ value + 1 }}

  lemma MapContractIsUsable()
  {{
    var mapped := Functional.Map(Increment, [1, 2]);
    assert |mapped| == 2;
    assert mapped[0] == 2;
    assert mapped[1] == 3;
  }}
}}
''',
        encoding="utf-8",
    )

    completed = subprocess.run(
        [dafny_command(), "verify", "--standard-libraries:false", str(source)],
        cwd=ROOT,
        env={**os.environ, "TMPDIR": "/tmp"},
        check=False,
        capture_output=True,
        text=True,
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
