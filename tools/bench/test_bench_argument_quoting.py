"""Compare argument quoting with pinned gnulib; requires `make build-coreutils`."""

from __future__ import annotations

import os
import subprocess
from dataclasses import dataclass
from pathlib import Path

import pytest

from dafny_cli import dafny_command
from evaluation.submission.candidate_execution import run_candidate

ROOT = Path(__file__).resolve().parents[2]


@dataclass(frozen=True)
class QuotePrograms:
    reference: Path
    candidate: Path


# Compile both boundaries once; the reference calls the pinned gnulib quote_mem directly.
@pytest.fixture(scope="module")
def quote_programs(tmp_path_factory: pytest.TempPathFactory) -> QuotePrograms:
    build = tmp_path_factory.mktemp("argument-quoting-build")
    reference_source = build / "quote-reference.c"
    reference_source.write_text(
        """#include <config.h>
#include <stdio.h>
#include <stdlib.h>
#include "quote.h"

int main(void) {
  char input[4096];
  size_t count = fread(input, 1, sizeof input, stdin);
  if (ferror(stdin) || count == sizeof input) return 2;
  return fputs(quote_mem(input, count), stdout) < 0 ? 3 : 0;
}
""",
        encoding="utf-8",
    )
    reference = build / "quote-reference"
    subprocess.run(
        [
            "cc",
            "-I",
            str(ROOT / "_build/coreutils/lib"),
            "-I",
            str(ROOT / "coreutils/lib"),
            str(reference_source),
            str(ROOT / "_build/coreutils/lib/libcoreutils.a"),
            "-o",
            str(reference),
        ],
        check=True,
        capture_output=True,
        timeout=60,
    )
    source = build / "QuoteProbe.dfy"
    source.write_text(
        f"""include "{ROOT / "bench/core/IO.dfy"}"

module QuoteProbe {{
  import BenchIO
  import BW = BenchWorld

  method Quote(io: BenchIO.IO, data: BW.Bytes) returns (quoted: BW.Bytes)
    ensures quoted == BenchIO.QuoteArgumentResult(data)
  {{
    quoted := io.QuoteArgument(data);
  }}

  method {{:main}} Main()
    modifies BenchIO.Process().stdinRegion, BenchIO.Process().stdoutRegion
  {{
    var io := BenchIO.Process();
    var data, readErr := io.ReadStdinWithOutcome();
    var quoted := Quote(io, data);
    var committed, writeErr := io.WriteStdoutWithOutcome(quoted);
    BenchIO.Exit(if readErr == 0 && writeErr == 0 then 0 else 1);
  }}
}}
""",
        encoding="utf-8",
    )
    candidate = build / "QuoteProbe.dll"
    completed = subprocess.run(
        [
            dafny_command(),
            "build",
            "--standard-libraries:false",
            "--target:cs",
            "--output",
            str(candidate),
            str(source),
            str(ROOT / "bench/core/IOExtern.cs"),
        ],
        cwd=build,
        env={**os.environ, "TMPDIR": "/tmp"},
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=120,
        check=False,
    )
    assert completed.returncode == 0, completed.stdout
    return QuotePrograms(reference, candidate)


# Argument diagnostics must preserve gnulib's C-locale quoting for each input class.
@pytest.mark.parametrize(
    "payload",
    [
        pytest.param(b"", id="empty-argument"),
        pytest.param(b"invalid value", id="spaces"),
        pytest.param(b"can't\\\"", id="quotes-and-backslash"),
        pytest.param(bytes(range(256)), id="every-byte"),
        pytest.param(b"\0" + b"0\0" + b"7\0" + b"8\0" + b"9\0x", id="nul-digit-boundary"),
        pytest.param("잘못된 값".encode(), id="utf8-argument"),
    ],
)
def test_argument_quote_matches_gnulib(
    quote_programs: QuotePrograms,
    tmp_path: Path,
    payload: bytes,
) -> None:
    # upstream: none - repository-owned diagnostic primitive conformance
    reference = subprocess.run(
        [str(quote_programs.reference)],
        input=payload,
        capture_output=True,
        env={**os.environ, "LC_ALL": "C", "LANG": "C"},
        check=True,
        timeout=10,
    )
    candidate = run_candidate(
        quote_programs.candidate,
        [],
        cwd=tmp_path,
        input=payload,
        timeout=30,
    )
    assert candidate.returncode == 0, candidate.stderr
    assert candidate.stderr == b""
    assert candidate.stdout == reference.stdout
