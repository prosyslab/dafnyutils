# pathchk NL Specification

Source:

- `coreutils/doc/coreutils.texi`, `@node pathchk invocation`, lines 14141-14212.
- `coreutils/src/pathchk.c` at submodule commit
  `2cf491412c199e2211880ec3f4ba387026638a33`; GPL-3.0-or-later.
- Upstream tests: `coreutils/tests/misc/pathchk.sh` and
  `coreutils/tests/help/help-version.sh`.

## `pathchk`: Check file name validity and portability

`pathchk` checks names without creating files. A nonexistent name is not itself
an error.

```text
pathchk [OPTION]... NAME...
```

- `-p`: require a nonempty name containing only ASCII letters, digits, `.`, `_`,
  `-` and `/`, within the POSIX portability limits.
- `--portability`: equivalent to `-p -P`; also reject a component beginning with
  `-`. For example, `foo/-bar` passes `-p` but fails `--portability`.
- `--help`, `--version`: print information and exit.

Options must precede names. In `pathchk -p foo --help`, `--help` is a name;
`pathchk -p --help foo` displays help. `--` explicitly ends option processing.

### Benchmark-Supported Behavior

The benchmark supports `-p`, `--portability`, combinations of `-p` with `-P`,
GNU long-option abbreviations, short-option bundles, help/version, and
option/operand errors.
Names are NUL-free strings encoded as UTF-8; diagnostics use the C locale.

Limits are 255 bytes for the whole name, excluding its terminating NUL, and
14 bytes per component. Components are nonempty runs between `/` separators;
repeated or trailing slashes do not create empty components.

Each name produces at most one diagnostic, in this priority order:

1. Component-leading `-`, when `-P` is enabled.
2. Empty name.
3. First byte outside the portable alphabet.
4. Excessive total byte length.
5. First component exceeding its byte limit.

Every operand is checked in order, even after a failure. Valid names produce no
output; invalid names produce the GNU diagnostic on stderr.

[Issue #17](https://github.com/prosyslab/dafnyutils/issues/17) explicitly excludes
the default host-dependent mode and `-P` alone. These require host `pathconf`
limits and directory-searchability checks outside this contribution. The formal
guarantee is conditional on `AllowedInput`; the executable currently returns 1
without a diagnostic for these excluded normal modes.

### Scope and model

- Observation: exact stdout/stderr bytes, diagnostic order and exit status.
  The entry modifies only stdout/stderr, preserving the filesystem and stdin.
  Partial writes follow the shared contracts; reported write failures return 1.
- Trusted boundary: shared CLI parsing, UTF-8, quoting, C-locale errno text and
  `WriteStdoutSpec`/`WriteStderrSpec` in `bench/core` at upstream revision
  `55110e9`. Decimal rendering reuses the `wc` implementation and proof.
- Proof: `Pathchk.PathchkBenchmarkItem.RunCore` directly ensures
  `PathchkSpec.Spec`. Relations specify valid names, ordered diagnostics and
  output effects. Core loops terminate on finite input; whole-process
  termination is not proved because the shared CLI and `PlanParseFailure` use
  `decreases *`. Native extern implementations remain trusted.
- Known limitation: reporting errors for 100,000-byte names matched GNU but
  took about 14 seconds locally, exceeding the usual 10-second fuzz-process
  budget. Long-name performance remains unresolved.

### Validation evidence

Recorded with uncommitted work on `53107aa`, upstream base `55110e9`, and Dafny
`4.11.1+0776df27c2449bad68e9a28e687bb6c70bf4b401` in the development container.

- Before the latest generator changes: build passed; 49 runtime tests and
  5 proof tests passed; `make -C bench/utils/pathchk verify` reported
  `5230 verified, 0 errors`; `python3 -m tools.contribution check pathchk`
  exited 0. Verification includes project sources and non-library dependencies,
  including reused `wc` code; `bench/core` is the trusted library.
- Those runtime cases compare stdout, stderr and exit status, including
  `--help` output failure through `/dev/full`.
- Earlier fuzz campaigns: seeds 1, 7 and 19 each completed 1,000 matches with
  no mismatches, timeouts or other errors.
- Latest generator: two focused Rust tests and a 100-case GNU campaign (seed 7)
  passed, with no mismatches, timeouts or other errors. Full PR campaigns have
  not been rerun after the generator changes.

Detailed commands and logs are container-local under
`/workspace/tmp/pathchk-final-20261106/`,
`/workspace/tmp/pathchk-pr-review-20261106/` and
`/workspace/tmp/pathchk-random-names-20261107/`; they may be unavailable after
container removal.

### Exit Status

The supported command returns 0 when all names pass or help/version succeeds.
Invalid names, option/operand errors and reported output failures return 1.
