# truncate

The contribution targets GNU coreutils `truncate` at commit
`2cf491412c199e2211880ec3f4ba387026638a33` (`coreutils/src/truncate.c`), licensed
GPL-3.0-or-later. It is repository maintenance, not an evaluated candidate run.

The minimum prepared input is explicit `-c -s N`, with decimal absolute sizes
from zero through `9223372036854775807`, stable regular files and symlinks,
directory rejection, and missing paths. Review of the pinned source and
`bench/core/IO.dfy` also admits ordinary creation, reference-file sizes, all six
relative modifiers, GNU size suffixes, `--io-blocks`, long options and
abbreviations, GNU option permutation, `--`, help/version, and option failures.
These behaviors are included. Regular-file hard-link aliases, dangling symlinks,
repeated operands, continuing after operand failures, and argument quoting are
observable parts of the scope.

The environment is Linux with 64-bit `off_t`, C locale, UTC0, `TERM=dumb`,
`NO_COLOR=1`, GNU option permutation (`POSIXLY_CORRECT` unset), captured stdout/stderr
(or the deterministic `/dev/full` stdout-failure cases), and stable finite local
files, the evaluator's ordinary non-root credentials and controlled umask.
Observations are exact stdout/stderr bytes, exact status, and the modeled
filesystem after each operand, including creation or successful earlier operands
retained when a later operation fails. The signed-64 upper bound is accepted by
the parser; an actual filesystem may reject that length. Tests must not allocate
or read enormous sparse payloads.

`CreateFile` provides open-for-writing with creation and no content truncation;
`PathExists` supports no-create filtering; `GetFileStatus` supplies ordinary
regular-file sizes and preferred IO block sizes; `TruncateFile` resizes without
creation. Every effect remains linked to the IO handle's fixed trusted
filesystem observations and its per-operation validity predicate. Metadata
observations use the IO status cursor. The utility itself owns parsing, relative
size arithmetic, diagnostics, iteration, and exit policy.

GNU descriptor-specific injected faults, concurrent path replacement, devices,
FIFOs, sockets, and nonregular reference seeking are outside the existing API:
there is no descriptor open/fstat/lseek/ftruncate/close interface. In particular,
path-based metadata cannot reproduce a descriptor retained across a rename, and
`CreateFile` combines open and close into one result. Ordinary directory, missing
path, symlink-loop, access-control, and size-limit failures remain in scope.
Overlong reference pathnames are excluded because `GetFileStatus` maps native
`ENAMETOOLONG` to `ENOENT`; the IO documentation records that limitation.
Signal delivery and externally closed output pipes are excluded because the IO
interface represents returned errno outcomes rather than process signals.
The current `CreateFile` contract ties the complete resulting filesystem to a
fixed native observation but does not mathematically constrain fresh-file mode
and ownership from umask/credentials. Runtime cases compare both fields.
Creation modes/owners remain within the
existing approved native-observation trust boundary; no independent algebraic
mode/owner proof is claimed. No stronger native postcondition or assumption has
been introduced here.
No GNU command-line option is omitted because of `IO.dfy`; only the listed
filesystem and fault environments are omitted.

Source evidence includes `coreutils/src/truncate.c`, `coreutils/src/system.h`
(`usable_st_size`), `coreutils/gnulib/lib/xstrtol.c`,
`coreutils/gnulib/lib/stat-size.h`, and `coreutils/tests/truncate/`.
Native syntax probes and subsequent validation evidence are kept outside the
repository at `/workspace/tmp/fs-benchmarks-20261020/evidence/truncate/` and are
available in the current maintenance workspace. The native probe session is
`truncate-source-20261020`.

For example, in a directory without `missing`, exit status is 0:

```sh
truncate -c -s 3 missing
```

```text
(no stdout or stderr; no file is created)
```

An invalid size exits with status 1 before changing files:

```sh
truncate --size=invalid file
```

```text
truncate: Invalid number: 'invalid'
```

## Design and evidence

`TruncateSpec.dfy` defines the decimal value, the last active modifier, the first
size/configuration error, and the ordered filesystem transition relation.
Existential intermediate states constrain each operand and accumulated diagnostic;
failed operands retain earlier effects. `TruncateCore.dfy` contains the parser,
size arithmetic and IO iteration. `RunCore` directly ensures `Spec.Spec`.
`TruncateProof.dfy` supplies mathematical witness lemmas. Its opaque relations
retain their bodies and are explicitly revealed by ordinary verified proofs.
The CLI entry selects an invalid short-option character with a terminating loop
and proves `UnknownShortRelation`, a finite-index relation identifying the first
character outside `c`/`o`. Spec formats the diagnostic from that explicit
character; it does not execute a recursive option scan.
There are no new native calls, assumptions, trust annotations, verification skips,
or increased verification limits in this utility.

The new `Tests.py` is an evaluator-owned GNU differential oracle/scoring fixture,
selected by `make test TASK=truncate`; it is not in the development suite selected
by `pytest-dev.ini`. Each side uses the equivalent bounded tree: two directories,
four small regular files, three symbolic links and one hard-link alias. Snapshots
compare exact bytes, kinds, modes, uid/gid, link counts and alias identities;
timestamps follow the existing evaluator policy. Parser boundary cases use
`-c` with missing operands and cannot produce huge sparse files. Snapshot reads
reject a regular payload above 16384 bytes. No Python development test was added.

The registered Rust generator uses `PatternInputGenerator` and regenerates the
filesystem case when arguments mutate. Its 52 fixed cases cover GNU syntax,
creation and no-create, references, block units, aliases, quoting, failures and
ordered partial progress. Generated successful operation sizes stay small;
signed-64 parser boundaries target missing files or arithmetic failures before
resize.

Native status requests now bind both timestamp observations and native failure
observations at the exact request ordinal. Diagnostic and help writes retain
their committed prefixes and explicit errors; empty diagnostic output does
not issue a native write. A failed help write or diagnostic write contributes
to the final nonzero exit status.

The following validation is historical: it describes the earlier filesystem
implementation, not the later native-failure contract changes. Current failure
semantics and model limits are described in
[the API model limits](../../../docs/core-api.md#trust-limits-and-api-changes).

Historical validation used `/workspace/tmp/fs-benchmarks-20261020/integration`,
with `PYTHONPATH="$PWD/src:$PWD"`, based on
`1ed3144e6b092f50ce99b0450d242a43309e1bd4` plus this maintenance change.

- `make check TASK=truncate` passes on unchanged before/after source manifests:
  compilation, 92 strict GNU oracle cases, the mandatory 20-case campaign,
  canonical verification of all 34 declarations and 605 obligations, and all
  four marked Spec/Core/Proof/Entry module checks. Proofs retain seed 42,
  included-file verification, isolated assertions, the 30-second VC limit and
  the 100-second declaration limit.
- `python3 tools/coreutils_fuzzer/run.py fuzz truncate --seeds 1,7,19 --iterations 1000`
  completes all 3,000 requested cases with exact output, status and filesystem
  comparison: zero mismatches, timeouts or other errors. The executable was
  frozen before the campaign and the source manifests remain unchanged.
- The saved quoting mismatch at
  `/tmp/coreutils-fuzzer-repros/truncate-seed1-iter476` now replays as comparator
  Match. The replay command returns raw exit 2 with
  `FUZZER_OUTCOME=replay_not_reproduced` because the saved failure did not recur;
  a separate checked status records the successful comparison.
- The diagnostic refactor also matches 24 bounded GNU CLI probes covering
  clustered options, multibyte invalid characters, missing values and
  help/version precedence. Every affected declaration passes focused canonical
  verification; these overlapping counts are not added to the utility total.

Current-workspace evidence is outside public task resources under
`/workspace/tmp/fs-benchmarks-20261020/evidence/`:
`final-gates-approved-v1/` contains the complete contribution gate and unchanged
source manifests for the approved nonnegative `ReadDirContractFields` error
domain;
`runtime-boundary-final/truncate/` contains the rebuilt strict oracles, exact
replay, three campaigns, metrics, frozen DUT and source manifests;
`truncate/spec-boundary/` records the focused refactor checks. The runtime
coordinator's aggregate status is nonzero because its separate cp campaign
failed; truncate's own build/oracle/fuzz statuses are all zero. Earlier failed,
empty-target or superseded checks remain recorded externally and are not
passing evidence for this source. `core-approved-closure-v5/` separately records
598 shared declarations and 3640 conditions with zero failures. The 3,000-case
campaign predates the approved ghost contract refinement; utility execution,
native IO, generators and the comparator are unchanged. The final supported
gate rebuilds and reruns the strict oracles and its short campaign.

Tools are Dafny 4.11.1+10dca3ba4a2909c11299176440401fc31413b53d, pinned Z3 4.16.0,
.NET SDK 8.0.131, Python 3.12.3, pytest 9.1.1, Rust/Cargo 1.94.0 and Ruff 0.15.12.
The fuzzer uses `dafnyutils-coreutils-fuzzer:latest`, image
`sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76`,
uid/gid 1000, a 10-second case timeout, at most 10 arguments and 12 filesystem
entries, and 250 shrink attempts. Build/oracle/fuzz success is separate from
Dafny proof success. Shared-core, public-profile and development-suite checks
are recorded separately for the combined contribution.
