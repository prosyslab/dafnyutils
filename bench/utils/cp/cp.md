# cp

## Source and observable contract

GNU coreutils revision `2cf491412c199e2211880ec3f4ba387026638a33`
(version `9.10.13-2cf49`), primarily `src/cp.c`, `src/copy.c`,
`src/force-link.c`, `lib/backupfile.c`, and public `tests/cp` cases.
License: GPL-3.0-or-later.

The input environment is a finite, stable local Linux filesystem, C locale,
UTC0, Unicode argv without NUL, and a controlled umask. Regular files,
directories, symlinks, hardlink aliases, permission and special mode bits,
inaccessible paths, and partial read/write failures are significant inputs.
Concurrent namespace changes, ACLs, security labels, capabilities, and
unmodeled special-file kinds are outside the current filesystem model.

`CpSpec.Spec` relates the initial and final filesystem, exact stdout and stderr,
stream committed prefixes, and exit status. Both `CpCore.RunCore` and
`Cp.CpBenchmarkItem.RunCore` directly ensure it. Finite primitive observation
witnesses bind partial effects as well as success; no trusted high-level copy
operation is used.

## Implemented behavior

- Multiple sources, target-directory forms, `-t`, and `-T`.
- Recursive `-R`/`-r`, `-L`/`-H`/`-P`, one-filesystem traversal, retained
  directory symlinks, and trailing-slash stripping.
- Force, no-clobber, destination removal, all modeled update policies,
  attributes-only, verbose output, hard links, and symbolic links.
- Mode and timestamp preservation, disabled preservation attribute lists,
  preserved hardlink aliases through `--preserve=links` and `-d`. The compound
  short form `-dR` combines the supported `-d` and `-R` behavior.
- `--parents`, simple/existing/numbered backups, `-b`, suffix selection,
  `VERSION_CONTROL`, and `SIMPLE_BACKUP_SUFFIX`.
- GNU optional long arguments attached with `=`, unique option/argument
  abbreviations, help/version, and exact parse diagnostics.

Ordinary overwrite preserves an existing regular destination inode and its
aliases. Dangling destination symlinks are refused unless `POSIXLY_CORRECT`
permits creating their referent. Identity checks precede destructive effects.
Ordinary destination removal can replace distinct regular hardlink entries.
When following a symlink source, ordinary copying refuses a regular destination
with the same device and inode, including an alias of the referent. GNU's
same-file check precedes the `--update=older` timestamp decision; `none` and
`none-fail` skip that check. Hard-link early success follows the older-skip
bookkeeping. Repeated files and directories have GNU's distinct diagnostics.
Destination records prevent later operands from overwriting just-created
entries or following just-created symlinks.

Earlier successful operands and committed destination byte prefixes remain
when a later operation fails. Backups rename the old entry before copying and
restore it only if creation has not completed; directories and symlinks can
remain after subsequent attribute failures. Numbered backup selection permits
gaps and arbitrary natural-number versions. `--parents` restores intermediate
modes and timestamps, including special bits and temporary owner access under
restrictive umasks.

Configured backup mode permits directory/non-directory replacement even when
the source ends in `.` or `..`. GNU suppresses actual backup creation for those
names, then applies the ordinary destination-unlink policy, including the
attributes-only guard. Self-copy checking remains active when an existing file
can become a directory. Verbose output and failed removals retain their exact
partial effects.

Attributes-only opens the source for reading without reading its data, and
opens an existing destination for writing without truncating or writing its
contents. Open and close failures remain observable. Force retries report the
successful unlink in verbose output even when a subsequent creation fails.

GNU recursive order depends on raw directory-entry `d_ino`. The formal relation
retains that native observation. Copying into a descendant re-observes the
relevant listing after destination creation and propagates self-copy detection
to stop later siblings, preserving the preceding partial tree. The strict
verbose oracle shares read-only source nodes. The self-copy regression instead
assigns four directory names by observed inode order in each isolated tree,
so both inputs have the same relative native order.

Numbered backup versions are related to canonical positive decimal strings;
the selected maximum is an upper bound that is attained unless it is zero.
Parent offsets form the complete increasing sequence of nonempty component
boundaries. Parsing, maximum scanning, and offset construction belong to Core;
`ParentGroups` is mathematical sequence concatenation.

Source discovery terminates by a finite inode-identity measure with ancestor
cycle detection. Copy recursion decreases the natural `TreeHeight` of retained
source subtrees; finite work-list and index measures handle their children.
Live metadata refresh cannot introduce an unbounded new directory subtree.
There is no arbitrary depth or fuel limit. Shared path algorithms and proved
relations are reused through `bench/core/PathSpec.dfy`, `PathCore.dfy`, and
`PathProof.dfy`; `CpSpec.TrimmedPath` is declarative, and `CpPathProof` connects
the existing implementation summary to it.

## Options left out due to IO.dfy

Ownership preservation, xattrs, security contexts, sparse allocation, and
reflink allocation lack faithful low-level observations. Archive mode and
ordinary `-p` require those unavailable preservation effects. Interactive
replacement also requires an unavailable interactive input observation.
Disabling their preservation is expressible and supported.

`--debug` also requires GNU copy-backend observations. `src/cp.c` enables
verbose and debug together; `src/copy.c:emit_debug` prints the recorded copy
offload, reflink, and sparse-detection decisions. `src/copy-file-data.c` records
offload attempts and `SEEK_HOLE` versus zero scanning, while `copy.c` records
clone outcomes. `ReadFile`/`WriteFile` expose bytes and error stages, without
those backend choices or capabilities, so they cannot determine the exact GNU
debug text. That option remains excluded rather than inventing fixed backend
results.

Special-file boundaries differ by kind. FIFO recognition (`GetFileStatus`'s
`FifoKind`) and native creation (`CreateSpecialNode(FifoNode)`, implemented with
`mkfifo`) exist. However, successful `CreateSpecialNodeSpec` observations in
`ValidFilesystemObservation` constrain only eligibility: their `postFs` does
not guarantee the created kind, new namespace entry, or preservation of other
entries and aliases. The exact required FIFO creation effect cannot be proved
from that contract. Recursive FIFO node replication remains excluded pending
that shared effect contract. Block/character replication additionally lacks
source `st_rdev`; sockets have no creation constructor. FIFO content copying
requires a separate endpoint/stream protocol, rather than regular finite-file
reads. These are distinct from the FIFO success-effect gap.

GNU's atomic forced-link replacement uses `src/force-link.c`'s `CuXXXXXX` and
`try_tempname_len`, followed by link/symlink, rename, and cleanup. Its temporary
namespace and failure effects require an entropy observation absent from the
API. Effective force combined with explicit hard/symbolic-link replacement is
outside this boundary. So is replacement of an existing later destination
through GNU's remembered-alias path, including preserved aliases and the
`--update=older` skipped-alias case (`src/copy.c` calls the same forced-link
primitive). Ordinary forced data copy, ordinary links, and alias preservation
into fresh destination names are supported. No deterministic replacement name
or unlink-first substitute is invented.

Backup basenames requiring GNU's truncation need the unavailable
`pathconf`/`fpathconf(_PC_NAME_MAX)` observation from
`lib/backupfile.c:check_extension`. Accepted backup names fit without that
truncation; the model does not assert an arbitrary universal basename limit.
The generator respects these API boundaries while retaining exact output and
filesystem comparison.

The existing `WriteFile` primitive accepts requested creation permissions
through `0777` and retains the default `0666` for existing callers. Requested
set-ID bits are excluded because Linux writes can clear them. Raw directory
inode observations, constrained directory-open errors, link-source following,
and exact hardlink effects are low-level shared contracts. The attributes-only
source probe uses a separate open/close observation without weakening the
existing full-read contract. Native creation ownership and other inherited
model limits are documented in [the core API guide](../../../docs/core-api.md).

## Native failure observations

Metadata, mode, symlink-target, path-identity, directory open/read/close, and
mutation failures are bound to the exact primitive request. The utility-owned
observation bundle keeps these native failures alongside filesystem results.
A failed mode or symlink query retains the earlier successful metadata
observation; it does not substitute a failed initial stat. Copying and
restoration retain the filesystem effects of earlier successful operations.
Directory cleanup consumes the opened handle on a close error and preserves
the primary read error when both reading and closing fail.

## Historical validation and evidence

The following records describe the earlier filesystem implementation. They
are historical evidence, not verification of the subsequent native-failure
contract changes. Current failure semantics and model limits are described in
[the API model limits](../../../docs/core-api.md#trust-limits-and-api-changes).

Maintenance starts at repository revision
`1ed3144e6b092f50ce99b0450d242a43309e1bd4`. Integrated commands run in
`/workspace/tmp/fs-benchmarks-20261020/integration` with
`PYTHONPATH="$PWD/src:$PWD"`. Tools are Dafny
`4.11.1+10dca3ba4a2909c11299176440401fc31413b53d`, Z3 `4.16.0`, .NET SDK
`8.0.131`, Python `3.12.3`, pytest `9.1.1`, Ruff `0.15.12` and Rust/Cargo
`1.94.0`. Docker uses `dafnyutils-coreutils-fuzzer:latest`, image
`sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76`,
uid/gid 1000 and the existing 10-second command timeout.

- The final integrated `make check TASK=cp` passes with unchanged source
  manifests: build, all 193 strict GNU runtime cases, the mandatory 20-case
  campaign, all 84 declarations and 2696 verification conditions, and all five
  marked Spec/Core/CpPathProof/Proof/Entry module cases. Compilation, runtime
  agreement and proof success are separate checked results. Canonical policy
  remains isolated assertions, included-file checking, seed 42, a 30-second
  condition limit and a 100-second declaration limit. The marked module tests
  retain their existing helper defaults.
- The frozen executable's full comparison passes all 3,000 cases: seeds 19, 1
  and 7 each complete 1000 matches with no mismatch, timeout or other error, in
  258.42, 256.67 and 262.80 seconds. Its before/built/after manifests match;
  all six exact saved replays also pass. Later edits refine only the approved
  shared directory-read error domain and ghost proof guidance; utility
  execution, native IO, generators and the comparator are unchanged. The final
  contribution gate rebuilds and reruns all strict cases and its short campaign.
- Cargo formatting, compilation and the three existing capability registry
  unit tests pass on the final five-utility registration. Ruff formatting and
  checks pass for all 134 Python files. The normal fuzzer binary retains all
  five registrations during the library unit checks.
- The separate approved shared-core closure passes 598 declarations and 3640
  conditions on unchanged sources. Native extern behavior remains a separate
  trusted boundary. No new assumption, trust annotation, verification skip,
  execution bound or increased verifier limit is introduced.

Current-workspace artifacts are external to public task resources under
`/workspace/tmp/fs-benchmarks-20261020/evidence/`. The latest full runtime source
manifests, 193-case oracle, six strict replay checks and 3,000-case campaigns are
in `runtime-directory-cp-final/cp/`; the final supported contribution gate is
`final-gate-cp-approved-v2/`. The final proof-only refinement and unchanged-policy
focused/default results are in `cp-proof-final/`; earlier cumulative behavioral
fixes are in `cp_repair/` and `cp/integrated-directory-final.json`. Approved
shared-library evidence is in `core-approved-closure-v5/`; final registration
and static checks are in `quality-landing-cp-final-v1/`. Public-profile, affected
legacy and development checks are recorded separately. Earlier failed proof
attempts, module timeouts and formatting warnings remain historical failed
checks in the referenced logs; they are not passing evidence for this source.

Six genuine mismatches are retained as failed campaigns:

| Seed/iteration | Trigger | Preserved campaign evidence |
| --- | --- | --- |
| 1/61 | `--parents` lost a source parent's sticky bit | `runtime-final-cp/cp/` |
| 1/328 | `-R -L . DEST` continued after nested self-copy | `runtime-final-cp-v2/cp/` |
| 1/950 | attributes-only skipped a read-only destination open | `runtime-final-cp-v3/cp/` |
| 19/102 | backup renamed a symlink source's regular referent | `runtime-final-cp-v4/cp/` |
| 19/196 | older-update skipped a required same-file diagnostic | `runtime-boundary-final/cp/` |
| 19/249 | dot-source backup produced the wrong replacement and self-copy tree | `runtime-samefile-cp-final/cp/` |

Exact saved bundles are `/tmp/coreutils-fuzzer-repros/cp-seed1-iter61`,
`cp-seed1-iter328`, `cp-seed1-iter950`, `cp-seed19-iter102`,
`cp-seed19-iter196`, and `cp-seed19-iter249` in that same directory. For each
fixed mismatch the replay command deliberately returns 2 with
`FUZZER_OUTCOME=replay_not_reproduced`; the strict checked status is 0 only when
it reports comparator Match, rather than an alternate failure verdict.
The previous snapshot matched 1000 cases each for seeds 1 and 7 but failed at
seed 19/249; that result is not a full 3k pass.

`Tests.py` is a benchmark oracle/scoring fixture selected by
`BenchmarkDefinition.evaluation` and `benchmarks.make_tasks`;
`pytest-dev.ini` excludes `bench/` from development tests. The fixed fixture has
13 nodes and fewer than 64 data bytes; the inode-aligned self-copy fixture has
8 nodes including its root. New dot-source cases use three tiny nodes per tree.
Teardown restores permissions only on named bounded nodes. The oracle compares
exact output/status and complete bounded filesystem bytes, kinds, modes,
ownership, targets and normalized inode alias groups. Timestamps follow the
existing comparator policy. No Python development temporary-directory test or
weakened comparator was introduced.
