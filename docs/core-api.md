# Use the trusted core API

`bench/core` provides IO APIs and their contracts for utilities. A utility proof
holds only under these contracts; libc, gnulib and the C/C# adapters are trusted,
not verified.

Current maintenance validation and source-snapshot evidence are recorded in the
[trusted API audit](trustbase-failures.md).

## Contents

- [Index](#index)
- [Copy stdin with explicit error results](#copy-stdin-with-explicit-error-results)
- [Entry and CLI contract](#entry-and-cli-contract)
- [Values and observations](#values-and-observations)
- [Streams](#streams)
- [Diagnostics and process context](#diagnostics-and-process-context)
- [Paths and metadata](#paths-and-metadata)
- [Filesystem effects](#filesystem-effects)
- [Timestamps](#timestamps)
- [Directory iteration](#directory-iteration)
- [CLI and pure helpers](#cli-and-pure-helpers)
- [Trust limits and API changes](#trust-limits-and-api-changes)

## Index

| Source | Responsibility |
| --- | --- |
| [World.dfy](../bench/core/World.dfy) | Mathematical model of the system |
| [Errno.dfy](../bench/core/Errno.dfy) | Linux errno constants for contracts, utilities and native adapters |
| [IOContract.dfy](../bench/core/IOContract.dfy) | Specification of IO APIs |
| [IO.dfy](../bench/core/IO.dfy) | IO APIs for making effect (e.g., read, write on files ) on the system |
| [CliTypes.dfy](../bench/core/CliTypes.dfy) | CLI protocol data types; no parsing algorithms or derived proofs |
| [Utf8.dfy](../bench/core/Utf8.dfy), [StringEscaping.dfy](../bench/core/StringEscaping.dfy) | Executable pure encoding and byte-quoting definitions, also usable in specifications |

## Copy stdin with explicit error results

[StreamCopy](../tools/fixtures/contributor/StreamCopy.dfy) copies the stdin bytes
it read, even after a read error, and returns both errors so the caller picks the
exit status. The checked-in file uses a relative `include`.

```dafny
include "/workspace/dafnyutils/bench/core/IO.dfy"

module StreamCopy {
  import BenchIO
  import BW = BenchWorld
  import C = IOContract

  method CopyInput(io: BenchIO.IO) returns (readErr: int, writeErr: int)
    modifies io.stdinRegion, io.stdoutRegion
    ensures readErr == 0 && writeErr == 0 ==>
      io.stdin() == [] && io.stdout() == old(io.stdout()) + old(io.stdin())
  {
    var read := io.ReadStdin();
    var data := C.ReadResultData(read);
    readErr := C.ResultErrno(read);
    var write := io.WriteStdout(data);
    writeErr := C.ResultErrno(write);
  }

  method {:main} Main()
    modifies BenchIO.Process().stdinRegion, BenchIO.Process().stdoutRegion
  {
    var readErr, writeErr := CopyInput(BenchIO.Process());
    BenchIO.Exit(if readErr == 0 && writeErr == 0 then 0 else 1);
  }
}
```

`old(io.stdout())` is needed because stdout changes. The frame covers all other
state; do not restate it.

Run this check from the Dafnyutils root in the development container.

```sh
# Expected duration: Estimated 1–10 sec for this small client after tool installation.
# Success criteria: Exit 0 and zero verification errors.
dafny verify --standard-libraries:false tools/fixtures/contributor/StreamCopy.dfy
```

This checks only the client contract, not the native build, GNU `cat` parity or
error messages. Expected output:

```text
Dafny program verifier finished with 4 verified, 0 errors
```

For a complete program with a partial-result spec, exit policy, proof, build and
error tests, see the
[small IO example](../README.md#example-test-and-verify-a-small-program).

## Entry and CLI contract

A utility's local `CliSupport.dfy` defines `BenchItem.BenchmarkItemTwostate<CmdRaw>` with hooks `Name`,
`Schema`, `ParseConfig`, `Decode`, `FormatParseError`, `PlanParsed`,
`PlanParseFailure`, `PlanArgv` and `RunCore`. `BenchItem.RunMain(item, argv, io)`
runs `RunCore` for `CliRun(raw)`, or writes the planned output and exit status
for `CliEarlyExit`. Early-exit writes are checked explicitly; stdout failure
appends the named GNU write-error diagnostic after the planned diagnostics, and
either write failure returns exit status 1.

The parser and runner are task-local fixed protocol scaffolding. They preserve
the command-line-to-raw-input mapping and call the shared pure UTF-8 definition
for diagnostic encoding. Runtime algorithms and their derived proofs belong in
the utility's editable Core and Proof sources, outside the fixed CLI dependency
closure.

- `RunCore` must ensure `Spec(raw, io, exit)` directly; a proof about a helper
  is not enough.
- Test early exits too. Example: `true` and `false` keep the original argument
  count when detecting help/version.
- Keep fixed diagnostic text in Spec. The utility chooses the error, operand,
  quoting style, message order and exit code; trusted errno and quoting calls
  only transform values.
- Note that we don't verify CLI parsing itself. In the formal specification,
  we assume that input arguments are well-formed.

## Values and observations

`IOResult<T>` is `Results.Result<T, IOError>`, i.e. `Ok(v) | Err(e)` from
[Result.dfy](../bench/core/Result.dfy). The shared type exposes only result
construction, inspection and error-propagation projections. Utilities implement
any result mapping or binding they need; Seq's proof maps its parse result locally.

- `BenchIO.Process()`: the process's `IO` handle.
- `BenchIO.Exit(code)`: exits the process.
- `IO.Init` cannot be called from verified code. Never create a new `IO` to
  reset observations.
- `io.Footprint()`: all regions, for broad frames. Prefer the smallest regions.

Observers are ghost (proof-only), each reads its same-named getter function (e.g., `fs()` reads `fsRegion`).
Direct access to `*Region` field is not allowed.

| Observer | Value |
| --- | --- |
| `fs()` | Inode filesystem, including aliases |
| `stdin()`, `stdout()`, `stderr()` | Unread input; output written so far |
| `cwd()`, `env()`, `props()` | Historical cwd hint, environment, process properties |
| `cwdContext()` | Authenticated current directory context and operation ordinal |
| `directoryState()`, `directoryModel()` | Validated live state; FS-indexed model and immutable response provider |
| `directoryTopology()`, `directoryPosition()` | Current full-record directory view and position token |
| `currentDirectoryPath()` | Genuine current pathname as a sequence of length zero or one |
| `directoryCapabilities()`, `directoryOrdinal()`, `directoryObservations()` | Owned live capabilities, next occurrence, immutable responses |
| `credentials()`, `security()`, `umask()` | Process identity and filesystem security context |
| `dirHandles()`, `directoryOrigins()` | Exact legacy handle map and authenticated opening snapshots |
| `now()`, `stdoutTimestamp()` | Current seconds; stdout timestamp state |
| `statusObservations()`, `statusCursor()` | File-status observations and the next position (`statusObservationsRegion`) |
| `trustedTimeParses()` | Result per date/timestamp parse request |
| `trustedStreams()` | Result per read/write request |
| `trustedFilesystem()` | Result per filesystem request |
| `trustedNativeFailures()` | Exact errno per metadata, identity, legacy mutation, stdout timestamp or directory request |

Observation providers are functions of their request keys. An identical key has
the same result. Status ordinals distinguish old ordered status calls, and the
typed cwd/directory context advances an operation ordinal. Other legacy native
and stream requests can repeat a key without a new occurrence. See the
[maintenance audit](trustbase-failures.md) for this temporal abstraction limit.

`directoryStateRegion` aliases `dirHandlesRegion`. That region contains one
validated joint resource value; its legacy and live handle keys are disjoint.
Observers preserve the exact legacy map without sign-based filtering. Candidates
cannot mutate the region's private representation. The full context contains
current topology/position, live capabilities, legacy maps and an operation
ordinal. `cwd()` is a historical hint; unnamed cwd access uses the authenticated
position and full records, never a pathname fallback.

In the tables below, "Modifies" names an IO region. `none` means no modeled
change; a native read may still update host access times. Specs use `reads` and
methods use `modifies` to state what stays unchanged.

## Streams

Stream methods return `IOResult<T>`.

Every stream call returns an explicit result, including a failed call that has
already consumed or committed a prefix. Callers inspect `Err` and choose their
own diagnostics and exit status. There is no stream error policy or exception
path that can turn a failed call into a success-only proof obligation. Writes
to standard descriptors are unbuffered.

`ReadStdin` returns the exact result selected by
`ObservedReadStdinResultFields(beforeStdin, observations)` and leaves the exact
unread suffix selected by `ObservedReadStdinRemainingFields`. Every public
stream result is `Ok` exactly when `ResultErrno(result) == 0`; failed results
retain the native errno and committed prefix.

`ReadStdin` is a verified Dafny loop over `ReadStdinChunk` calls with a
64 KiB limit:

- There is no separate `NativeReadStdin` primitive or whole-read observation
  request.
- Its result is derived from a finite partition of the chunk observations that
  ends with an empty successful read (EOF) or a failed read.
- Lemmas prove the partition's uniqueness, byte conservation, exhaustion on
  success and the accumulated prefix on failure. No assumption relates
  independent whole and chunk reads.

| Function | Return |
| --- | --- |
| `ReadFile(path)` → `IOResult<Bytes>` | `Ok`: the byte stream of whole file. `Err(ReadFailure(errno, message, partial, readStage))`: errno, message, bytes read, failed stage. |
| `ProbeReadFile(path)` → `IOResult<Bytes>` | Opens read-only and closes without reading contents. Data is empty; the exact errno and `OpenFailed`/`CloseFailed` stage remain observable. |
| `ReadStdin()` → `IOResult<Bytes>` | `StreamFailure` holds the bytes read; bytes read + remaining input = old stdin. |
| `ReadStdinChunk(limit)` → `IOResult<Bytes>` | One noninterrupted bounded read; successful short prefixes are allowed. A failure consumes no bytes; an empty successful result is EOF for finite captured input. |
| `WriteStdout(data)` → `IOResult<WriteReceipt>` | Appends exactly the committed prefix; `StreamFailure` holds the count. |
| `WriteStderr(data)` → `IOResult<WriteReceipt>` | Same, for stderr. |

Full data does not mean success: a read can fail at close after returning all
bytes, and an empty write can fail with nothing committed.

- `ResultErrno`, `ReadResultData`, `ReadResultStage`, `WriteResultCommitted`
  (`IOContract`): get the errno, bytes, stage or committed count from a result.
- `FileReadResultFromOutcome`, `ObservedReadFileResultFields`: build a read
  result from a native outcome or a stream observation. Utility code uses
  `ReadFile`'s result directly.

`ProbeReadFile` uses its own `StreamOpenReadFile` request and
`ObservedOpenReadFileResultFields`, so access and close observations remain
separate from full reads. Its result contains no data and cannot have the
`ReadFailed` stage. It supports commands such as `cp --attributes-only` that
must open the source without consuming its bytes. The existing `ReadFileSpec`
and whole-file `ReadFile` operation retain their behavior.

`ReadStdinChunk` binds its result and exact unread suffix to
`StreamReadStdinChunk(beforeStdin, limit)` through
`ObservedReadStdinChunkResultFields` and
`ObservedReadStdinChunkRemainingFields`. Its precondition is
`0 < limit <= 9223372036854775806` in the fixed 64-bit Linux profile.
The adapter uses the registered stdin capability and retries interrupted reads;
it returns after one noninterrupted native read. The primitive does not fill
blocks, pad input, swap bytes, count records, or select utility diagnostics.
`dd` implements and proves those derived policies in its editable task closure.
`ReadStdin` implements the generic whole-input policy above this primitive;
its public result/remaining-input guarantees retain their behavior.

For a failed chunk, `StreamFailure.partial` is empty and `committed` is zero.
If earlier chunks succeeded, the upper `ReadStdin` failure contains their entire
concatenated prefix and its length. These contracts describe read-call outcomes;
they do not add standard-input close receipts or cover every managed-runtime
resource-exhaustion exception.

The raw `TrustedStreamRequest` and `TrustedStreamResult` datatypes and all
stream contract relations admit inspection of malformed observations. Actual IO
ghost state stores `IOContract.ValidStreamObservations`: each callable request must have
the matching result constructor and satisfy its full original operation relation.
For `StreamReadStdinChunk`, validity uses exactly the native method's existing
`0 < limit <= 9223372036854775806` domain; unused invalid-limit raw requests remain
expressible and unconstrained. Whole-input `ReadStdin` remains derived from
validated chunk observations, with no independent whole-read request.
`trustedStreams()` keeps its raw function return type and guarantees
`StreamObservationsValid`. `StreamFailureWitness` constructively proves that this
state invariant is inhabited for every request, and
`StreamObservationAdmitsRequest` provides the observation fields as a witness of
the unchanged full Spec. The witness is ghost proof data; native operations report
their actual outcomes. Utilities retain their unconditional observable Specs and
do not gain assumptions or caller preconditions from this correction.

Each utility decides what to do with partial data; `cat` prints the bytes read
before the error. Read diagnostics come from the errno and failed stage, not a
later metadata lookup.

| Method | Contract | Modifies |
| --- | --- | --- |
| `ReadFile` | `ReadFileSpec` | `none` |
| `ProbeReadFile` | `OpenReadFileSpec` | `none` |
| `ReadStdin` | `ReadStdinSpec` | `stdinRegion` |
| `ReadStdinChunk` | `ReadStdinChunkSpec` | `stdinRegion` |
| `WriteStdout` | `WriteStdoutSpec` | `stdoutRegion` |
| `WriteStderr` | `WriteStderrSpec` | `stderrRegion` |

## Diagnostics and process context

- `GetCLocaleErrnoText(err)`: libc error text.
- `QuoteafPath(path)`: quoted file name bytes.
- `QuoteArgument(value: Bytes)`: the C-locale argument-quoting contract compatible
  with gnulib `quote_mem` (C escapes and single quotes). The current
  `IOExtern.cs` implementation is a managed compatibility adapter, not a direct
  gnulib call. Encode text with `Utf8Semantics.Encode`; raw
  input bytes need no encoding. An embedded NUL is
  escaped, so to match a C-string `quote` call, pass only the bytes before it.
- `ParseTimestamp`, `ParseDate`: `IOResult<ParsedInstant>` under
  `TrustedTimeParseResultFields`, from pinned gnulib via `TouchTimeParser.c`
  (C locale, `TZ=UTC0`). The parser is trusted, not verified.
- The result values are defined in `IOContract`; `BenchIO.CLocaleErrnoTextResult`,
  `BenchIO.QuoteafPathResult` and `BenchIO.QuoteArgumentResult` forward to them.

| Method | Contract | Modifies |
| --- | --- | --- |
| `GetCLocaleErrnoText` | `GetCLocaleErrnoTextSpec` | `none` |
| `QuoteafPath` | `QuoteafPathSpec` | `none` |
| `QuoteArgument` | `QuoteArgumentSpec` | `none` |
| `GetCwd` | `DirectoryOperationSpec` with `DirectoryGetCwd` | `directoryStateRegion` |
| `GetEnv` | `GetEnvSpec` | `none` |
| `GetEnvironment` | `ValidEnvironment`; `GetEnvironmentSpec` | `none` |
| `GetLoginName` | `GetLoginNameSpec` | `none` |
| `GetUmask` | `GetUmaskSpec` | `none` |
| `Now` | `NowSpec` | `none` |
| `ParseTimestamp` | `ParseTimestampSpec` | `none` |
| `ParseDate` | `ParseDateSpec` | `none` |

The time-parse provider similarly stores `ValidTimeParseObservations` internally;
`trustedTimeParses()` keeps its raw map return type and guarantees
`TimeParseObservationsValid`. Successful observations require nanoseconds in
`[0, 1000000000)`, while failures preserve their observed fields. An empty map is
a constructive witness, and `TimeParseObservationAdmitsRequest` proves that each
request has an outcome of the unchanged timestamp/date Spec. Malformed raw maps
remain expressible, but cannot inhabit the IO model state.

`Now`, the environment map and the umask are supplied process-context observations.
POSIX `umask` has no error return; its adapter observes and restores the actual
value. Invalid environment keys cannot be found in the validated map. `GetCwd`
is different: it returns `IOResult<Path>` from libc `getcwd(NULL, 0)`, preserves
the immediate native errno, and frees a successful allocation. It has no `"."`
substitute. Success identifies the genuine pathname of the authenticated current
position; failure is allowed even when a pathname exists. GNU recovery belongs
to Pwd's utility implementation and proof.

## Paths and metadata

| Method | Returns | Contract | Modifies |
| --- | --- | --- | --- |
| `ReadLink` | `IOResult<Path>` | `ReadLinkSpec` | `none` |
| `PathExists` | `IOResult<Unit>` | `PathExistsSpec` | `none` |
| `GetFileMode` | `IOResult<bv32>` | `GetFileModeSpec` | `none` |
| `GetFileStatus` | `IOResult<FileStatus>` | `GetFileStatusSpec` | `statusObservationsRegion` |
| `IsDirectory` | `IOResult<bool>` | `IsDirectorySpec` | `none` |
| `IsSymlink` | `IOResult<bool>` | `IsSymlinkSpec` | `none` |
| `ResolvePathIdentity` | `IOResult<Path>` | `ResolvePathIdentitySpec` | `none` |
| `GetFileTimes` | `IOResult<FileTimeStatus>` | `GetFileTimesSpec` | `none` |

- On failure, `Err` holds the errno and message; there is no metadata.
- `FileStatus`: inode identity, link count, kind, mode, owner, size/storage and
  times. Identity tells aliases apart.
- `GetFileStatus` consumes the next status observation and advances the cursor,
  even on failure.
- Resolvable paths may still fail with a modeled native errno. Success retains
  the exact kind, mode, target, identity and status guarantees; a finite error
  domain does not itself identify the actual failure.
- These APIs bind errno to `trustedNativeFailures()` using the exact operation,
  prior filesystem, operands and status ordinal where applicable. Bound status
  contexts carry both the time provider and native failure provider. Use the
  observed API relation in a utility's principal specification; an existential
  lower projection such as `IsDirectoryStrictContractFields` is insufficient to
  justify a native failure.
- ABI path validation rejects embedded NUL with `EINVAL`. `ReadLink` preserves
  the actual `EINVAL` for an ordinary file instead of relabeling it as `ELOOP`.
  Metadata name-length failures retain `ENAMETOOLONG`.

`SYMLINK_MAX_DEPTH = 40` bounds symlink following within one modeled native
pathname lookup, matching the Linux kernel's
[`MAXSYMLINKS` limit](https://docs.kernel.org/filesystems/path-lookup.html).
It is not a bound on the total number of `ReadLink` calls a utility may perform.
The repository's pinned GNU `realpath` walks and expands links in user space,
so it can resolve finite chains longer than forty links. Library implementations
and other revisions may impose different cumulative limits. The realpath
utility implements and proves its pinned traversal and cycle rules locally;
the bounded metadata resolver cannot replace that algorithm. The existing
`Symlink` node, `ReadLink` primitive and ordinal-sensitive parent `GetFileStatus`
contract supply the individual observations. No shared canonicalization
primitive or global utility traversal bound is added.

### Authenticated relative paths

The following methods pass the raw operand unchanged and start resolution at the
authenticated current position or a held directory. They can describe a renamed
or detached cwd without requiring a recoverable absolute pathname.

| Method | Contract | Modifies |
| --- | --- | --- |
| `ReadLinkAtCwd(path)` | `ReadLinkAtCwdSpec` | `directoryStateRegion` |
| `GetFileStatusAtCwd(path, follow)` | `GetFileStatusAtCwdSpec` | `directoryStateRegion`, `statusObservationsRegion` |
| `GetFileStatusAtDir(parent, path, follow)` | `GetFileStatusAtDirSpec` | same |
| `SetFileModeAtCwd(path, follow, mode)` | `SetFileModeAtCwdSpec` | `fsRegion`, `directoryStateRegion` |
| `SetFileModeAtDir(parent, path, follow, mode)` | `SetFileModeAtDirSpec` | same |
| `OpenDirAtCwd(path, dots)` | `OpenDirAtCwdSpec` | `directoryStateRegion` |
| `OpenDirAtDir(parent, path, dots)` | `OpenDirAtDirSpec` | `directoryStateRegion` |

Every call returns an `IOResult` and binds the exact native request. Read-only
calls satisfy `CwdContextReadStepFields`: only the operation ordinal advances.
Status also advances its separate cursor on failure. Mode success preserves
identity and all record fields except mode/change time across visible aliases
and live unnamed objects. Open success returns an owned live capability with
its authenticated anchor, entry set and dot policy; failure retains ownership.

`ResolvePathAtCwdForMetadataFields` and
`ResolvePathAtDirContextForMetadataFields` return an `IOResult<CwdTarget>`.
`CwdTargetRecordFields` selects the exact full record;
`CwdTargetNamedPathFields` supplies a genuine optional namespace path. Do not
assert that every successful target is namespace-reachable. Resolution starts
at the directory itself, preserving symlink-hop behavior and avoiding permission
checks on unrelated ancestors. It does not lexically normalize the raw operand.
For an owned relative parent, the AtDir methods require
`DirectoryParentAnchorForContextRequestFields`; callers prove its current-anchor
fact from their own trace. Absolute, empty, NUL and unknown-parent errors remain
callable under that predicate.

The legacy path APIs above retain their existing root-based model projection
for relative spellings while native calls use process cwd. The new APIs repair
their explicit clients; they do not claim a general correction to every legacy
relative-path contract or composition after cwd movement. New typed mode effects
prove their before/after identity and topology transport. Arbitrary legacy
filesystem mutations do not gain a general transport theorem between their
FS-indexed directory views. Old CLI and API input domains are unchanged.

## Filesystem effects

- `WriteFile(path, data, createMode := 0666)` accepts ordinary permission bits
  `0000` through `0777`; native `open` applies the process umask. Existing callers
  retain `0666`. The request binds this mode to the observed creation effect.
  Special set-ID bits require a separate metadata-preservation operation because
  Linux can clear them during a write; the new parameter's precondition excludes
  those bits.
- `WriteFile`, `AppendFile`: `IOResult<WriteReceipt>`. `WriteFailure` holds the
  errno, message, committed count and `FileWriteStage` (see
  [Write failures](#write-failures)).
- All other calls: `IOResult<Unit>`. All except `Sync` modify `fsRegion`.
- `CreateDirectory`, `RemoveDirectory`, `CreateHardLink`, `UnlinkPath`,
  `TruncateFile` and `CreateSpecialNode` take their whole result, including the
  filesystem after the call (also on failure), from a trusted observation
  (`TrustedFilesystemEffectContractFields`). This does not prove that the native
  filesystem matches the model.
- Successful unlink and empty-directory removal delete exactly the resolved
  namespace entry and preserve surviving aliases. Truncation preserves the
  existing inode and aliases, with the old prefix followed by zero bytes on
  extension. Successful hard-link creation adds an alias to the selected inode.
  Parent metadata, allowed timestamp changes and native storage observations
  remain part of the trusted result; these relations do not prove libc/kernel
  correctness.
- `CreateFile` retains its existing fixed observation contract. Fresh-file mode
  and ownership come from that observation, rather than a new mathematical
  ownership or umask guarantee. GNU differential oracles compare both fields.
- `Sync` takes a trusted result and does not change the modeled filesystem.
- `CreateHardLink(source, target, followSource := false)` keeps the existing
  native `link` behavior by default. `true` uses `linkat` with
  `AT_SYMLINK_FOLLOW` to follow a terminal source symlink; destination creation
  does not follow an existing terminal link. Empty paths retain native errno;
  a path with NUL fails with `EINVAL`.
- `CreateSymlink`, `DeletePath`, `SetFileMode` and `RenamePath` retain their
  modeled successful effects and failure frames, while binding a native errno
  to an exact `trustedNativeFailures()` request. In particular, an unsupported
  symlink mode change remains an error. `UnlinkPath` uses a richer whole-result
  filesystem observation; these operations are not interchangeable.
- Recursion, parent creation, overwrite policy and diagnostics are up to the
  utility. An available API does not mean device privileges or every filesystem
  setup are approved.

| Method | Contract | Modifies |
| --- | --- | --- |
| `CreateFile` | `CreateFileSpec` | `fsRegion` |
| `WriteFile` | `WriteFileSpec` | `fsRegion` |
| `AppendFile` | `AppendFileSpec` | `fsRegion` |
| `CreateSymlink` | `CreateSymlinkSpec`; an empty destination returns native ENOENT (2) | `fsRegion` |
| `DeletePath` | `DeletePathSpec` | `fsRegion` |
| `CreateDirectory` | `CreateDirectorySpec` | `fsRegion` |
| `RemoveDirectory` | `RemoveDirectorySpec` | `fsRegion` |
| `CreateHardLink` | `CreateHardLinkSpec` | `fsRegion` |
| `UnlinkPath` | `UnlinkPathSpec` | `fsRegion` |
| `TruncateFile` | `TruncateFileSpec` | `fsRegion` |
| `CreateSpecialNode` | `CreateSpecialNodeSpec` | `fsRegion` |
| `Sync` | `SyncSpec` | `none` |
| `SetFileMode` | `SetFileModeSpec` | `fsRegion` |
| `RenamePath` | `RenamePathSpec` | `fsRegion` |

## Timestamps

`TimestampUpdate` is `Current`, `Keep` or `Exact(sec, nsec)`. Setters return
`IOResult<Unit>`. File setters modify `fsRegion`; stdout setters modify
`stdoutTimestampRegion`. Access-only and modification-only setters `Keep` the
other time. The current time is the modeled `now()`.
Path setters use the validated filesystem provider. Stdout setters additionally
bind the exact prior target, requested updates and native errno through
`trustedNativeFailures()`: even an available target can fail, and a failed
setter preserves its modeled timestamp state.

| Method | Contract | Modifies |
| --- | --- | --- |
| `SetFileTimesNow` | `SetFileTimesNowSpec` | `fsRegion` |
| `SetFileAccessTimeNow` | `SetFileAccessTimeNowSpec` | `fsRegion` |
| `SetFileModificationTimeNow` | `SetFileModificationTimeNowSpec` | `fsRegion` |
| `SetFileTimes` | `SetFileTimesSpec` | `fsRegion` |
| `SetStdoutTimesNow` | `SetStdoutTimesNowSpec` | `stdoutTimestampRegion` |
| `SetStdoutAccessTimeNow` | `SetStdoutAccessTimeNowSpec` | `stdoutTimestampRegion` |
| `SetStdoutModificationTimeNow` | `SetStdoutModificationTimeNowSpec` | `stdoutTimestampRegion` |
| `SetStdoutTimes` | `SetStdoutTimesSpec` | `stdoutTimestampRegion` |

## Directory iteration

- `OpenDir(path, includeDots)` → `IOResult<int>`, an opaque handle.
- `ReadDir(handle)` → `IOResult<DirectoryRead>`: `DirectoryItem(name, kind, inode)`,
  `DirectoryEnd` at EOF, or `Err` (e.g., an invalid handle). It advances the
  handle and returns entries in native order. `inode` is the native `d_ino`
  observation, so utilities can implement GNU's inode-based directory ordering
  without adding metadata lookups. Existing name/kind and handle contracts remain.
- `ReadDirContractFields` requires `0 <= err`: an entry or end-of-directory
  returns zero, and failure returns a positive libc error number.
- `CloseDir(handle)` → `IOResult<Unit>` consumes an owned handle on both
  success and failure. Its exact native errno remains observable. Invalid handles
  return `EINVAL` and leave the handle map unchanged.
- Open, read, opened-directory status and close each use a distinct request in
  `trustedNativeFailures()`. Preserve those links through utility trace
  relations. Cleanup-close failures follow each utility's GNU policy: some
  callers report them, while GNU traversal helpers deliberately preserve an
  earlier read result across cleanup. Either policy must retain the actual
  observed close result and handle transition in the specification.
- Recursion, ordering and filtering are up to the utility.
- `OpenDirOutcomeFields` admits only a positive modeled lookup error or a
  listed native access, I/O, memory, name-length or descriptor-allocation error
  on failure. An existing directory can fail to open. Success still establishes
  the exact resolved-directory handle and entry set, and failure preserves handles.

Entry kinds (`BenchWorld.DirectoryEntryKind`): regular file, directory, symlink,
FIFO, block device, character device, socket, or `UnknownDirentKind`. Never treat
an unknown kind as a regular file or guess it from the name.

`OpenDir(path, true)` keeps `.` and `..`; use it when their position matters.
`false` omits them; `ReadDir` follows the handle's mode. Dots get
`DirectoryDirentKind` without a metadata lookup;
other entries keep their native kind, known or unknown.

`GetOpenDirectoryStatus(handle)` → `IOResult<FileStatus>` of the open directory,
for cycle detection without a separate status call before the open.

- Success consumes the next status observation for the handle's resolved path
  (following symlinks) and advances the cursor by one.
- Failure returns a positive errno and consumes nothing.
- A failed status differs from a failed open; use the matching diagnostic.
- The handle stays open.

| Method | Contract | Modifies |
| --- | --- | --- |
| `OpenDir` | `OpenDirSpec` | `dirHandlesRegion` |
| `ReadDir` | `ReadDirSpec` | `dirHandlesRegion` |
| `GetOpenDirectoryStatus` | `GetOpenDirectoryStatusSpec` | `statusObservationsRegion` |
| `CloseDir` | `CloseDirSpec` | `dirHandlesRegion` |

### Live capabilities and physical cwd recovery

`OpenDirAtCwd`, `OpenDirAtDir`, and `OpenParentDirectory` use the live registry;
legacy `OpenDir` uses its original registry. Handles are opaque Dafny integers,
with no abstract sign restriction. Native legacy keys use an unbounded
`BigInteger` allocator. The registries cannot consume each other's handles.

| Method | Operation and result | Modifies |
| --- | --- | --- |
| `GetCwdDirectoryIdentity()` | `DirectoryCurrentStatus`; exact current `FileStatus` | `directoryStateRegion`, `statusObservationsRegion` |
| `OpenParentDirectory()` | `DirectoryOpenParent`; owned parent handle, dots omitted | `directoryStateRegion` |
| `GetDirectoryDescriptor(handle)` | `DirectoryGetDescriptor`; actual libc fd | `directoryStateRegion` |
| `FchdirDirectory(fd)` | `DirectoryFchdir`; exact cwd movement | `directoryStateRegion`, `cwdRegion` |
| `ChdirParent()` | `DirectoryChdirParent`; source-derived descriptor fallback | `directoryStateRegion`, `cwdRegion` |
| `FstatDirectory(fd)` | `DirectoryFstat`; descriptor status | `directoryStateRegion`, `statusObservationsRegion` |
| `ReadDirectoryCapability(handle)` | `DirectoryReadNext`; raw name, kind, inode or EOF | `directoryStateRegion` |
| `LstatCwdEntry(name)` | `DirectoryEntryLstat`; status of a valid child name | `directoryStateRegion`, `statusObservationsRegion` |
| `CloseDirectoryCapability(handle)` | `DirectoryClose`; consumes on both outcomes | `directoryStateRegion` |
| `GetOpenDirectoryCapabilityStatus(handle)` | Exact live opened libc `statx` status, including a returned ENOSYS | `directoryStateRegion`, `statusObservationsRegion` |

The first nine operations use `DirectoryOperationSpec`; the context-form
`ContextOperationSpec` binds the same request and full before/after context.
Requests include the actual occupied legacy keys, so live allocation is fresh
across both registries. Each occurrence advances the context ordinal. A failed
read retains the exact observed subset `remainingAfterReadError`, admitting
native entry advancement without inventing a returned entry. Dot policy and raw
inode observations remain explicit, including unavailable inode zero and mount
boundaries. An owned read or descriptor operation requires its corresponding
current-anchor predicate; utility traces derive and preserve that fact.

Read-only recovery preserves the filesystem and complete legacy handle/origin
maps. Mode and open operations preserve those same legacy projections despite
sharing their resource region. The joint validity witnesses are proved from
valid model/provider values; native postconditions do not manufacture an old
state invariant. Pwd performs its GNU parent walk in task-owned code and proofs,
including search, errno precedence, fallback selection and output. None of
these primitives implements robust_getcwd for the utility.

## CLI and pure helpers

| Module | Main names | Use |
| --- | --- | --- |
| `CliTypes` | `OptionDecl`, `CliSchema`, `ParseConfig`, `ParsedArgs`, `ParseError`, `CliPlan` | Shared protocol data types only |
| Task-local `CliModel` | `ParseValue(argv, schema, cfg)` | Fixed CLI parser; config sets order, bundling and abbreviations |
| Task-local `CliExtern` | `Cli.Parse`, `Cli.ParsePortable` | Fixed executable parser wrappers with the `ParseValue` result contract |
| Task-local `BenchItem` | `BenchmarkItemTwostate<CmdRaw>`, `RunMain` | Fixed plan/decode/run protocol; hooks in [Entry and CLI contract](#entry-and-cli-contract) |
| `Utf8Semantics` | `Encode`, `EncodeChar`, `ValidExternalText`, `UnicodeScalar` | Executable UTF-8 encoding and input validation |
| `StringEscaping` | C, shell and locale quoting | Executable pure byte-quoting definitions |

Map, filter, scan and fold implementations and their derived proofs are not
supplied as shared verified support. Implement any needed sequence algorithms
and prove their properties in the utility's editable Core and Proof sources.
Utility-specific path algorithms and their connecting proofs are task-local
in `cp`, `mv`, `rm` and `rmdir`. Their mathematical relations remain fixed
specifications; runtime helpers are candidate proof targets. Cp's decoder has
a separate fixed CLI trim routine so it does not make the runtime PathCore
file immutable.

## Trust limits and API changes

`IO.dfy` and `IOContract.dfy` are authoritative; this page cannot strengthen
them.

- Stream contracts fix only the consumed or committed prefix and the errno. They
  describe library results, not syscalls. `FileReadStage` is success, or an
  open, read or close failure. `ReadStdinChunk` supplies bounded stdin reads;
  block assembly remains utility-owned. There are no public standard-stream
  close receipts. Whole operations and utility output plans do not establish
  every libc buffer-flush or syscall-order behavior.
- `AppendFile` results come from native observations. `AppendFile` keeps the
  file on empty input, appends exactly the bytes to the file (or symlink target)
  on success, and leaves other inodes alone; mode and timestamp effects are
  host-specific.
- `GetEnvironment` may list the same map in different orders.
- Ghost credentials are not real UID/GID or name-service lookups.
- Path metadata adapters retain the actual `ENAMETOOLONG` errno.
- `TruncateFile` does not create a missing file. Path `Sync` lacks GNU's
  write-only-open retry and separate failure phases.
- There is no API for running processes, user/group lookup, terminal control,
  random data, disk capacity or seeking within a file. The `remaining_preparation` column of
  [TODOLIST.csv](../TODOLIST.csv) lists what each candidate still needs.

### Filesystem validation

Every trusted filesystem result satisfies `ValidFilesystemObservation`:

- errno is never negative, and the call succeeds exactly when errno is 0;
- no success that the model rules out;
- failure errnos and effects stay within per-operation limits;
- successful directory creation and file writes have the expected effect.

`TrustedFilesystemEffectContractFields` links the request, the prior filesystem
and the result, and requires this check. Keep that link and the check when you
use these contracts. Other success
effects come from each operation's own predicate. The check is proved
satisfiable and never replaces a native errno. The native filesystem is still
trusted.

### Directory creation

Example: creating `parent/new` successfully leaves a fresh empty directory at the
resolved path.

| `CreateDirectorySpec` result | Guarantee |
| --- | --- |
| Success | One new entry: a fresh empty directory (`DirectoryCreationEffectFields`). Other inodes unchanged, except parent metadata and symlink access times. |
| Parent after success | Identity, owner, kind, mode and extension fields unchanged; times, link count and storage may change. |
| Symlinks after success | Only access times may change; traversed links are not tracked. |
| Failure | The request and the returned filesystem stay linked. Namespace and inodes unchanged, except symlink access times. Errno is the modeled cause or a listed host fault. |
| Both | Mode, umask and time come from the request. No exact permission, owner, time or link-count rules. |

`FileSystem` requires a valid inode structure. Parent symlinks and `.`/`..` use
the normal resolver; trailing slashes are accepted without following a final
symlink. Concurrent outside changes are not modeled.

### Error order

- `HardLinkFailureErrnosFields`: a NUL in either path gives only `EINVAL`.
  Otherwise the source is resolved before the empty-target check, so `source/`
  with an empty target excludes `ENOENT` when the source lookup gives `ENOTDIR`.
- `RenameFailureErrnosFields` checks for NUL, then for an empty source or target,
  before resolving either path.
- `unlink` and `rmdir` reject a final symlink with a trailing slash.
- Native fault sets also allow storage, allocation, access-control and
  filesystem-limit errors that the model does not track.

### Write failures

| `FileWriteStage` | Committed | Filesystem after |
| --- | --- | --- |
| `WriteOpenFailed` | 0 | Unchanged, except symlink access times |
| `WriteFailed` | Fewer than requested | `WriteFile`: the file may be created or truncated and holds exactly the committed prefix. `AppendFile`: old contents + committed prefix. |
| `WriteCloseFailed` | All | Same as `WriteFailed` |

`WriteFileSpec` and `AppendFileSpec` bind committed bytes, stage, errno and the
resulting filesystem to the exact validated filesystem request. Legacy
`WriteFileContractFields`/`AppendFileContractFields` project the same partial
creation, truncation, append and close effects, but existentially hide the
receipt and do not identify the actual observation. They cannot replace the
bound API relation in a principal utility specification.

Files created by a failed write still follow the creation mode and owner rules.
`CreateFile` can fail at close after creating its empty file.

### Contributor and maintainer rules

- Maintainers own shared contracts and adapters. To request a missing operation,
  give its GNU scenario, inputs, errors, effects and proposed observation.
- Do not modify immutable support, add unchecked externs, reset IO observations,
  or weaken a contract to pass verification.
- Evaluation owns GNU execution, adapters, comparison and trusted tests.
  Differential replay reproduces observed behavior; it does not prove a Dafny
  spec. Exact-spec replay is not required for contributions. See
  [the full workflow](../CONTRIBUTING.md#validate-and-submit).
