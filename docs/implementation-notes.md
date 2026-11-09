# Utility implementation notes

Notes for writing a utility's specification, implementation, proof and GNU
comparison tests. Each example shows a common mistake.

For the contribution workflow, see [Extending benchmark](../CONTRIBUTING.md#extending-benchmark).

## Contents

- [Common implementation rules](#common-implementation-rules)
- [Handle stream errors and partial output](#handle-stream-errors-and-partial-output)
- [Check filesystem effects](#check-filesystem-effects)
- [Prove the utility contract](#prove-the-utility-contract)

## Common implementation rules

### Handle stream errors and partial output

**Example: copy stdin to stdout when a read returns partial data and an error.**
Method bodies with `io: BenchIO.IO` that modify `io.stdinRegion` and
`io.stdoutRegion`. Full version: [copy example](../example/copy/Copy.dfy).

Bad — drops bytes returned with a read error and ignores write errors:

```dafny
var read := io.ReadStdin();
if read.Err? {
  return 1; // The error may retain bytes that must still be written.
}
var write := io.WriteStdout(read.v);
return 0; // A failed write is reported as success.
```

Good — writes the returned bytes and checks both errors:

```dafny
var read := io.ReadStdin();
var write := io.WriteStdout(IOContract.ReadResultData(read));
return if read.Ok? && write.Ok? then 0 else 1;
```

**Example: specify a write that may stop after two bytes.**
These predicates use the real library types. `C` is `IOContract`.

Bad — requires all bytes to be written, even on failure:

```dafny
predicate BadWrite(before: BenchWorld.Bytes, after: BenchWorld.Bytes,
                   data: BenchWorld.Bytes)
{
  after == before + data
}
```

Good — describes only the bytes written and keeps earlier output:

```dafny
predicate WrittenPrefix(before: BenchWorld.Bytes, after: BenchWorld.Bytes,
                        data: BenchWorld.Bytes, committed: nat)
{
  committed <= |data| && after == before + data[..committed]
}

lemma PartialWriteExample()
{
  // Earlier output: ">". Requested output: "abc". Only "ab" was written.
  assert WrittenPrefix(">", ">ab", "abc", 2);
  assert !BadWrite(">", ">ab", "abc");
}
```

`WrittenPrefix` shows one property, not a full write specification. Use
`C.WriteStdoutSpec` to tie the result and `errno`
to the trusted IO observation, as [CopySpec.dfy](../example/copy/CopySpec.dfy)
does.

**Required tests and limits**

- Specify and test missing files, directory inputs, access denied and invalid
  arguments. Follow GNU for file operands, repeated `-`, continuing after errors
  and exit status.
- Test failed writes, including `/dev/full`. Record a signal as a signal, not
  success.
- Use stable finite regular files, captured stdin and enough memory. Out of
  scope: interactive terminals, infinite/device input, concurrent changes, forced
  memory exhaustion, disk spilling and injected late read/close failures.
- `ReadFile(path)` returns `IOResult<Bytes>`. On failure,
  `ReadFailure` holds the bytes read, the native errno, the message and the
  `FileReadStage`. Each utility decides what to do with those bytes; `cat` writes
  them, then reports the error. Exact output timing and buffering under
  asynchronous faults are not modeled.
- Reads may update host access times; the model ignores this. Claim only the
  evaluator's declared observations. A new observation sends the task back to
  `model_preparation` until a maintainer approves it.
- An excluded option may still be valid GNU behavior; do not call it invalid.
  Keep the same scope in the description, formal specification, generated
  profile and case generator. Scope changes to a released benchmark need
  maintainer review and must not narrow it.

### Check filesystem effects

**Example: create one directory.**
These methods use `BenchIO`, `BenchWorld` and `C = IOContract`. They show the IO
contract only, not the full `mkdir` command or its diagnostics.

Bad — verifies without creating anything:

```dafny
method BadCreate(io: BenchIO.IO, path: BenchWorld.Path, mode: bv32)
    returns (ok: bool, err: int)
  ensures ok <==> err == 0
{
  return true, 0; // The contract never mentions the filesystem or path.
}
```

Good — ties the requested path and mode to the observed filesystem result:

```dafny
method CreateOne(io: BenchIO.IO, path: BenchWorld.Path, mode: bv32)
    returns (ok: bool, err: int)
  modifies io.fsRegion
  ensures C.CreateDirectorySpec(
    old(io.fs()), old(io.now()), old(io.trustedFilesystem()),
    old(io.umask()), io.fs(), path, mode, ok, err)
{
  var result := io.CreateDirectory(path, mode);
  ok := result.Ok?;
  err := C.ResultErrno(result);
}
```

`TrustedFilesystemEffectContractFields` ties the typed request to `ok`, `errno`
and the complete returned filesystem. The IO handle owns this fixed observation function;
do not pick another state to make a proof pass. POSIX/libc correctness stays
trusted. For `mkdir`, `ValidFilesystemObservations` and
`DirectoryCreationEffectFields` also constrain success.

**Example: the first operation succeeds and the second fails.**
Inside a method that modifies `io.fsRegion`:

```dafny
var first := io.CreateDirectory(firstPath, mode);
var second := io.CreateDirectory(secondPath, mode);

// Bad: the first call may already have changed the filesystem.
// This assertion is not valid in general.
assert second.Err? ==> io.fs() == old(io.fs());
```

Good — relate **each** call to its own starting state with `CreateDirectorySpec`,
as `CreateOne` does, and keep the first call's effects when handling the second
result. The utility specification must also require the correct operand order,
exact diagnostics
and the final exit status.

Give filesystem-processing loops their own narrow `modifies` clause. For example,
[`MkdirCore.RunCore`](../bench/utils/mkdir/Impl/MkdirCore.dfy) gathers diagnostic bytes
while its loop modifies only `io.fsRegion`; it flushes the streams afterwards.
Without that loop clause, Dafny inherits the enclosing method's broader stream
frame, so the final output relation loses its starting stream values. State this
preservation through the loop frame rather than adding unchanged-output equalities.
The creation, stream-result and final existential-composition lemmas remain
separate proof obligations.

**Test environment and comparisons**

- Use a stable, isolated local Linux test tree, the evaluator's fixed non-root
  user, a controlled `umask` and ordinary permission bits. Keep all operands in
  that tree; never target the host root or mounts to force a failure.
- Use regular files, directories, symlinks and hard links. These need separate
  maintainer review of behavior and model first: cross-mount tests,
  access/default ACLs, SELinux/SMACK, capabilities, setgid inheritance,
  block/character devices, resource exhaustion and concurrent changes.
- Check paths, node types, contents, modes, owners, link targets, link counts and
  aliases as applicable. Example: two hard links must point to the same file
  **within each run**; raw inode numbers need not match between GNU and Dafny
  runs. The comparator removes host keys and checks identity changes separately.
- Keep parent/child timestamp effects in the returned state. Compare timestamps
  by the evaluator's policy, not exact wall-clock equality between runs. Stronger
  checks need maintainer observation work first.
- Add GNU comparison cases for every behavior in the utility's scope.
  Shared-model tests cover only their recorded native success/error cases, not a
  whole utility.

### Prove the utility contract

**Example: the API exists, but the utility proof is missing.**
These entry points use the existing `CopyCore` and `CopySpec` modules.

Bad — calls the API but promises no utility behavior:

```dafny
method BadRun(io: BenchIO.IO) returns (exit: int)
  modifies io.stdinRegion, io.stdoutRegion
{
  var readErr, writeErr := CopyCore.CopyInput(io);
  exit := 0; // A verifier has no postcondition to reject here.
}
```

Good — ensures the complete copy specification, including the error policy:

```dafny
method RunCore(io: BenchIO.IO) returns (exit: int)
  modifies io.stdinRegion, io.stdoutRegion
  ensures CopySpec.Spec(io, exit)
{
  var readErr, writeErr := CopyCore.CopyInput(io);
  exit := if readErr == 0 && writeErr == 0 then 0 else 1;
  CopyProof.CopyResultImpliesSpec(io, readErr, writeErr, exit);
}
```

This is the entry point in [Copy.dfy](../example/copy/Copy.dfy). Changing its
exit assignment to `exit := 0` makes verification fail.

- `open` means an API and a sufficient observable contract exist for the listed
  scope, based on source review and representative contract/native checks. It does not mean the
  utility specification or proof is complete.
- Each contribution must rule out the counterexamples listed in its scope.
- `ReadStdin` tries to read all input. Success leaves nothing unread; failure can
  return a prefix and leave the rest.
- `ReadStdinChunk(limit)` performs one noninterrupted bounded read and can
  return a successful short prefix. A failed chunk consumes no input.
- `ReadStdin` is a verified Dafny loop over 64 KiB chunk calls. Its whole-input
  observations are derived from those calls, with no native whole-read axiom,
  and its failure retains all earlier successful chunks.
- A utility can stop at a byte count or assemble blocks by proving its own
  consumption and error rules; the primitive supplies neither policy.
- Logical input consumption
  is modeled; GNU's kernel read-ahead and a shared descriptor's final offset are
  not checked by the current stdout/stderr/filesystem comparator.

## tr/paste denotational refactor validation

The refactor replaces output assembly witnesses with exact byte functions and
uses record reconstruction and stdin occurrence counts for paste's input
assignment. `LinesRelationEquivalent` connects the reconstruction equation to the
former partition relation. Core still implements execution; its entry points
retain `ensures Spec(...)`. Output-function determinacy is distinct from a theorem
about the entire IO-dependent `Spec` or CLI termination.

Validation on 2026-11-09 used revision
`4001ff9fbfa907464f2bb1d274a0bdd252208684` plus this working-tree change, in the
development container `dafnyutils-spec-refactor`, from `/workspace/dafnyutils`.
The tools were Dafny `4.11.1+0776df27c2449bad68e9a28e687bb6c70bf4b401`,
.NET SDK `8.0.133`, Python `3.12.3`, and the pinned GNU coreutils
`9.10.13-2cf49` reference. Final proof runs used `DOTNET_PROCESSOR_COUNT=16`;
the supported target's 30-second assertion limit and complete source scope were
preserved.

| Command | Result |
| --- | --- |
| `make -C bench/utils/tr lint build test` | Exit 0; definition valid, build successful, 53 passed and 1 skipped |
| `make -C bench/utils/paste lint build test` | Exit 0; definition valid, build successful, 67 passed and 1 skipped |
| Fuzzing and contributor `final-check` | Not run; this maintenance change preserves the execution algorithms and does not change fuzzer or release policy |
| `make -C bench/utils/tr verify` | Exit 0; 6,194 verified, 0 errors, no timeouts |
| `make -C bench/utils/paste verify` | Exit 0; 3,645 verified, 0 errors, no timeouts |
| `dafny format`, then `dafny format --check` on changed Dafny files | Both exit 0 |
| `git diff --check` | Exit 0 |

The two skips are the existing deferred-feature inventories. Each runtime test
command deselects five `dafny_verify` cases; the full verification targets above
check every local Dafny source, including the entry, implementation and proof
modules. Shared `bench/core` sources remain library contracts under the existing
native trust boundary, and the existing `decreases *` entry points do not prove
CLI termination. Repository-wide development tests were not run because no
Python or Rust code changed.

Commands, versions, failed proof approaches and final logs are retained in
`/workspace/tmp/tr-paste-spec/validation.txt` and its sibling logs inside
`dafnyutils-spec-refactor`; they remain available while that container exists.
The final logs are `tr-formatted-runtime.log`, `paste-formatted-runtime.log`,
`tr-formatted-verify.log`, `paste-formatted-verify.log`, `format.log` and
`format-check.log`. No commit was created.
