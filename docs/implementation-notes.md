# Utility implementation notes

Use these notes when writing a utility specification, implementation, proof and
GNU comparison tests. The examples show common mistakes; the utility entries
list required behavior, errors and current limits.

For the contribution workflow, see [Extending benchmark](../CONTRIBUTING.md#extending-benchmark).

## Contents

- [Common implementation rules](#common-implementation-rules)
- [Handle stream errors and partial output](#handle-stream-errors-and-partial-output)
- [Check filesystem effects](#check-filesystem-effects)
- [Prove the utility contract](#prove-the-utility-contract)
- [Requirements by utility](#requirements-by-utility)
- [b2sum](#b2sum)
- [base32](#base32)
- [basenc](#basenc)
- [cksum](#cksum)
- [date](#date)
- [dd](#dd)
- [dir](#dir)
- [dircolors](#dircolors)
- [fmt](#fmt)
- [join](#join)
- [link](#link)
- [md5sum](#md5sum)
- [mkdir](#mkdir)
- [mkfifo](#mkfifo)
- [mknod](#mknod)
- [od](#od)
- [pathchk](#pathchk)
- [pr](#pr)
- [ptx](#ptx)
- [realpath](#realpath)
- [rm](#rm)
- [rmdir](#rmdir)
- [sha1sum](#sha1sum)
- [sha224sum](#sha224sum)
- [sha256sum](#sha256sum)
- [sha384sum](#sha384sum)
- [sha512sum](#sha512sum)
- [sort](#sort)
- [split](#split)
- [sum](#sum)
- [sync](#sync)
- [test](#test)
- [truncate](#truncate)
- [tsort](#tsort)
- [unexpand](#unexpand)
- [unlink](#unlink)
- [vdir](#vdir)
- [Candidates awaiting model work](#candidates-awaiting-model-work)

## Common implementation rules

### Handle stream errors and partial output

**Example: copy stdin to stdout, even when reading returns partial data and an error.**
These are method-body examples using `io: BenchIO.IO`. The method changes
`io.stdinRegion` and `io.stdoutRegion`. See the full [copy example](../example/copy/Copy.dfy).

Bad — loses bytes returned with a read error and ignores write errors:

```dafny
var data, readErr := io.ReadStdinWithOutcome();
if readErr != 0 {
  return 1; // data may still contain bytes that must be written.
}
var committed, writeErr := io.WriteStdoutWithOutcome(data);
return 0; // A failed write is reported as success.
```

Good — writes the returned bytes and checks both errors:

```dafny
var data, readErr := io.ReadStdinWithOutcome();
var committed, writeErr := io.WriteStdoutWithOutcome(data);
return if readErr == 0 && writeErr == 0 then 0 else 1;
```

**Example: specify a write that may stop after two bytes.**
These predicates use the real library types. `C` means `IOContract`.

Bad — requires all bytes to be written, even on failure:

```dafny
predicate BadWrite(before: BenchWorld.Bytes, after: BenchWorld.Bytes,
                   data: BenchWorld.Bytes)
{
  after == before + data
}
```

Good — describes the bytes actually written and preserves earlier output:

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

`WrittenPrefix` explains one property; it is not a complete write specification.
Use `C.WriteStdoutWithOutcomeSpec` to also connect the result and `errno` to the
trusted IO observation, as [CopySpec.dfy](../example/copy/CopySpec.dfy) does.

**Required tests and limits**

- Include missing files, directories used as input, access denied and invalid
  arguments in the specification and GNU comparison tests. Follow GNU's rules
  for file operands, repeated `-`, continuing after errors and exit status.
- Test failed writes, including `/dev/full`. Record a signal as a signal, not success.
- Use stable finite regular files, captured stdin and enough memory. Exclude
  interactive terminals, infinite/device input, concurrent changes, forced memory
  exhaustion, disk spilling and injected late read/close failures.
- The read API returns one error code for open/read/close; it does not identify
  the failed step. Step-specific diagnostics for injected faults need a maintainer
  model extension. Exact output timing and buffering under asynchronous faults
  are also outside the model.
- Reads may update host access times; this is not a modeled filesystem change.
  Claim only the evaluator's declared observations. New observations return the
  task to `model_preparation` until maintainer review and approval.
- An excluded option may still be valid GNU behavior. Do not label it invalid.
  Keep the agreed scope in the description, formal specification, generated
  profile and case generator. Changes need maintainer review and must not narrow
  released benchmarks.

### Check filesystem effects

**Example: create one directory.**
These methods use `BenchIO`, `BenchWorld` and `C = IOContract`.
They illustrate the IO contract, not the full `mkdir` command or its diagnostics.

Bad — this verifies without creating anything:

```dafny
method BadCreate(io: BenchIO.IO, path: BenchWorld.Path, mode: bv32)
    returns (ok: bool, err: int)
  ensures ok <==> err == 0
{
  return true, 0; // The contract never mentions the filesystem or path.
}
```

Good — connects the requested path and mode to the observed filesystem result:

```dafny
method CreateOne(io: BenchIO.IO, path: BenchWorld.Path, mode: bv32)
    returns (ok: bool, err: int)
  modifies io.fsRegion
  ensures C.CreateDirectorySpec(
    old(io.fs()), old(io.now()), old(io.trustedFilesystem()),
    old(io.umask()), io.fs(), path, mode, ok, err)
{
  ok, err := io.CreateDirectory(path, mode);
}
```

The library connects the typed request to `ok`, `errno` and the complete returned
filesystem through `TrustedFilesystemEffectContractFields`. The IO handle owns
the fixed observation function. Do not choose another state to make a proof pass.
POSIX/libc correctness remains trusted. For `mkdir`,
`DirectoryValidFilesystemObservations` and `DirectoryCreationEffectFields` also
constrain successful directory creation.

**Example: the first operation succeeds and the second fails.**
Inside a method that changes `io.fsRegion`:

```dafny
var firstOK, firstErr := io.CreateDirectory(firstPath, mode);
var secondOK, secondErr := io.CreateDirectory(secondPath, mode);

// Bad: the first call may already have changed the filesystem.
// This assertion is not valid in general.
assert !secondOK ==> io.fs() == old(io.fs());
```

Good — relate **each** call to its own starting state using `CreateDirectorySpec`,
as `CreateOne` does. Keep the first call's effects when processing the second
result. The utility specification must also require the correct operand order,
exact diagnostics and final exit status.

**Test environment and comparisons**

- Use a stable, isolated local Linux test tree, the evaluator's fixed non-root
  user, controlled `umask` and ordinary permission bits. Keep all operands inside
  that tree; never target the host root or mounts to cause a failure.
- Use regular files, directories, symlinks and hard links. Cross-mount tests,
  access/default ACLs, SELinux/SMACK, capabilities, setgid inheritance,
  block/character devices, resource exhaustion and concurrent changes need
  separate maintainer review of the behavior and model.
- Check paths, node types, contents, modes, owners, link targets, link counts and
  alias relationships as applicable. For example, two hard links must point to
  the same file **within each run**; their raw inode numbers need not match
  between GNU and Dafny runs. The comparator removes host keys and checks
  identity changes separately.
- Keep parent/child timestamp effects in the returned state. Compare timestamps
  under the evaluator's policy, not by requiring exact wall-clock equality
  between runs. Stronger checks need maintainer observation work first.
- Include the GNU comparison cases listed for each utility below. Shared-model
  tests cover only their recorded native success/error cases, not a whole utility.

### Prove the utility contract

**Example: an API exists, but the utility proof is still missing.**
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

Good — requires the complete copy specification, including the error policy:

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

This is the entry point in [Copy.dfy](../example/copy/Copy.dfy).
Changing its exit assignment to `exit := 0` makes verification fail.

- `open` means an API and a sufficient observable contract exist for the listed
  scope, based on source review and representative contract/native checks.
  It does not mean the utility specification or proof is complete.
- Each contribution must rule out the counterexamples listed in its scope.
- A whole-read API is not an incremental stdin API. Follow the restrictions for
  `od` and `sort` below. Logical input consumption is modeled; matching GNU's
  kernel read-ahead or a shared descriptor's final offset is not established by
  this API or the current stdout/stderr/filesystem comparator.
