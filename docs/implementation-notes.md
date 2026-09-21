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


## Requirements by utility

Each entry lists the behavior to implement and verify for a new contribution.
These are requirements, not completed implementations or claims of full GNU
support. [TODOLIST.csv](../TODOLIST.csv) records open, released and blocked items.
Source paths below are relative to `coreutils/src/`.

### b2sum

| Question | Answer |
| --- | --- |
| Where is the GNU code? | cksum.c: digest_file / digest_check; blake2/b2sum.c |
| What must I implement? | Digest generation; -b, -t, -z and -l digest length; ordered file/stdin operands. |
| What must the spec guarantee? | BLAKE2b parameter block, little-endian words, compression equations, final-block flag and requested digest length; exact GNU record escaping. |
| Which APIs can I use? | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| What is outside this task? | Check-file verification, tagged records and keyed hashing. |

### base32

| Question | Answer |
| --- | --- |
| Where is the GNU code? | basenc.c: do_encode / do_decode (BASE_TYPE=32) |
| What must I implement? | Default encoding; -d, -i, -w (including zero); zero or one file operand. |
| What must the spec guarantee? | Eight output symbols per five input bytes, padding and wrap positions; inverse bit equations with the exact decoded prefix before an invalid suffix. |
| Which APIs can I use? | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostic primitives; pure bit and byte relations. |
| What is outside this task? | Other encodings. |

### basenc

| Question | Answer |
| --- | --- |
| Where is the GNU code? | basenc.c: main / do_encode / do_decode |
| What must I implement? | --base16, --base32, --base64; -d, -i, -w; zero or one file operand. |
| What must the spec guarantee? | Selected alphabet and bit-block relation; option precedence, padding, wrapping and invalid suffix behavior. |
| Which APIs can I use? | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostic primitives; pure bit and byte relations. |
| What is outside this task? | Base32hex, base64url, base2, Z85. |

### cksum

| Question | Answer |
| --- | --- |
| Where is the GNU code? | cksum.c: digest_file; cksum_crc.c: crc_sum_stream |
| What must I implement? | Default POSIX CRC with length and filename; ordered file/stdin operands. |
| What must the spec guarantee? | CRC polynomial remainder including the encoded input length and final complement; decimal checksum/length record grammar. |
| Which APIs can I use? | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| What is outside this task? | -a algorithm selection, check files, raw/base64 and tagged output. |

### date

| Question | Answer |
| --- | --- |
| Where is the GNU code? | date.c: main / show_date |
| What must I implement? | Explicit --reference=FILE, -u, and an explicit +%s, +%Y-%m-%d or +%H:%M:%S format. |
| What must the spec guarantee? | File modification seconds selected through GetFileTimes; signed epoch rendering or UTC civil-calendar arithmetic with exact separators. |
| Which APIs can I use? | GetFileTimes, output outcomes and diagnostics; pure UTC calendar relations. No new date parser helper is shipped. |
| What is outside this task? | Live-clock output, date parsing, setting the clock, nanoseconds, other formats and time zones. ParseDate delivery is currently Touch-specific. |

### dd

| Question | Answer |
| --- | --- |
| Where is the GNU code? | dd.c: scanargs / dd_copy / apply_translations |
| What must I implement? | Finite stdin to stdout; status=none; iflag=fullblock; bs=N and conv=lcase,ucase,swab (valid combinations), including plain copying. |
| What must the spec guarantee? | Byte-index case mapping and adjacent-pair swapping, preserving a final odd byte; ordered composition of requested conversions and exact output prefix. |
| Which APIs can I use? | Finite stream outcomes, output outcomes and diagnostics. Transformations remain pure Dafny. |
| What is outside this task? | if/of, seek/skip/count, record padding, encodings, devices, timed progress/statistics and injected short-read faults. |

### dir

| Question | Answer |
| --- | --- |
| Where is the GNU code? | ls.c: decode_switches / print_current_files; ls-dir.c |
| What must I implement? | Explicit -1; -a, -A, -d, -r; stable local paths, stdout capture and C locale. |
| What must the spec guarantee? | Directory entry selection and bytewise name ordering, GNU dir escape quoting, operand sections and exit status, using directory and metadata APIs. |
| Which APIs can I use? | OpenDir / ReadDir / CloseDir, GetFileStatus / ReadLink, GetEnv, output outcomes and diagnostics; inspect existing ls model for reusable metadata/time relations. |
| What is outside this task? | Default columns, terminal layout, recursive listing, color, ACL/context markers and long output. |

### dircolors

| Question | Answer |
| --- | --- |
| Where is the GNU code? | dircolors.c: dc_parse_stream / append_quoted / main |
| What must I implement? | Explicit -b or -c and one configuration file; normal TERM/COLORTERM matching and color/extension records in C locale. |
| What must the spec guarantee? | Line grammar, shell selection, ordered active assignments, shell escaping and TERM glob language; no regular-expression engine required. |
| Which APIs can I use? | Finite stream outcomes, GetEnv, output outcomes and diagnostics. Transformations remain pure Dafny. |
| What is outside this task? | Implicit SHELL inference, embedded database output and print-ls-colors display mode. |

### fmt

| Question | Answer |
| --- | --- |
| Where is the GNU code? | fmt.c: get_paragraph / fmt_paragraph / base_cost / line_cost |
| What must I implement? | Default; -w, -g, -s, -u; ordered file/stdin operands. |
| What must the spec guarantee? | Paragraph/word partition, indentation, exact line-break cost equations and strict tie rule; include the source buffer flush boundaries in the relation. |
| Which APIs can I use? | Finite stream outcomes, output outcomes and diagnostics. Transformations remain pure Dafny. |
| What is outside this task? | Crown/tagged margins, prefix selection and legacy -WIDTH spelling. |

### join

| Question | Answer |
| --- | --- |
| Where is the GNU code? | join.c: join / check_order / prjoin |
| What must I implement? | Two operands, at most one stdin; -1, -2, -j, -t, -a, -v, -e; --check-order / --nocheck-order. |
| What must the spec guarantee? | Ordered field records, equal-key group Cartesian products and unmatched rows; exact order-check detection point and retained output prefix. |
| Which APIs can I use? | Finite stream outcomes, output outcomes and diagnostics. Transformations remain pure Dafny. |
| What is outside this task? | Output lists, headers, case folding, NUL records and historical syntax. |

### link

| Question | Answer |
| --- | --- |
| Where is the GNU code? | link.c: main |
| What must I implement? | Exactly two operands; normal option delimiter/help/version handling. |
| What must the spec guarantee? | One FilesystemCreateHardLink request relating source/target and the state before the call, exact diagnostic on failure and normal exit. |
| Which APIs can I use? | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| What is outside this task? | Cross-mount links, devices and privileged directory links. |

### md5sum

| Question | Answer |
| --- | --- |
| Where is the GNU code? | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| What must I implement? | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| What must the spec guarantee? | MD5 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Which APIs can I use? | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| What is outside this task? | Check-file verification and tagged output. |

### mkdir

| Question | Answer |
| --- | --- |
| Where is the GNU code? | mkdir.c: process_file / main; ../gnulib/lib/mkdir-p.c |
| What must I implement? | Default one-directory creation; -v; ordered operands. |
| What must the spec guarantee? | `CreateDirectorySpec` with typed `FilesystemCreateDirectory` requests (0777, umask and time); success proves a fresh empty directory and preservation of unrelated state; existential intermediate filesystems; exact success/error/verbose records and exit conjunction. Permission and metadata laws remain native observations. |
| Which APIs can I use? | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| What is outside this task? | -p, -m, security contexts, setgid inheritance, ACLs and cross-mount/resource races. |

### mkfifo

| Question | Answer |
| --- | --- |
| Where is the GNU code? | mkfifo.c: main |
| What must I implement? | Default FIFO creation with mode 0666 and process umask; ordered operands. |
| What must the spec guarantee? | FilesystemCreateSpecialNode with FifoNode and zero device numbers; ordered outcomes, errors and exit aggregation. |
| Which APIs can I use? | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| What is outside this task? | -m, security contexts, FIFO data transfer and device nodes. |

### mknod

| Question | Answer |
| --- | --- |
| Where is the GNU code? | mknod.c: main (case p) |
| What must I implement? | FIFO form NAME p (including GNU first-character type matching); default mode 0666 and umask. |
| What must the spec guarantee? | Same FifoNode request as mkfifo with mknod-specific operand/type grammar and diagnostics. |
| Which APIs can I use? | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| What is outside this task? | Block/character devices, device numbers, -m and security contexts; these still need approved test setups for privileged operations. |

### od

| Question | Answer |
| --- | --- |
| Where is the GNU code? | od.c: decode_format_string / dump / write_block |
| What must I implement? | Explicit -t x1, o1 or u1; -A, -j, -N, -v, -w; regular file operands (no stdin for bounded reads). |
| What must the spec guarantee? | Byte-block partition, offsets, radix rendering, padding and duplicate-row compression over the selected byte interval. |
| Which APIs can I use? | Finite stream outcomes, output outcomes and diagnostics. Transformations remain pure Dafny. |
| What is outside this task? | Stdin with skip/limits (whole-read API cannot retain an unread suffix), implicit word format, multibyte/float/character formats and legacy offsets. |

### pathchk

| Question | Answer |
| --- | --- |
| Where is the GNU code? | pathchk.c: validate_file_name / portable_chars_only / no_leading_hyphen |
| What must I implement? | -p or --portability (equivalent to -p -P); one or more names. |
| What must the spec guarantee? | Portable byte alphabet; nonempty pathname, POSIX path/component byte bounds; optional no-leading-hyphen rule with source error precedence. |
| Which APIs can I use? | GetCwd for lexical realpath; pathchk portability is pure argv processing; output outcomes and diagnostics. |
| What is outside this task? | Default host pathconf/searchability mode and -P alone. |

### pr

| Question | Answer |
| --- | --- |
| Where is the GNU code? | pr.c: init_parameters / print_files / print_page |
| What must I implement? | Explicit -t; single-column output; -l page length, -d double spacing, -n numbering, -o indentation; file/stdin operands. |
| What must the spec guarantee? | Line/page partitions, form-feed boundaries, numbering, spacing and indentation; omit headers/trailers as requested. |
| Which APIs can I use? | Finite stream outcomes, output outcomes and diagnostics. Transformations remain pure Dafny. |
| What is outside this task? | Timestamped headers, multicolumn/merge layouts, custom date formats and terminal behavior. |

### ptx

| Question | Answer |
| --- | --- |
| Where is the GNU code? | ptx.c: initialize_regex / compare_occurs / define_all_fields |
| What must I implement? | Default GNU keyword output; -w width and -g gap; file/stdin input, stdout only; no user regex. |
| What must the spec guarantee? | Maximal C-locale alphabetic word intervals; the fixed default sentence-boundary language; keyword ordering with source-position ties, clipping and reference fields. |
| Which APIs can I use? | Finite stream outcomes, output outcomes and diagnostics. Transformations remain pure Dafny. |
| What is outside this task? | User regex, break/ignore/only files, traditional mode, roff/TeX, input/automatic references and output files. |

### realpath

| Question | Answer |
| --- | --- |
| Where is the GNU code? | realpath.c: realpath_canon / process_path; ../gnulib/lib/canonicalize.c: canonicalize_filename_mode |
| What must I implement? | Explicit -m -s; -z and -q; one or more nonempty/empty operands in the fixed Linux filesystem namespace. |
| What must the spec guarantee? | Absolute lexical component normalization relative to GetCwd; slash/dot/dotdot rules and newline/NUL rendering; empty-path error. |
| Which APIs can I use? | GetCwd for lexical realpath; pathchk portability is pure argv processing; output outcomes and diagnostics. |
| What is outside this task? | Physical/logical link traversal, existence checks, relative-to/base and alternate platform double-slash roots. |

### rm

| Question | Answer |
| --- | --- |
| Where is the GNU code? | rm.c: main; remove.c: rm / prompt / excise |
| What must I implement? | Explicit -f; optional -v; nonrecursive ordinary files/symlinks and directory-rejection cases; ordered operands. |
| What must the spec guarantee? | Typed unlink results, missing-name suppression, directory refusal, dot/dotdot protection and verbose output for successful removals. |
| Which APIs can I use? | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| What is outside this task? | Interactive/default prompting, recursion, -d, secure overwrite, mount traversal and resource races. |

### rmdir

| Question | Answer |
| --- | --- |
| Where is the GNU code? | rmdir.c: remove_parents / main |
| What must I implement? | Default empty-directory removal; -v; ordered operands. |
| What must the spec guarantee? | Typed FilesystemRemoveDirectory relation for each operand; GNU attempt/verbose/error order and retained prior effects. |
| Which APIs can I use? | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| What is outside this task? | -p and --ignore-fail-on-non-empty. |

### sha1sum

| Question | Answer |
| --- | --- |
| Where is the GNU code? | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| What must I implement? | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| What must the spec guarantee? | SHA-1 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Which APIs can I use? | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| What is outside this task? | Check-file verification and tagged output. |

### sha224sum

| Question | Answer |
| --- | --- |
| Where is the GNU code? | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| What must I implement? | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| What must the spec guarantee? | SHA-224 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Which APIs can I use? | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| What is outside this task? | Check-file verification and tagged output. |

### sha256sum

| Question | Answer |
| --- | --- |
| Where is the GNU code? | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| What must I implement? | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| What must the spec guarantee? | SHA-256 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Which APIs can I use? | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| What is outside this task? | Check-file verification and tagged output. |

### sha384sum

| Question | Answer |
| --- | --- |
| Where is the GNU code? | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| What must I implement? | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| What must the spec guarantee? | SHA-384 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Which APIs can I use? | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| What is outside this task? | Check-file verification and tagged output. |

### sha512sum

| Question | Answer |
| --- | --- |
| Where is the GNU code? | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| What must I implement? | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| What must the spec guarantee? | SHA-512 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Which APIs can I use? | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| What is outside this task? | Check-file verification and tagged output. |

### sort

| Question | Answer |
| --- | --- |
| Where is the GNU code? | sort.c: compare / check / sort |
| What must I implement? | Whole-line C byte order; -r, -u, -s, -c, -C, -z; file/stdin operands, stdout output (check mode uses regular files). |
| What must the spec guarantee? | Ordered multiset of records (set multiplicities for -u), delimiter normalization and exact first-disorder location; stable ties where relevant. |
| Which APIs can I use? | Finite stream outcomes, output outcomes and diagnostics. Transformations remain pure Dafny. |
| What is outside this task? | Stdin check mode (early-stop consumption needs incremental IO), keys, numeric/month/version/random order, output files, merging and spilling. |

### split

| Question | Answer |
| --- | --- |
| Where is the GNU code? | split.c: lines_rr / main |
| What must I implement? | Explicit -n r/K/N to stdout; optional one file operand or stdin; default newline records. |
| What must the spec guarantee? | Select records at indices congruent to K-1 modulo N, preserving exact bytes and the last unterminated record. |
| Which APIs can I use? | Finite stream outcomes, output outcomes and diagnostics. Transformations remain pure Dafny. |
| What is outside this task? | File-creating modes, filters/subprocesses, byte/line-size partitions, suffix policies and custom separators. |

### sum

| Question | Answer |
| --- | --- |
| Where is the GNU code? | cksum.c: digest_file; sum.c: bsd_sum_stream / sysv_sum_stream |
| What must I implement? | Default BSD checksum; -r and -s; ordered file/stdin operands. |
| What must the spec guarantee? | BSD rotate/add congruences or System V byte-sum folding; ceiling block count with the selected 512/1024-byte unit and filename rules. |
| Which APIs can I use? | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| What is outside this task? | Other cksum algorithms and check-file syntax. |

### sync

| Question | Answer |
| --- | --- |
| Where is the GNU code? | sync.c: main / sync_arg |
| What must I implement? | Global no-operand sync; --help/--version and invalid option combinations including -d without operands. |
| What must the spec guarantee? | Typed FilesystemSync(AllSyncTargets, SyncAllFilesystems) result; exact CLI diagnostics and exit. Persistence internals stay trusted. |
| Which APIs can I use? | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| What is outside this task? | All path-targeted modes: adapter lacks GNU write-only-open retry and open/sync/close failure-phase observations. |

### test

| Question | Answer |
| --- | --- |
| Where is the GNU code? | test.c: posixtest / unary_operator / binary_operator |
| What must I implement? | String -n/-z and =/!=; integer -eq/-ne/-lt/-le/-gt/-ge; !, parentheses, -a/-o and GNU argument-count precedence. |
| What must the spec guarantee? | A declarative expression grammar and rules based on the number of arguments, decimal integer values and Boolean truth; syntax errors distinct from false. |
| Which APIs can I use? | CliPlan/PlanArgv override, output outcomes and diagnostics; expression rules without IO. |
| What is outside this task? | Filesystem, identity/access, terminal predicates and the separate [ command. |

### truncate

| Question | Answer |
| --- | --- |
| Where is the GNU code? | truncate.c: main / do_ftruncate |
| What must I implement? | Explicit -c -s N with absolute nonnegative decimal size through signed 64-bit maximum; stable regular files/symlinks, directories and missing paths. |
| What must the spec guarantee? | Missing-path no-create success; otherwise typed FilesystemTruncate request, absolute size and operand order. Ordinary open/path errors use cannot-open wording; no late truncate/close faults in this scope. |
| Which APIs can I use? | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| What is outside this task? | Default file creation, reference/relative/block sizes, nonregular objects, resource/late operation/close faults and injected failures. |

### tsort

| Question | Answer |
| --- | --- |
| Where is the GNU code? | tsort.c: record_relation / scan_zeros / detect_loop / tsort |
| What must I implement? | Zero or one file/stdin operand; space/tab/newline-separated pairs; self pairs, duplicate edges and cycles; legacy -w no-op. |
| What must the spec guarantee? | Graph ordering rules: initial zero nodes by strcmp order; FIFO eligibility, successors in reverse insertion order; exact deterministic cycle selection/removal and diagnostics. |
| Which APIs can I use? | Finite stream outcomes, output outcomes and diagnostics. Transformations remain pure Dafny. |
| What is outside this task? | No additional transformation modes; late read/close faults follow the common exclusion. |

### unexpand

| Question | Answer |
| --- | --- |
| Where is the GNU code? | unexpand.c: next_file / unexpand |
| What must I implement? | Default leading blanks; -a, --first-only, -t tab lists including continuation; ordered file/stdin operands. |
| What must the spec guarantee? | Column-position and tab-stop relation preserving nonblank bytes; backspace/newline effects and GNU option precedence. |
| Which APIs can I use? | Finite stream outcomes, output outcomes and diagnostics. Transformations remain pure Dafny. |
| What is outside this task? | Non-C locale display widths. |

### unlink

| Question | Answer |
| --- | --- |
| Where is the GNU code? | unlink.c: main |
| What must I implement? | Exactly one operand, including symlink operands. |
| What must the spec guarantee? | One FilesystemUnlink request without terminal dereference; preserve the returned state and select GNU failure diagnostic. |
| Which APIs can I use? | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| What is outside this task? | Recursive removal and open detached handles. |

### vdir

| Question | Answer |
| --- | --- |
| Where is the GNU code? | ls.c: decode_switches / print_long_format; ls-vdir.c |
| What must I implement? | Explicit -n --time-style=long-iso; -a, -A, -d, -r; C locale and UTC0. |
| What must the spec guarantee? | Numeric ownership, mode, links, size, UTC modification time, escaping, ordered rows and width/total rules from observable metadata. |
| Which APIs can I use? | OpenDir / ReadDir / CloseDir, GetFileStatus / ReadLink, GetEnv, output outcomes and diagnostics; inspect existing ls model for reusable metadata/time relations. |
| What is outside this task? | Name-service output, default locale time style, devices, ACL/context markers, recursive listing and terminal/color features. |


## Candidates awaiting model work

For a `model_preparation` item, read `remaining_preparation` in [TODOLIST.csv](../TODOLIST.csv). That field preserves the specific blocker, such as missing identity lookup or process execution. An available libc function does not create a Dafny wrapper. Ask maintainers to prepare and review the missing contract before treating the scope as open.

The openings above were recorded against core revision `1f52dd00e39906bb6970746fb103beff9219072e` plus the additive quoting wrapper, and GNU revision `2cf491412c199e2211880ec3f4ba387026638a33`. Check current declarations before relying on historical evidence.
