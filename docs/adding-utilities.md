# Add a utility from start to finish

Contribute a utility by writing its behavior contract, implementing it, proving the entry point, and comparing the executable with the pinned GNU binary. Submit all four kinds of evidence for human review.

This guide follows `base32`, an open utility with byte-stream input. The scaffold is a starting point, not a working implementation. Use the existing `base64` and `cat` projects to learn the structure; do not copy their specifications as the meaning of `base32`.

## Contents

- [Set up your checkout](#set-up-your-checkout)
  - [Install the tools](#install-the-tools)
  - [Check the installation](#check-the-installation)
- [Find the right files](#find-the-right-files)
- [Build one contribution](#build-one-contribution)
  - [Agree on the observable behavior](#agree-on-the-observable-behavior)
  - [Create the files](#create-the-files)
  - [Specify first, then implement and prove](#specify-first-then-implement-and-prove)
  - [Add differential cases and a generator](#add-differential-cases-and-a-generator)
- [Validate and submit](#validate-and-submit)
  - [Check the definition and public profile](#check-the-definition-and-public-profile)
  - [Build, test and verify](#build-test-and-verify)
  - [Open a pull request](#open-a-pull-request)
- [Initial scopes](#initial-scopes)
  - [Shared stream scope](#shared-stream-scope)
  - [Filesystem environment and observations](#filesystem-environment-and-observations)
  - [What open status means](#what-open-status-means)
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

## Set up your checkout

### Install the tools

Use the checked-in [development container](../.devcontainer/devcontainer.json). On a host with Docker and VS Code's Dev Containers extension, open this repository and select **Dev Containers: Reopen in Container**. Setup installs Python 3.12, .NET 8, Rust and native build tools, creates `.venv`, installs the development/contributor extras, initializes the pinned coreutils submodule and its dependencies, and builds the bundled Dafny source. Allow an estimated 10–30 minutes with downloads; a cold or slow network can take longer. This is based on the setup script, not a new clean-machine timing.

The container uses the host Docker daemon for execution tests. Docker access must work from its terminal. The full editor setup was not rerun for this documentation update.

Run all commands below in a Bash or zsh terminal at `/workspace/dafnyutils`, with `.venv/bin` on `PATH`. Use the repository's `dafny-benchmark`, not an unrelated Dafny installation. If you use another checkout path, adjust absolute paths in examples.

### Check the installation

```sh
# Expected duration: < 1 sec in the documentation checkout.
# Success criteria: Exit 0 and list, init, validate and check appear.
python3 -m benchmarks --help
```

This checks the installed contributor CLI. It does not build or verify a utility. The check completed within 10 seconds. Output excerpt:

```text
usage: python -m benchmarks [-h] [--root ROOT] {list,init,validate,check} ...
```

## Find the right files

| Path | Purpose |
| --- | --- |
| `bench/utils/<utility>/` | Utility definition, description, Dafny modules and local Makefile |
| `bench/core/` | Shared model, contracts, helpers and trusted runtime adapters |
| `coreutils/` | Pinned upstream GNU source and tests; keep its revision fixed |
| `tools/benchmark_templates/coreutils/` | Incomplete starting files used by the scaffold command |
| `tools/coreutils_fuzzer/` | Differential runner, generators and comparison logic |
| `src/benchmarks/` | Discovery, validation, builds and contribution checks |
| `_build/` | Generated binaries and reports, created by build/check commands |

Read [bench rules](../bench/AGENTS.md) and [Dafny style](../DAFNYSTYLE.md) before editing Dafny. Agent-assisted changes also follow the repository's plan and knowledge workflow.

## Build one contribution

### Agree on the observable behavior

Choose an `open_for_contribution` row in [TODOLIST.csv](../TODOLIST.csv), then read its [initial scope](#initial-scopes). For `base32`, the opening covers encoding, `-d`, `-i`, `-w`, and zero or one file operand. It does not cover other encodings.

Write a scope table in `bench/utils/base32/base32.md` before implementation:

| Question | Example answer for base32 |
| --- | --- |
| What is the source? | Pinned `coreutils/src/basenc.c`, built with `BASE_TYPE=32`; record the submodule commit |
| What is accepted? | Finite raw bytes from stdin or one regular file; the options in the agreed initial scope |
| What is observed? | Exact output and error bytes, exit behavior, and modeled input consumption |
| Which environment? | Linux, C locale and UTC0; prepared filename and IO domains |
| Which errors matter? | Invalid alphabet/padding/options; missing or inaccessible file; partial progress followed by failure |
| What is trusted? | Named `bench/core` IO and diagnostic contracts, with their recorded revision |
| What remains to prove? | Bit-block relation, padding, wrapping, decoding prefix, diagnostics and exit policy |

A missing API or observation is a maintainer model issue. Record it before extending the scope. Do not narrow an existing task, assume successful IO, or add an unchecked native call to make a proof pass.

### Create the files

```sh
# Expected duration: Estimated < 1 sec; copies a small local template.
# Success criteria: Exit 0 and a new bench/utils/base32 directory.
python3 -m benchmarks init --kind coreutils --id base32
```

Run this only when `base32` is absent. The command refuses to overwrite an existing item and reports that the scaffold is incomplete. It was not run in this checkout because this documentation change must not add a benchmark.

Replace `benchmark.yaml` with this complete metadata after checking the source and license:

```yaml
schema_version: benchmark.definition.v2
task_id: base32
kind: coreutils
source:
  status: verified
  name: GNU coreutils base32
  url: https://www.gnu.org/software/coreutils/
  license: GPL-3.0-or-later
```

Here `verified` means the source attribution has been checked. It does not mean the utility or its proof has passed. New contributions cannot use `legacy-unverified`. Do not add invented fields for evaluator paths: the loader derives them from the task ID and family.

Complete these generated files:

| File | What to put there |
| --- | --- |
| `base32.md` | Agreed input, option, environment, output and error scope, with examples and source provenance |
| `Base32Schema.dfy` | CLI schema/configuration, raw command types and decode behavior |
| `Base32Spec.dfy` | Declarative observable relation and fixed help/version/error text |
| `Base32Core.dfy` | Executable parsing/processing algorithms and implementation witnesses |
| `Base32Proof.dfy` | Lemmas connecting the implementation summary to the specification |
| `Base32.dfy` | Entry assembly; `RunCore` directly ensures the principal `Spec(...)` |
| `Base32Cli.dfy` | Process entry using `BenchIO.Process()`, the shared runner and `BenchIO.Exit` |
| `Tests.py`, `Tests.dfy` | Evaluator-owned differential cases and executable Dafny cases |
| `dfyconfig.toml`, `Makefile` | Existing project/build conventions from the scaffold |

### Specify first, then implement and prove

State the result as a mathematical relation. For example, a valid base32 block relates five input bytes to eight alphabet symbols through bit equations. Padding and line breaks have separate position rules. Decoding must constrain the bytes emitted before an invalid suffix. A second copy of the encoder loop is not an independent specification.

Use the [core API guide](core-api.md) for IO, byte conversion and reusable lemmas. Keep algorithms in Core, proof connections in Proof, and fixed user-facing text in Spec. Spec must not import Core, Proof or CLI. Keep the direct entry obligation:

```dafny
ensures Spec(raw, io, exit)
```

This is a contract line, not a complete method. Use the actual argument types and frames of your utility. A separate `CoreSummary ==> Spec` lemma supports this obligation; it does not replace it. Use narrow `reads` and `modifies` clauses. Do not add `assume`, trust annotations, or verification skips.

The shared runner calls `RunCore` only for a run plan. Help, version and parse errors may use an early-exit plan. Review and test that CLI path separately; a `RunCore` proof alone does not prove every early-exit branch.

### Add differential cases and a generator

Follow [Add test cases](adding-test-cases.md) to port upstream scenarios into `bench/utils/<utility>/Tests.py`, reusing its fixtures and runner helpers. Compare the pinned GNU binary with the built Dafny binary. Include normal, malformed-input and partial-effect cases; reject plausible wrong outputs as part of specification review.

For a new utility, add its generator under `tools/coreutils_fuzzer/src/fuzz/input/generators/`, declare the module in `generators/mod.rs`, and register `GENERATOR` in `src/utils/capabilities.rs`. Reuse `PatternInputGenerator` and the shared argument-pattern engine. See [generator extension](fuzzing.md#support-a-new-utility) for the concrete registration points. A case JSON file alone does not register a new utility.

Keep evaluator cases, oracle code and reference answers out of public task resources. Authors can inspect public GNU tests during maintenance; an evaluated agent may only read material allowed by that run's protocol.

## Validate and submit

### Check the definition and public profile

```sh
# Expected duration: Unknown; depends on source analysis and the completed utility.
# Success criteria: Exit 0 and base32: valid.
python3 -m benchmarks validate base32
```

This checks the completed item and its contract structure. The untouched scaffold is intentionally invalid. This example was not executed because `base32` is not implemented here.

```sh
# Expected duration: Unknown; requires the completed item and Dafny analysis.
# Success criteria: Exit 0 and _build/profile-review/base32/task.json exists.
python3 -m tools.generate_task_profiles --utility base32 --output-dir _build/profile-review
```

Review the generated specification closure, read-only support and editable/output boundaries. Confirm that tests and oracle material are absent. This generation command was checked against its source but not run for an unimplemented item. Generation is not a proof.

### Build, test and verify

```sh
# Expected duration: Unknown; first GNU bootstrap/build depends on downloads and CPU.
# Success criteria: Exit 0 and _build/coreutils/src/base32 is executable.
make build-coreutils
```

This builds the pinned original utilities. It may need network access for build inputs. An existing GNU build was available during this documentation update; this full build was not repeated.

```sh
# Expected duration: Unknown; requires a complete Base32 implementation and .NET.
# Success criteria: Exit 0 and _build/bench/base32_bench.dll exists.
make -C bench/utils/base32 build

# Expected duration: Unknown; depends on the new case population and Docker setup.
# Success criteria: Exit 0 with real, non-skipped runtime cases passing.
make -C bench/utils/base32 test

# Expected duration: Unknown; depends on proof obligations and solver cost.
# Success criteria: Exit 0 and zero Dafny verification errors for the project closure.
make -C bench/utils/base32 verify
```

These separate compilation, executable behavior and proof. They were not run for the unimplemented example. A build is not verification, and matching a finite test set is not proof of the specification. On a timeout, locate the expensive obligation and add local proof guidance before considering a larger time limit.

```sh
# Expected duration: Unknown; includes builds, runtime tests, 20 fuzz cases and proofs.
# Success criteria: Exit 0 and base32: checks passed; every required check completes.
make check TASK=base32
```

This is the final contribution gate. Current mandatory checks are `impl_layout`, `implementation_tests`, `fuzzer`, `proof_layout` and `dafny_verify`, defined in [checks.py](../src/benchmarks/checks.py). The implementation test report is `_build/contribution_checks/base32/implementation-tests.xml`; it must include at least one non-skipped case. Missing tools, unsupported fuzzing, skipped mandatory work and timeouts are not passes. This full new-utility example remains unverified until the utility is implemented and the gate runs.

### Open a pull request

Follow [CONTRIBUTING.md](../CONTRIBUTING.md) and use the [pull request template](../.github/pull_request_template.md). Paste actual stdout in **tests → fuzzing → verification** order, with commands, exit codes and accessible artifacts. For each affected coreutils utility, show three distinct seeds with at least 1,000 completed matching iterations each, no failures, and full comparison settings. The 20-case automatic gate is additional evidence, not a substitute. Explain failed, unrun and inapplicable checks. Include source revision/license, accepted scope, trusted APIs, the principal specification, proof/termination limits, and exact commands with outcomes. Record campaign seeds, budgets, artifact identities, original mismatch bundles and separate fixed-case regression results.

The maintainer reviews whether the specification describes GNU behavior, rejects wrong behavior, and uses only the approved trust boundary. Automated checks do not replace this review. Keep failed and unrun checks visible and rerun affected checks after corrections.

## Initial scopes

These handoffs preserve the existing openings; they are not completed utility implementations or claims of full GNU support. [TODOLIST.csv](../TODOLIST.csv) records open, released and blocked items. The source paths below are relative to `coreutils/src/`.

### Shared stream scope

For stream utilities, ordinary missing-file, directory-as-input, inaccessible-file and invalid-argument
behavior belongs in each specification and differential suite. File operands
and repeated `-` must follow GNU's operand rules; failures must preserve earlier
output and the utility's continuation/exit policy. The outcome API exposes
consumed/committed prefixes and errno, so success cannot be assumed merely
because a call returned.

The stream scopes use stable finite regular files and captured stdin with
available memory. Interactive terminals, unbounded/device streams, concurrent
file mutation, injected allocation exhaustion, disk spilling and injected
late read/close faults are outside these new scopes. The current read interface
aggregates native open/read/close failure into one errno and does not identify
which phase failed. A utility needing phase-specific diagnostics for injected
faults must first request a maintainer model extension. Output-error regression
fixtures must cover failed writes (including `/dev/full`) and treat a signal as
a signal, never as a successful exit. Exact timing or buffering of output under
asynchronous faults is not supplied by the whole-request model.

Host access-time bookkeeping on reads is not a modeled filesystem mutation.
Do not claim an exact physical filesystem frame beyond the existing evaluator's
declared observation policy. Any newly required observation returns the item to
`model_preparation` until maintainers qualify it.

Options listed as outside the initial scope are valid GNU functionality outside
this new task's domain; implementations must not pretend GNU rejects them.
This choice does not narrow any released benchmark. Contributors must preserve
the agreed scope in the description, formal specification, generated profile and
case generator; scope changes require maintainer review.

### Filesystem environment and observations

The mutating filesystem entries use a stable, isolated local Linux filesystem with
regular files, directories, symlinks and hard-link aliases. Use the evaluator's
fixed non-root identity, controlled umask and ordinary mode-bit permissions.
Cross-mount fixtures, access/default ACLs, SELinux/SMACK policy, capabilities,
setgid-directory inheritance, block/character device nodes, resource exhaustion and concurrent
mutation require separate scope/model qualification. Operands stay inside the
fixture tree; do not target the host root or mounts to test a failure.

Each mutating call has `modifies io.fsRegion`. It selects a typed request
containing the pre-filesystem and operation arguments, and returns `ok`, errno
and the complete trusted post-filesystem. The shared
`TrustedFilesystemEffectContractFields` connects that observation to the call;
it does not derive POSIX inode effects from the pathname or prove libc correct.
Utility specifications must express the intended request/operand order, preserve
returned effects, select exact diagnostics and derive the final exit status.
Failure does not erase an earlier successful operand or justify assuming an
unchanged whole filesystem.

Runtime evidence must check namespace entries, node kind, content, modes,
ownership, symlink targets, link counts and alias relationships as applicable.
Compare alias/identity correspondence across independent fixtures, not raw host
inode numbers. The current comparator strips host keys and has a separate identity
transition comparison; exact timestamp comparisons depend on its existing policy.
These new entries do not claim exact cross-run wall-clock timestamp equality.
Their native operations still have real parent/child timestamp effects, retained
in the trusted post-state. A stronger timestamp requirement needs maintainer
observation work before opening that extension; do not silently discard it.

Required GNU differential scenarios below are contributor deliverables. The
focused common-model tests establish only the recorded native success/error
cases, not complete filesystem utility conformance.

### What open status means

Check three things separately: an available API, a sufficient observable contract
for the **declared initial scope**, and a completed utility specification/proof. Open status establishes the first two by
source review and representative contract/native checks. It does not establish
the third. Every contribution must reject the counterexamples in its handoff.

For filesystem effects, the principal relation must bind the operation, arguments,
prestate and supplied result. It cannot be just `ok <==> err == 0`, nor may a
contributor choose arbitrary post-states as witnesses. The IO handle owns the
immutable observation function. POSIX operation correctness remains trusted.
The public mkdir contract additionally constrains successful namespace effects
through `DirectoryValidFilesystemObservations` and `DirectoryCreationEffectFields`.

For early-stopping commands, the whole-read API does not give an incremental
stdin interface. The `od` and `sort` scopes below constrain the affected modes.
Logical stdin consumed by a supplied read is modeled; matching GNU's kernel read
ahead or a shared descriptor's final offset is not established by this API or the
current stdout/stderr/filesystem comparator. Do not claim it from these openings.


### b2sum

| Handoff | Scope |
| --- | --- |
| GNU source | cksum.c: digest_file / digest_check; blake2/b2sum.c |
| Supported behavior | Digest generation; -b, -t, -z and -l digest length; ordered file/stdin operands. |
| Declarative specification | BLAKE2b parameter block, little-endian words, compression equations, final-block flag and requested digest length; exact GNU record escaping. |
| Available API | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| Required counterexamples and errors | Empty input; exact block boundary; wrong length parameter; newline/backslash in names; missing input. |
| Outside initial scope | Check-file verification, tagged records and keyed hashing. |

### base32

| Handoff | Scope |
| --- | --- |
| GNU source | basenc.c: do_encode / do_decode (BASE_TYPE=32) |
| Supported behavior | Default encoding; -d, -i, -w (including zero); zero or one file operand. |
| Declarative specification | Eight output symbols per five input bytes, padding and wrap positions; inverse bit equations with the exact decoded prefix before an invalid suffix. |
| Available API | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostic primitives; pure bit and byte relations. |
| Required counterexamples and errors | Wrong padding; accepting an incomplete final group; losing output before a decode error. |
| Outside initial scope | Other encodings. |

### basenc

| Handoff | Scope |
| --- | --- |
| GNU source | basenc.c: main / do_encode / do_decode |
| Supported behavior | --base16, --base32, --base64; -d, -i, -w; zero or one file operand. |
| Declarative specification | Selected alphabet and bit-block relation; option precedence, padding, wrapping and invalid suffix behavior. |
| Available API | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostic primitives; pure bit and byte relations. |
| Required counterexamples and errors | Conflicting selectors, invalid alphabet, all byte values and wrap boundaries. |
| Outside initial scope | Base32hex, base64url, base2, Z85. |

### cksum

| Handoff | Scope |
| --- | --- |
| GNU source | cksum.c: digest_file; cksum_crc.c: crc_sum_stream |
| Supported behavior | Default POSIX CRC with length and filename; ordered file/stdin operands. |
| Declarative specification | CRC polynomial remainder including the encoded input length and final complement; decimal checksum/length record grammar. |
| Available API | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| Required counterexamples and errors | Omitting the length contribution; empty input; embedded NUL; multiple operands with an intervening failure. |
| Outside initial scope | -a algorithm selection, check files, raw/base64 and tagged output. |

### date

| Handoff | Scope |
| --- | --- |
| GNU source | date.c: main / show_date |
| Supported behavior | Explicit --reference=FILE, -u, and an explicit +%s, +%Y-%m-%d or +%H:%M:%S format. |
| Declarative specification | File modification seconds selected through GetFileTimes; signed epoch rendering or UTC civil-calendar arithmetic with exact separators. |
| Available API | GetFileTimes, output outcomes and diagnostics; pure UTC calendar relations. No new date parser helper is shipped. |
| Required counterexamples and errors | Epoch -1, leap day, directory/symlink references, missing path, missing option value and surplus operands. |
| Outside initial scope | Live-clock output, date parsing, setting the clock, nanoseconds, other formats and time zones. ParseDate delivery is currently Touch-specific. |

### dd

| Handoff | Scope |
| --- | --- |
| GNU source | dd.c: scanargs / dd_copy / apply_translations |
| Supported behavior | Finite stdin to stdout; status=none; iflag=fullblock; bs=N and conv=lcase,ucase,swab (valid combinations), including plain copying. |
| Declarative specification | Byte-index case mapping and adjacent-pair swapping, preserving a final odd byte; ordered composition of requested conversions and exact output prefix. |
| Available API | Finite stream outcomes, output outcomes and diagnostics; GetEnv for dircolors. Transformations remain pure Dafny. |
| Required counterexamples and errors | Odd byte count, conflicting case conversions, repeated operands, invalid block size and failed stdout. |
| Outside initial scope | if/of, seek/skip/count, record padding, encodings, devices, timed progress/statistics and injected short-read faults. |

### dir

| Handoff | Scope |
| --- | --- |
| GNU source | ls.c: decode_switches / print_current_files; ls-dir.c |
| Supported behavior | Explicit -1; -a, -A, -d, -r; stable local paths, stdout capture and C locale. |
| Declarative specification | Directory entry selection and bytewise name ordering, GNU dir escape quoting, operand sections and exit status, using directory and metadata APIs. |
| Available API | OpenDir / ReadDir / CloseDir, GetFileStatus / ReadLink, GetEnv, output outcomes and diagnostics; inspect existing ls model for reusable metadata/time relations. |
| Required counterexamples and errors | Hidden files, symlinks, backslash/control characters in names, repeated operands and absent directory. |
| Outside initial scope | Default columns, terminal layout, recursive listing, color, ACL/context markers and long output. |

### dircolors

| Handoff | Scope |
| --- | --- |
| GNU source | dircolors.c: dc_parse_stream / append_quoted / main |
| Supported behavior | Explicit -b or -c and one configuration file; normal TERM/COLORTERM matching and color/extension records in C locale. |
| Declarative specification | Line grammar, shell selection, ordered active assignments, shell escaping and TERM glob language; no regular-expression engine required. |
| Available API | Finite stream outcomes, output outcomes and diagnostics; GetEnv for dircolors. Transformations remain pure Dafny. |
| Required counterexamples and errors | Duplicate records, inactive TERM blocks, invalid keyword, missing value, shell metacharacters and read failure. |
| Outside initial scope | Implicit SHELL inference, embedded database output and print-ls-colors display mode. |

### fmt

| Handoff | Scope |
| --- | --- |
| GNU source | fmt.c: get_paragraph / fmt_paragraph / base_cost / line_cost |
| Supported behavior | Default; -w, -g, -s, -u; ordered file/stdin operands. |
| Declarative specification | Paragraph/word partition, indentation, exact line-break cost equations and strict tie rule; include the source buffer flush boundaries in the relation. |
| Available API | Finite stream outcomes, output outcomes and diagnostics; GetEnv for dircolors. Transformations remain pure Dafny. |
| Required counterexamples and errors | A legal width-respecting wrap that differs from GNU; equal-cost breaks; very long paragraphs; tabs, sentence spacing and invalid goal and width zero. |
| Outside initial scope | Crown/tagged margins, prefix selection and legacy -WIDTH spelling. |

### join

| Handoff | Scope |
| --- | --- |
| GNU source | join.c: join / check_order / prjoin |
| Supported behavior | Two operands, at most one stdin; -1, -2, -j, -t, -a, -v, -e; --check-order / --nocheck-order. |
| Declarative specification | Ordered field records, equal-key group Cartesian products and unmatched rows; exact order-check detection point and retained output prefix. |
| Available API | Finite stream outcomes, output outcomes and diagnostics; GetEnv for dircolors. Transformations remain pure Dafny. |
| Required counterexamples and errors | Duplicate keys, missing fields, unsorted input after prior output, two stdin operands and empty files. |
| Outside initial scope | Output lists, headers, case folding, NUL records and historical syntax. |

### link

| Handoff | Scope |
| --- | --- |
| GNU source | link.c: main |
| Supported behavior | Exactly two operands; normal option delimiter/help/version handling. |
| Declarative specification | One FilesystemCreateHardLink request binding source/target and prestate, exact diagnostic on failure and normal exit. |
| Available API | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| Required counterexamples and errors | Existing target, directory source, dangling source symlink, remaining alias content/link count and wrong operand count. |
| Outside initial scope | Cross-mount links, devices and privileged directory links. |

### md5sum

| Handoff | Scope |
| --- | --- |
| GNU source | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| Supported behavior | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| Declarative specification | MD5 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Available API | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| Required counterexamples and errors | Empty input; padding boundary; all byte values; newline/backslash in names; missing input and later success. |
| Outside initial scope | Check-file verification and tagged output. |

### mkdir

| Handoff | Scope |
| --- | --- |
| GNU source | mkdir.c: process_file / main; ../gnulib/lib/mkdir-p.c |
| Supported behavior | Default one-directory creation; -v; ordered operands. |
| Declarative specification | `CreateDirectorySpec` with typed `FilesystemCreateDirectory` requests (0777, umask and time); success proves a fresh empty directory and preservation of unrelated state; existential intermediate filesystems; exact success/error/verbose records and exit conjunction. Permission and metadata laws remain native observations. |
| Available API | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| Required counterexamples and errors | Existing name, missing parent, wrong path type, permission denial, trailing slash and earlier success before later failure. |
| Outside initial scope | -p, -m, security contexts, setgid inheritance, ACLs and cross-mount/resource races. |

### mkfifo

| Handoff | Scope |
| --- | --- |
| GNU source | mkfifo.c: main |
| Supported behavior | Default FIFO creation with mode 0666 and process umask; ordered operands. |
| Declarative specification | FilesystemCreateSpecialNode with FifoNode and zero device numbers; ordered outcomes, errors and exit aggregation. |
| Available API | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| Required counterexamples and errors | Existing path, absent parent, permission denial, umask and partial success across operands. |
| Outside initial scope | -m, security contexts, FIFO data transfer and device nodes. |

### mknod

| Handoff | Scope |
| --- | --- |
| GNU source | mknod.c: main (case p) |
| Supported behavior | FIFO form NAME p (including GNU first-character type matching); default mode 0666 and umask. |
| Declarative specification | Same FifoNode request as mkfifo with mknod-specific operand/type grammar and diagnostics. |
| Available API | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| Required counterexamples and errors | Extra major/minor operands for p, unknown type, existing target and absent parent. |
| Outside initial scope | Block/character devices, device numbers, -m and security contexts; these still lack qualified privilege fixtures. |

### od

| Handoff | Scope |
| --- | --- |
| GNU source | od.c: decode_format_string / dump / write_block |
| Supported behavior | Explicit -t x1, o1 or u1; -A, -j, -N, -v, -w; regular file operands (no stdin for bounded reads). |
| Declarative specification | Byte-block partition, offsets, radix rendering, padding and duplicate-row compression over the selected byte interval. |
| Available API | Finite stream outcomes, output outcomes and diagnostics; GetEnv for dircolors. Transformations remain pure Dafny. |
| Required counterexamples and errors | Address radix, partial row, duplicate runs, skip across operands, zero limits and invalid counts. |
| Outside initial scope | Stdin with skip/limits (whole-read API cannot retain an unread suffix), implicit word format, multibyte/float/character formats and legacy offsets. |

### pathchk

| Handoff | Scope |
| --- | --- |
| GNU source | pathchk.c: validate_file_name / portable_chars_only / no_leading_hyphen |
| Supported behavior | -p or --portability (equivalent to -p -P); one or more names. |
| Declarative specification | Portable byte alphabet; nonempty pathname, POSIX path/component byte bounds; optional no-leading-hyphen rule with source error precedence. |
| Available API | GetCwd for lexical realpath; pathchk portability is pure argv processing; output outcomes and diagnostics. |
| Required counterexamples and errors | Empty operand, exactly-at-limit component/path, non-ASCII argv, repeated slashes and leading hyphen. |
| Outside initial scope | Default host pathconf/searchability mode and -P alone. |

### pr

| Handoff | Scope |
| --- | --- |
| GNU source | pr.c: init_parameters / print_files / print_page |
| Supported behavior | Explicit -t; single-column output; -l page length, -d double spacing, -n numbering, -o indentation; file/stdin operands. |
| Declarative specification | Line/page partitions, form-feed boundaries, numbering, spacing and indentation; omit headers/trailers as requested. |
| Available API | Finite stream outcomes, output outcomes and diagnostics; GetEnv for dircolors. Transformations remain pure Dafny. |
| Required counterexamples and errors | Form feed, partial page, unterminated input, tabs, invalid length and multiple files. |
| Outside initial scope | Timestamped headers, multicolumn/merge layouts, custom date formats and terminal behavior. |

### ptx

| Handoff | Scope |
| --- | --- |
| GNU source | ptx.c: initialize_regex / compare_occurs / define_all_fields |
| Supported behavior | Default GNU keyword output; -w width and -g gap; file/stdin input, stdout only; no user regex. |
| Declarative specification | Maximal C-locale alphabetic word intervals; the fixed default sentence-boundary language; keyword ordering with source-position ties, clipping and reference fields. |
| Available API | Finite stream outcomes, output outcomes and diagnostics; GetEnv for dircolors. Transformations remain pure Dafny. |
| Required counterexamples and errors | Repeated identical keywords with different context, punctuation, line breaks, narrow width and invalid gap. |
| Outside initial scope | User regex, break/ignore/only files, traditional mode, roff/TeX, input/automatic references and output files. |

### realpath

| Handoff | Scope |
| --- | --- |
| GNU source | realpath.c: realpath_canon / process_path; ../gnulib/lib/canonicalize.c: canonicalize_filename_mode |
| Supported behavior | Explicit -m -s; -z and -q; one or more nonempty/empty operands in the fixed Linux filesystem namespace. |
| Declarative specification | Absolute lexical component normalization relative to GetCwd; slash/dot/dotdot rules and newline/NUL rendering; empty-path error. |
| Available API | GetCwd for lexical realpath; pathchk portability is pure argv processing; output outcomes and diagnostics. |
| Required counterexamples and errors | A symlink component followed by dotdot must stay lexical; above-root dotdot, repeated separators, empty operand and failed stdout. |
| Outside initial scope | Physical/logical link traversal, existence checks, relative-to/base and alternate platform double-slash roots. |

### rm

| Handoff | Scope |
| --- | --- |
| GNU source | rm.c: main; remove.c: rm / prompt / excise |
| Supported behavior | Explicit -f; optional -v; nonrecursive ordinary files/symlinks and directory-rejection cases; ordered operands. |
| Declarative specification | Typed unlink results, missing-name suppression, directory refusal, dot/dotdot protection and verbose output for successful removals. |
| Available API | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| Required counterexamples and errors | Symlink to directory must remove only the symlink; duplicate operands; missing path; inaccessible parent; earlier successful operand. |
| Outside initial scope | Interactive/default prompting, recursion, -d, secure overwrite, mount traversal and resource races. |

### rmdir

| Handoff | Scope |
| --- | --- |
| GNU source | rmdir.c: remove_parents / main |
| Supported behavior | Default empty-directory removal; -v; ordered operands. |
| Declarative specification | Typed FilesystemRemoveDirectory relation for each operand; GNU attempt/verbose/error order and retained prior effects. |
| Available API | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| Required counterexamples and errors | Nonempty directory, symlink, missing parent, dot/dotdot, permission denial and mixed success. |
| Outside initial scope | -p and --ignore-fail-on-non-empty. |

### sha1sum

| Handoff | Scope |
| --- | --- |
| GNU source | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| Supported behavior | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| Declarative specification | SHA-1 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Available API | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| Required counterexamples and errors | Empty input; padding boundary; all byte values; newline/backslash in names; missing input and later success. |
| Outside initial scope | Check-file verification and tagged output. |

### sha224sum

| Handoff | Scope |
| --- | --- |
| GNU source | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| Supported behavior | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| Declarative specification | SHA-224 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Available API | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| Required counterexamples and errors | Empty input; padding boundary; all byte values; newline/backslash in names; missing input and later success. |
| Outside initial scope | Check-file verification and tagged output. |

### sha256sum

| Handoff | Scope |
| --- | --- |
| GNU source | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| Supported behavior | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| Declarative specification | SHA-256 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Available API | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| Required counterexamples and errors | Empty input; padding boundary; all byte values; newline/backslash in names; missing input and later success. |
| Outside initial scope | Check-file verification and tagged output. |

### sha384sum

| Handoff | Scope |
| --- | --- |
| GNU source | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| Supported behavior | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| Declarative specification | SHA-384 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Available API | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| Required counterexamples and errors | Empty input; padding boundary; all byte values; newline/backslash in names; missing input and later success. |
| Outside initial scope | Check-file verification and tagged output. |

### sha512sum

| Handoff | Scope |
| --- | --- |
| GNU source | cksum.c: digest_file / main (algorithm selected by src/local.mk) |
| Supported behavior | Digest generation; -b, -t, -z; ordered file/stdin operands. |
| Declarative specification | SHA-512 word equations, initial state, padding, bit-length encoding and digest truncation; exact GNU record escaping and file marker. |
| Available API | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| Required counterexamples and errors | Empty input; padding boundary; all byte values; newline/backslash in names; missing input and later success. |
| Outside initial scope | Check-file verification and tagged output. |

### sort

| Handoff | Scope |
| --- | --- |
| GNU source | sort.c: compare / check / sort |
| Supported behavior | Whole-line C byte order; -r, -u, -s, -c, -C, -z; file/stdin operands, stdout output (check mode uses regular files). |
| Declarative specification | Ordered multiset of records (set multiplicities for -u), delimiter normalization and exact first-disorder location; stable ties where relevant. |
| Available API | Finite stream outcomes, output outcomes and diagnostics; GetEnv for dircolors. Transformations remain pure Dafny. |
| Required counterexamples and errors | Dropped duplicates, wrong final delimiter, embedded NUL, first disorder and unique/check interaction. |
| Outside initial scope | Stdin check mode (early-stop consumption needs incremental IO), keys, numeric/month/version/random order, output files, merging and spilling. |

### split

| Handoff | Scope |
| --- | --- |
| GNU source | split.c: lines_rr / main |
| Supported behavior | Explicit -n r/K/N to stdout; optional one file operand or stdin; default newline records. |
| Declarative specification | Select records at indices congruent to K-1 modulo N, preserving exact bytes and the last unterminated record. |
| Available API | Finite stream outcomes, output outcomes and diagnostics; GetEnv for dircolors. Transformations remain pure Dafny. |
| Required counterexamples and errors | K>N, zero N, fewer records than chunks, empty input and binary record contents. |
| Outside initial scope | File-creating modes, filters/subprocesses, byte/line-size partitions, suffix policies and custom separators. |

### sum

| Handoff | Scope |
| --- | --- |
| GNU source | cksum.c: digest_file; sum.c: bsd_sum_stream / sysv_sum_stream |
| Supported behavior | Default BSD checksum; -r and -s; ordered file/stdin operands. |
| Declarative specification | BSD rotate/add congruences or System V byte-sum folding; ceiling block count with the selected 512/1024-byte unit and filename rules. |
| Available API | ReadFileWithOutcome / ReadStdinWithOutcome, output outcomes and diagnostics. Digest arithmetic is contributor-owned; no trusted hash answer primitive. |
| Required counterexamples and errors | Empty input; wraparound; a partial final block; stdin versus named file records. |
| Outside initial scope | Other cksum algorithms and check-file syntax. |

### sync

| Handoff | Scope |
| --- | --- |
| GNU source | sync.c: main / sync_arg |
| Supported behavior | Global no-operand sync; --help/--version and invalid option combinations including -d without operands. |
| Declarative specification | Typed FilesystemSync(AllSyncTargets, SyncAllFilesystems) result; exact CLI diagnostics and exit. Persistence internals stay trusted. |
| Available API | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| Required counterexamples and errors | Conflicting -d/-f and -d without a path; returning success without relating it to the supplied observation. |
| Outside initial scope | All path-targeted modes: adapter lacks GNU write-only-open retry and open/sync/close failure-phase observations. |

### test

| Handoff | Scope |
| --- | --- |
| GNU source | test.c: posixtest / unary_operator / binary_operator |
| Supported behavior | String -n/-z and =/!=; integer -eq/-ne/-lt/-le/-gt/-ge; !, parentheses, -a/-o and GNU argument-count precedence. |
| Declarative specification | A declarative expression grammar and argument-count judgments, decimal integer values and Boolean truth; syntax errors distinct from false. |
| Available API | CliPlan/PlanArgv override, output outcomes and diagnostics; pure expression judgments. |
| Required counterexamples and errors | Empty arguments, negative/oversized integers, ambiguous operator strings, wrong arity and malformed parentheses. |
| Outside initial scope | Filesystem, identity/access, terminal predicates and the separate [ command. |

### truncate

| Handoff | Scope |
| --- | --- |
| GNU source | truncate.c: main / do_ftruncate |
| Supported behavior | Explicit -c -s N with absolute nonnegative decimal size through signed 64-bit maximum; stable regular files/symlinks, directories and missing paths. |
| Declarative specification | Missing-path no-create success; otherwise typed FilesystemTruncate request, absolute size and operand order. Ordinary open/path errors use cannot-open wording; no late truncate/close faults in this scope. |
| Available API | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| Required counterexamples and errors | Missing leaf/parent, shrink/extend with zero fill, aliases, directory/trailing slash, write permission denial and invalid size. |
| Outside initial scope | Default file creation, reference/relative/block sizes, nonregular objects, resource/late operation/close faults and injected failures. |

### tsort

| Handoff | Scope |
| --- | --- |
| GNU source | tsort.c: record_relation / scan_zeros / detect_loop / tsort |
| Supported behavior | Zero or one file/stdin operand; space/tab/newline-separated pairs; self pairs, duplicate edges and cycles; legacy -w no-op. |
| Declarative specification | Ordered graph judgments: initial zero nodes by strcmp order; FIFO eligibility, successors in reverse insertion order; exact deterministic cycle selection/removal and diagnostics. |
| Available API | Finite stream outcomes, output outcomes and diagnostics; GetEnv for dircolors. Transformations remain pure Dafny. |
| Required counterexamples and errors | Any different valid topological order; repeated edge counts; NUL within a token (C-string key); odd token count and cycle output. |
| Outside initial scope | No additional transformation modes; late read/close faults follow the common exclusion. |

### unexpand

| Handoff | Scope |
| --- | --- |
| GNU source | unexpand.c: next_file / unexpand |
| Supported behavior | Default leading blanks; -a, --first-only, -t tab lists including continuation; ordered file/stdin operands. |
| Declarative specification | Column-position and tab-stop relation preserving nonblank bytes; backspace/newline effects and GNU option precedence. |
| Available API | Finite stream outcomes, output outcomes and diagnostics; GetEnv for dircolors. Transformations remain pure Dafny. |
| Required counterexamples and errors | Existing tabs, backspace, irregular stops, last unterminated line, invalid stop order and option interaction. |
| Outside initial scope | Non-C locale display widths. |

### unlink

| Handoff | Scope |
| --- | --- |
| GNU source | unlink.c: main |
| Supported behavior | Exactly one operand, including symlink operands. |
| Declarative specification | One FilesystemUnlink request without terminal dereference; preserve returned post-state and select GNU failure diagnostic. |
| Available API | Typed filesystem request/result calls selected by this entry; path/kind queries where needed, output outcomes and diagnostics. |
| Required counterexamples and errors | Directory rejection, missing target, symlink target preservation and remaining hard-link alias. |
| Outside initial scope | Recursive removal and open detached handles. |

### vdir

| Handoff | Scope |
| --- | --- |
| GNU source | ls.c: decode_switches / print_long_format; ls-vdir.c |
| Supported behavior | Explicit -n --time-style=long-iso; -a, -A, -d, -r; C locale and UTC0. |
| Declarative specification | Numeric ownership, mode, links, size, UTC modification time, escaping, ordered rows and width/total rules from observable metadata. |
| Available API | OpenDir / ReadDir / CloseDir, GetFileStatus / ReadLink, GetEnv, output outcomes and diagnostics; inspect existing ls model for reusable metadata/time relations. |
| Required counterexamples and errors | Hard-link count, dangling symlink, different field widths, epoch boundary and missing operand. |
| Outside initial scope | Name-service output, default locale time style, devices, ACL/context markers, recursive listing and terminal/color features. |


## Candidates awaiting model work

For a `model_preparation` item, read `remaining_preparation` in [TODOLIST.csv](../TODOLIST.csv). That field preserves the specific blocker, such as missing identity lookup or process execution. An available libc function does not create a Dafny wrapper. Ask maintainers to prepare and review the missing contract before treating the scope as open.

The openings above were recorded against core revision `1f52dd00e39906bb6970746fb103beff9219072e` plus the additive quoting wrapper, and GNU revision `2cf491412c199e2211880ec3f4ba387026638a33`. Check current declarations before relying on historical evidence.
