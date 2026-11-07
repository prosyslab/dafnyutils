# Dafnyutils

Dafnyutils is a benchmark repository that tests whether agents can write code and
proofs from formal specifications of GNU coreutils written in Dafny. It includes
a model of system state as well as program logic. This model lets us specify and
verify effects on the system. We check the model through differential testing:
we compare its behavior with the original GNU coreutils binaries.

Read [CONTRIBUTING.md](CONTRIBUTING.md) for the contribution process and required PR evidence. Use these guides for detailed tasks:

| Your task | Guide |
| --- | --- |
| Add a utility from setup through review | [Add a utility](CONTRIBUTING.md#extending-benchmark) |
| Understand shared contracts and what the proof assumes | [Use the core API](docs/core-api.md) |
| Understand each utility's implementation and main proof idea | [Read the utility guide](docs/utility-guide.md) |
| Run generated cases and reproduce mismatches | [Use the fuzzer](docs/fuzzing.md) |
| Port upstream GNU scenarios into utility Python tests | [Add test cases](docs/adding-test-cases.md) |
| Integrate an agent with the public task and result wire | [Use the agent protocol](docs/agent-protocol.md) |

Follow [repository instructions](AGENTS.md), [bench rules](bench/AGENTS.md) and [Dafny style](DAFNYSTYLE.md).

## Setup

Use the [development container](.devcontainer/devcontainer.json) for every command
in this repository. In VS Code, select Dev Containers: Reopen in Container.

## Repository structure

Utility Dafny sources live under `bench/utils/<utility>/Spec/`, `Impl/` and
`Proof/`. The task directory retains its manifest, description, tests, Makefile
and project configuration. Algorithm sources retain their flat layout. See the
[source responsibilities](docs/benchmark-layout.md) for details.

```text
dafnyutils/
├── .devcontainer/         # Development container and setup scripts
├── .githooks/             # Repository Git hooks
├── .github/               # CI workflows and pull request template
├── .vscode/               # VS Code and Dafny extension settings
├── bench/                 # Benchmark definitions and Dafny sources
│   ├── algorithm/         # Algorithm tasks
│   ├── core/              # Shared system models, IO contracts and native adapters
│   └── utils/             # GNU coreutils task specifications, implementations and proofs
├── coreutils/             # Pinned upstream GNU coreutils submodule
├── docs/                  # Contributor guides and API documentation
├── example/               # Worked examples
│   └── copy/              # Stream-copy specification, implementation and proof
├── src/benchmarks/        # Problem definitions, schemas, paths and discovery
├── src/tools/             # Importable `tools` package: contributor commands and test helpers
│   ├── contribution/      # Local validation, task builds, proofs and contributor checks
│   ├── scaffold.py        # Create incomplete benchmark contributions
│   └── test_support.py    # Helpers that benchmark Tests.py files import
├── tools/                 # Build scripts, templates and the fuzzer (not importable)
│   ├── benchmark_templates/ # Templates for new utility and algorithm tasks
│   └── coreutils_fuzzer/  # Generated-input comparison with GNU coreutils
└── _build/                # Generated build artifacts
```

## Example: Test and verify a small program

This example copies standard input to standard output. It shows the same
Spec → Core → Proof → entry structure as a utility contribution, with only two
IO calls. The complete files are in
[`example/copy/`](example/copy).

Run the commands below in the development container from this repository's root.

### 1. Choose the behavior

Write down the behavior before implementing it:

- Read finite bytes from standard input, including NUL and non-UTF-8 bytes.
- Write the bytes that were read, even if the read ended with an error.
- Return exit status 0 only if both reading and writing succeed; otherwise return 1.
- A failed write may leave a prefix of the requested bytes on standard output.
- Do not write diagnostics or change files.

The example has no options or file operands. It is a teaching program, not a
GNU `cat` contribution. A real utility also needs its approved option, diagnostic
and error behavior, GNU comparison tests and generated fuzz cases.

### 2. State the specification

Open [CopySpec.dfy](example/copy/CopySpec.dfy).
`CopyResult` describes the input consumed and output written using the existing
contracts in `bench/core/IOContract.dfy`:

```dafny
twostate predicate CopyResult(io: BenchIO.IO, readErr: int, writeErr: int)
  reads io.stdinRegion, io.stdoutRegion, io.trustedStreamsRegion
{
  exists data: BenchWorld.Bytes, committed: nat ::
    C.ReadStdinSpec(
      old(io.stdin()), old(io.trustedStreams()), io.stdin(), data, readErr) &&
    C.WriteStdoutSpec(
      old(io.stdout()), old(io.trustedStreams()), io.stdout(), data, committed, writeErr)
}
```

The same `data` connects the two contracts. The read contract says it is the
consumed input prefix. The write contract says that exactly `committed` bytes
from its beginning were appended to stdout. Both contracts include the observed
error code. `exists` states that these values describe the result; it does not
run an algorithm or choose a different IO result.

`old(...)` refers to the state before the call. `reads` lists the state this
predicate uses, including the IO results supplied by the shared library.
`twostate` allows the predicate to compare the state before and after a call.

The main `Spec` adds the exit policy and makes the successful result explicit:

```dafny
twostate predicate Spec(io: BenchIO.IO, exit: int)
  reads io.stdinRegion, io.stdoutRegion, io.trustedStreamsRegion
{
  (exists readErr: int, writeErr: int ::
    CopyResult(io, readErr, writeErr) &&
    exit == (if readErr == 0 && writeErr == 0 then 0 else 1)) &&
  (exit == 0 ==>
    io.stdin() == [] && io.stdout() == old(io.stdout()) + old(io.stdin()))
}
```

On success, input is consumed and its bytes are appended unchanged. On failure,
`CopyResult` still constrains the consumed and written prefixes. The specification
does not assume that IO succeeds.

### 3. Implement the IO calls

[CopyCore.dfy](example/copy/CopyCore.dfy) contains the code:

```dafny
method CopyInput(io: BenchIO.IO) returns (readErr: int, writeErr: int)
  modifies io.stdinRegion, io.stdoutRegion
  ensures CopySpec.CopyResult(io, readErr, writeErr)
{
  var read := io.ReadStdin();
  var data := C.ReadResultData(read);
  readErr := C.ResultErrno(read);
  var write := io.WriteStdout(data);
  writeErr := C.ResultErrno(write);
}
```

`modifies` permits changes only to the two stream regions. There is no extra
assertion saying stderr or the filesystem stays unchanged: the narrow list
already guarantees that. The method promises `CopyResult` for every returned
result, including read and write failures.

### 4. Connect the result to the main specification

[CopyProof.dfy](example/copy/CopyProof.dfy) proves that
`CopyResult`, together with the chosen exit status, implies `Spec`. Its lemma
body is empty because Dafny can prove this small implication from the library
contracts. An empty lemma body is still checked; it is not an assumed fact.

[Copy.dfy](example/copy/Copy.dfy) combines the pieces:

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

The entry method itself promises `Spec`. The lemma helps prove that promise.
The Spec file imports no implementation or proof file.

[CopyCli.dfy](example/copy/CopyCli.dfy) gets the process IO
handle with `BenchIO.Process()`, calls `RunCore` and passes its result to
`BenchIO.Exit`. The build uses the existing `bench/core/IOExtern.cs` adapter
to connect the Dafny calls to real process streams.

### 5. Verify every example file

```sh
make -C example/copy verify
```

Expected output, exit 0 (the library warnings and make command lines are omitted):

```text
...
Dafny program verifier finished with 10 verified, 0 errors
...
```

The target uses `--verify-included-files` to check all five `Copy*.dfy` files.
It fixes the Boogie random seed to 42, as the task verifier does, so the same
sources give the same result on every run. It uses the repository's `--library`
setting for `bench/core`: those existing contracts are assumptions of this
example, not newly proved native IO code.
Dafny warns that these are source-library files. The target allows those warnings,
as the repository's utility verifier does. It does not skip any example proof.

The Dafny methods have no loops or recursion and prove termination of their own
code. Actual stream reads can wait for input; completion depends on the supplied
IO contracts and a finite input that reaches EOF or an error.

### 6. Build and run the program

```sh
make -C example/copy build
```

Expected output, exit 0 (other build lines omitted):

```text
...
Dafny program verifier did not attempt verification
...
```

This creates `_build/tutorial-copy/copy.dll`. Build and verification are separate
steps, so a successful build does not replace step 5.

```sh
printf 'hello\n' | dotnet _build/tutorial-copy/copy.dll
```

Expected output, exit 0:

```text
hello
```

### 7. Test real IO, including failures

```sh
make -C example/copy test
```

Expected output, exit 0 (build lines omitted):

```text
...
4 passed in <seconds>s
...
```

[Tests.py](example/copy/Tests.py) checks empty input, all 256
byte values, a write to `/dev/full`, and a directory supplied as stdin. Tests
check stdout, stderr and exit status where applicable. The two error tests must
return 1, not silently report success. These Linux tests exercise the actual
adapter; they do not inject every possible partial read or write failure. The
proof constrains those partial results under the shared IO contracts.

### 8. See a bug fail both checks

For a exercise, change the exit assignment in `Copy.dfy` to:

```dafny
exit := 0;
```

This bug reports success even when reading or writing fails.

```sh
make -C example/copy verify
```

Expected output, exit 2 from make (other lines omitted):

```text
...
Dafny program verifier finished with 9 verified, 1 error
...
```

The failing condition is the lemma's requirement that the exit status matches
the two error results. Now check the executable too:

```sh
make -C example/copy test
```

Expected output, exit 2 from make (build output and failure details omitted):

```text
...
2 failed, 2 passed in <seconds>s
...
```

The two failure cases catch the wrong exit status; the two successful IO cases
still pass. Restore the original assignment before continuing:

```dafny
exit := if readErr == 0 && writeErr == 0 then 0 else 1;
```

```sh
make -C example/copy verify test
```

Expected output, exit 0 (other lines omitted):

```text
...
Dafny program verifier finished with 10 verified, 0 errors
...
4 passed in <seconds>s
...
```
