# Dafnyutils

Dafnyutils is a benchmark repository that tests whether agents can write code and
proofs from formal specifications of GNU coreutils written in Dafny. It includes
a model of system state as well as program logic. This model lets us specify and
verify effects on the system. We check the model through differential testing:
we compare its behavior with the original GNU coreutils binaries.

Read [CONTRIBUTING.md](CONTRIBUTING.md) for the contribution process and required PR evidence. Use these four guides for detailed tasks:

| Your task | Guide |
| --- | --- |
| Add a utility from setup through review | [Add a utility](docs/adding-utilities.md) |
| Understand shared contracts and what the proof assumes | [Use the core API](docs/core-api.md) |
| Run generated cases and reproduce mismatches | [Use the fuzzer](docs/fuzzing.md) |
| Port upstream GNU scenarios into utility Python tests | [Add test cases](docs/adding-test-cases.md) |

Follow the setup steps below before using any guide. [TODOLIST.csv](TODOLIST.csv) records utility status and initial scope.

`bench/utils/` contains utility tasks, `bench/algorithm/` contains algorithm tasks, `bench/core/` supplies shared contracts, and `src/` contains authoring and evaluation tooling. `coreutils/` is a pinned upstream submodule. `dafny/` contains the Dafny source used by this project. Builds create `_build/`.

Runtime parity, Dafny verification and human specification review provide different evidence; none replaces the others. Follow [repository instructions](AGENTS.md), [bench rules](bench/AGENTS.md) and [Dafny style](DAFNYSTYLE.md).

## Setup

### Prerequisites

Install these tools on your host before you start:

- Git.
- Docker, with the Docker engine running.
- VS Code with the Dev Containers extension, or the Dev Container CLI for terminal use.

Use the [development container](.devcontainer/devcontainer.json) included in this
repository. The container has been tested on Linux x86-64 (Ubuntu 24.04).
Other architectures have not been tested.

We use a version of Dafny changed for dafnyutils. Its source is included in
`dafny/`. You must use the Dafny built inside the development container, available
at `/usr/bin/dafny-benchmark` in the container.

### Start the container

In VS Code, open this checkout and select **Dev Containers: Reopen in Container**.
Wait for setup to finish.

For terminal use, run:

```sh
# On the host, from this repository's root:
devcontainer up --workspace-folder .
```

Expected final output (after build/setup logs; IDs vary):

```text
{"outcome":"success","containerId":"<container-id>","remoteUser":"vscode","remoteWorkspaceFolder":"/workspace/dafnyutils"}
```

```sh
devcontainer exec --workspace-folder . zsh
```

Expected result: an interactive shell in the container. The prompt style varies:

```text
<container prompt> /workspace/dafnyutils $
```

The CLI uses the same configuration and setup script as VS Code.
The container name is `<USER>-dafnyutils`, where `<USER>` is the value of `USER`
on your host. For example, if `USER` is `duncan`, the name is `duncan-dafnyutils`.
Inside the container, the repository is `/workspace/dafnyutils`.

Setup installs Python 3.12, .NET 8, Rust, Z3, tmux and native build tools. It creates
`.venv`, installs the Python development and contributor dependencies, initializes
the pinned GNU submodules, and builds the bundled Dafny. Budget 10–30 minutes for
initial downloads and compilation; this is an estimate, not a time limit.
GNU binaries and the fuzzer execution image are built later by the task guides.
A clean Linux x86-64 setup used up to about 10 GiB of memory, excluding the image build.

Run repository commands inside the container. Its terminal already puts `.venv/bin`
on `PATH`; in a manually opened shell, activate it explicitly:

```sh
cd /workspace/dafnyutils
source .venv/bin/activate
make check-environment
```

Expected output (versions and the package list vary):

```text
Checking: python3 --version
Python 3.12.<patch>
...
No broken requirements found.
...
Checking: tmux -V
tmux <version>
...
Dafny program verifier finished with 4 verified, 0 errors

Environment ready. The StreamCopy result checks the verifier, not a utility proof.
```

`make check-environment` checks Python dependencies, Docker/Compose access, Rust,
Z3, tmux and the bundled `dafny-benchmark`. It verifies the [StreamCopy client](tools/fixtures/contributor/StreamCopy.dfy). Success ends with
`Environment ready` and a verifier result of `4 verified, 0 errors`. This checks
the tools. Setup runs the same check automatically.

## Repository structure

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
├── dafny/                 # Bundled Dafny source customized for this project
├── docker/                # Task and evaluation container build definitions
├── docs/                  # Contributor guides and API documentation
├── example/               # Worked examples
│   └── copy/              # Stream-copy specification, implementation and proof
├── src/                   # Python authoring, verification and evaluation tooling
│   ├── analysis/          # Evaluation result analysis
│   ├── benchmarks/        # Task discovery, scaffolding, builds and validation
│   ├── evaluation/        # Evaluation environments, task preparation and scoring
│   └── runtime/           # Runtime support for evaluation
├── tools/                 # Build scripts and repository maintenance tools
│   ├── benchmark_templates/ # Templates for new utility and algorithm tasks
│   └── coreutils_fuzzer/  # Generated-input comparison with GNU coreutils
└── _build/                # Generated build artifacts
```

## Example: Test and verify a small program

This example copies standard input to standard output. It shows the same
Spec → Core → Proof → entry structure as a utility contribution, with only two
IO calls. The complete files are in
[`example/copy/`](example/copy).

Use the [development container](#setup). Run the commands below
from `/workspace/dafnyutils` with `.venv/bin` on `PATH`.

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
    C.ReadStdinWithOutcomeSpec(
      old(io.stdin()), old(io.trustedStreams()), io.stdin(), data, readErr) &&
    C.WriteStdoutWithOutcomeSpec(
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
  var data;
  data, readErr := io.ReadStdinWithOutcome();
  var committed;
  committed, writeErr := io.WriteStdoutWithOutcome(data);
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
It uses the repository's `--library` setting for `bench/core`: those existing
contracts are assumptions of this example, not newly proved native IO code.
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

For a local exercise, change the exit assignment in `Copy.dfy` to:

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

### 9. Use the same steps after creating a utility scaffold

The [utility guide](docs/adding-utilities.md#create-the-files) creates intentionally
unfinished files. Fill them in using this order:

| Example | New utility |
| --- | --- |
| Behavior list in step 1 | Fill `<utility>.md` and get maintainer scope review |
| `CopySpec.CopyResult` and `Spec` | Replace false predicates in `<Utility>Spec.dfy` with the required IO and output relations |
| `CopyCore.CopyInput` | Replace the failing Core body; prove what its result satisfies |
| `CopyProof.CopyResultImpliesSpec` | Prove that the implementation's result satisfies the main specification |
| `Copy.RunCore` | Keep the direct `ensures Spec(...)` on the utility entry |
| `CopyCli.Main` | Keep the generated shared runner; complete Schema, parsing and early exits |
| `Tests.py` | Replace placeholder tests with real GNU comparisons and retain the generated proof tests |

Then register the utility's fuzzer generator and follow the full
[validation and submission steps](docs/adding-utilities.md#validate-and-submit).
This example has no benchmark definition or fuzzer registration and does not
count as a completed utility contribution.
