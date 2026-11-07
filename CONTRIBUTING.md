# Contributing to Dafnyutils

Submit a focused change with reproducible code verification and fuzzing results. Follow the utility contribution workflow below, then report the results in the [pull request template](.github/pull_request_template.md).

## Contents

- [Extending benchmark](#extending-benchmark)
  - [Set up your checkout](#set-up-your-checkout)
  - [Find the right files](#find-the-right-files)
  - [Build one contribution](#build-one-contribution)
    - [Create the files](#create-the-files)
    - [Define the observable behavior](#define-the-observable-behavior)
    - [Complete the generated files](#complete-the-generated-files)
    - [Specify first, then implement and prove](#specify-first-then-implement-and-prove)
    - [Add differential cases and a generator](#add-differential-cases-and-a-generator)
  - [Validate and submit](#validate-and-submit)
    - [Check the definition](#check-the-definition)
    - [Build, test and verify](#build-test-and-verify)
    - [Open a pull request](#open-a-pull-request)
- [Prepare the change](#prepare-the-change)
- [Coding style](#coding-style)
  - [Python](#python)
  - [Dafny and proofs](#dafny-and-proofs)
  - [Tests and documentation](#tests-and-documentation)
- [Naming conventions](#naming-conventions)
- [Commit messages](#commit-messages)
- [Show verification and fuzzing results](#show-verification-and-fuzzing-results)
- [Open the pull request](#open-the-pull-request)

## Extending benchmark

Contribute a utility by writing its behavior contract, implementing it, proving
the entry point and comparing the executable with the pinned GNU binary. Define
its scope within the system that `bench/core/IO.dfy` models, then submit the code
and validation evidence for human review.

This guide follows `base32`, an open utility with byte-stream input. The scaffold is a starting point, not a working implementation. Use the existing `base64` and `cat` projects to learn the structure; do not copy their specifications as the meaning of `base32`.

First try the [small IO example](README.md#example-test-and-verify-a-small-program) if you have not connected
Spec, Core, Proof and a process entry before. It includes working files and
commands for checking both the proof and the executable.

### Set up your checkout

Use the [development container](README.md#setup) for every
command in this guide, including the scaffold command below. Run them from this
repository's root.

The container mounts the host's Docker socket because the fuzzer and `check` start
containers on the host's Docker. Any process in the container can therefore control
the host's Docker, so use it only on a machine where you accept that.

### Find the right files

| Path | Purpose |
| --- | --- |
| `bench/utils/<utility>/` | Utility definition, description, oracle tests and local Makefile; Dafny sources under `Spec/`, `Impl/` and `Proof/` |
| `bench/core/` | System model, native contracts, protocol types and trusted runtime adapters |
| `bench/utils/<utility>/Impl/CliSupport.dfy`, `bench/algorithm/<number>/CliSupport.dfy` | Fixed task-local parser and process runner protocol |
| `coreutils/` | Pinned upstream GNU source and tests; keep its revision fixed |
| `src/tools/scaffold.py` | Create incomplete contributions from the templates in `tools/benchmark_templates/` |
| `tools/benchmark_templates/common/` | Common incomplete Dafny layout used by both scaffold kinds |
| `tools/coreutils_fuzzer/` | Differential runner, generators and comparison logic |
| `src/benchmarks/` | Definitions, paths, discovery and selection |
| `src/tools/` | Local validation, builds, proof commands and executable test helpers (imported as `tools`) |
| `_build/` | Generated binaries and reports, created by build/check commands |

Read [bench rules](bench/AGENTS.md) and [Dafny style](DAFNYSTYLE.md) before editing Dafny.
Keep the scope in the utility's Markdown file, as described in
[Prepare the change](#prepare-the-change).

### Build one contribution

#### Create the files

Choose an `open_for_contribution` row in [TODOLIST.csv](TODOLIST.csv), then
read the [implementation notes](docs/implementation-notes.md) and the
[core API guide](docs/core-api.md). This walkthrough uses `base32`.
Create the scaffold **before** creating its directory or scope document:

```sh
python3 -m tools.scaffold --kind coreutils --id base32
```

The command uses this tool's repository as its default root, even from another
working directory. Pass `--root <checkout>` to use another checkout and its
templates. It copies the common templates and the selected kind's templates;
`--kind algorithm --id algorithm-123` creates `bench/algorithm/123`.
Expected duration: less than a second for the current templates.

Expected output, exit 0:

```text
bench/utils/base32
scaffold is incomplete; replace TODO content and source status before validation
```

If the directory already exists, inspect it and continue that contribution; the
tool refuses to overwrite it. Do not delete someone else's work to rerun this command.

#### Define the observable behavior

Specify the utility in as much detail as the system modeled by
`bench/core/IO.dfy` can express. The row's `scope` column in
[TODOLIST.csv](TODOLIST.csv) is the minimum. For `base32` it lists the default
encoding, `-d`, `-i`, `-w` (including zero) and zero or one file operand. Also
cover every other option, operand form and error path of the GNU utility whose
observable behavior the model can express, such as `--help`, `--version` and
invalid options.

Settle open questions from the pinned GNU source, the upstream GNU tests, the
exact `IO.dfy` declarations and `IOContract.dfy` predicates, and
[Trust limits and API changes](docs/core-api.md#trust-limits-and-api-changes).
Record each scope decision and its evidence in the scope document.

Fill the generated `bench/utils/base32/base32.md` before implementation:

| Question | Example answer for base32 |
| --- | --- |
| What is the source? | Pinned `coreutils/src/basenc.c`, built with `BASE_TYPE=32`; record the submodule commit |
| What is accepted? | Finite raw bytes from stdin or one regular file; every GNU `base32` option that `IO.dfy` can model |
| What is observed? | Exact output and error bytes, exit behavior, and modeled input consumption |
| Which environment? | Linux, C locale and UTC0; the filename and IO limits in the [stream handling rules](docs/implementation-notes.md#handle-stream-errors-and-partial-output) |
| Which errors matter? | Invalid alphabet/padding/options; missing or inaccessible file; partial progress followed by failure |
| What is trusted? | Named `bench/core` IO and diagnostic contracts, with their recorded revision |
| What remains to prove? | Bit-block relation, padding, wrapping, decoding prefix, diagnostics and exit policy |

For each accepted input, make the specification determine every observation
that the [model exposes](docs/core-api.md#values-and-observations) and the GNU
utility defines:

- exact stdout and stderr bytes, including diagnostic text, quoting and order;
- the exact exit status, not only success or failure;
- the consumed input prefix and the output committed before a read or write error;
- each modeled error outcome that the utility reports differently;
- for a utility that changes files, the resulting filesystem, including the
  effects left after a failure.

Leave a result open only where GNU or the IO contract permits more than one, such
as the order of environment enumeration. Do not replace an exact value with "an
error occurred" or "the exit status is nonzero".

Check the current API in `bench/core/IO.dfy` before choosing the options to implement.
If an option cannot be implemented with this API, leave it out of the contribution.
List each such option in the utility's scope document and in the PR's
**Options left out due to IO.dfy** section. Explain what API support is missing.
Write `None` in that PR section if no options were left out for this reason.

Do not extend shared IO contracts or runtime adapters to add a left-out option;
maintainers own them. Report the missing operation in the PR instead. Do not
narrow the scope without recording it, assume successful IO, or add an
unchecked native call to make a proof pass.

#### Complete the generated files

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
capabilities:
  gnu_reference: true
  fuzzer: true
```

Here `verified` means the source name, URL and license have been checked. It does not mean the utility or its proof has passed. New contributions cannot use `legacy-unverified`. Do not add invented fields for evaluator paths: the loader derives them from the task ID and directory. Capabilities select optional oracle providers; they do not change the candidate layout or execution interface.

Complete these generated files:

| File | What to put there |
| --- | --- |
| `base32.md` | The scope you defined: input, option, environment, output and error behavior; scope decisions with evidence; options left out due to IO.dfy; examples, source revision, and license |
| `Spec/Base32Schema.dfy` | CLI schema/configuration, raw command types and decode behavior |
| `Spec/Base32Spec.dfy` | Declarative observable relation and fixed help/version/error text |
| `Impl/Base32Core.dfy` | Executable algorithms and the values they construct to satisfy the specification |
| `Proof/Base32Proof.dfy` | Lemmas connecting the implementation summary to the specification |
| `Impl/Base32.dfy` | Shared runner hooks; `RunCore` directly ensures the main `Spec(...)` |
| `Impl/Base32Cli.dfy` | Process entry using `BenchIO.Process()`, the shared runner and `BenchIO.Exit` |
| `Tests.py` | Evaluator-owned observable behavior and differential cases |
| `dfyconfig.toml`, `Makefile` | Existing project/build conventions from the scaffold |

The scaffold already connects the CLI to a class extending
`BenchItem.BenchmarkItemTwostate<Base32CmdRaw>`. It passes the parsed command and
IO handle through Core, the connecting lemma, and the entry postcondition.
Replace the raw-command wrapper and parser TODOs with the utility's actual rules.
Use only the IO regions it reads or changes; the supplied stream regions are a
starting point, not permission to widen an existing task's frame.

Utility sources use `Spec/`, `Impl/` and `Proof/` inside each task directory.
Algorithm sources retain their flat class-prefixed layout and the same `BenchmarkItem`
interface, build target, runtime test stage and verification gate. Their CLI
reads the problem input from standard input and parses it before calling
`RunCore(raw, io)`. Keep the original mathematical answer relation in Spec and
connect it to the observable output, explicit IO failures and exit status.
See [the common benchmark layout](docs/benchmark-layout.md) for the complete
interface and capability contract.

The false Spec/CoreSummary relations and failing assertions deliberately block
verification. Replace them with the specified behavior and its proofs, not `true`, `assume`,
or verification skips. `Main` uses `decreases *` because the shared runner permits
nontermination; this does not prove CLI termination. The generated Core method
still has to terminate. Review help/version/parse-error plans separately.

#### Specify first, then implement and prove

State the result as a mathematical relation. For example, a valid base32 block relates five input bytes to eight alphabet symbols through bit equations. Padding and line breaks have separate position rules. Decoding must constrain the bytes emitted before an invalid suffix. A second copy of the encoder loop is not an independent specification.

Use the [core API guide](docs/core-api.md) for IO, byte conversion and reusable lemmas. Keep algorithms in Core, proof connections in Proof, and fixed user-facing text in Spec. Spec must not import Core, Proof or CLI. Keep this required condition on the entry method:

```dafny
ensures Spec(raw, io, exit)
```

This is a contract line, not a complete method. Use the actual argument types and frames of your utility. A separate `CoreSummary ==> Spec` lemma helps prove this condition; it does not replace it. Use narrow `reads` and `modifies` clauses. Do not add `assume`, trust annotations, or verification skips.

The shared runner calls `RunCore` only for a run plan. Help, version and parse errors may use an early-exit plan. Review and test that CLI path separately; a `RunCore` proof alone does not prove every early-exit branch.

#### Add differential cases and a generator

Follow [Add test cases](docs/adding-test-cases.md) to port named scenarios from the upstream GNU test suite into `bench/utils/<utility>/Tests.py`, reusing its fixtures and runner helpers. Each runtime behavior case must run equivalent arguments, input and setup against the pinned executable built from the upstream C implementation and the built Dafny executable. Compare their stdout, stderr, exit status and, for mutating commands, filesystem effects. Record the upstream test path and case name. Include normal, malformed-input and partial-effect cases; reject plausible wrong outputs as part of specification review. The `@pytest.mark.dafny_verify` cases in the same file are separate proof checks.

For a new utility, start with [the generated test adapter](docs/adding-test-cases.md#start-a-new-utility-test-file).
It includes the build fixture, strict comparison helper, and three
`@pytest.mark.dafny_verify` cases for Entry/Core/Proof. Keep those proof cases:
The contributor gate runs them after project verification. Without them pytest selects
no proof tests and exits 5, even if `make verify` succeeded.

For a new utility, add its generator under `tools/coreutils_fuzzer/src/fuzz/input/generators/`, declare the module in `generators/mod.rs`, and register `GENERATOR` in `src/utils/capabilities.rs`. Reuse `PatternInputGenerator` and the shared argument-pattern engine. See [generator extension](docs/fuzzing.md#support-a-new-utility) for the concrete registration points. A case JSON file alone does not register a new utility.

Keep evaluator cases, oracle code and reference answers out of public task resources. Authors can inspect public GNU tests during maintenance; an evaluated agent may only read material allowed by that run's protocol.

For fixed stdin cases, declare `capabilities.fixed_cases: true` and retain the
original raw input/output dataset in evaluator-owned `cases.json`. The generated
`Tests.py` runs each input through the executable; legacy Python parser text in
the dataset is inert. Select an `output_contract` when valid outputs have several
representations or witnesses. All tasks execute `implementation_tests`; a missing
or empty fixed case set is an error, not an inapplicable test stage.

### Validate and submit

Run the commands in this section in the development container from this
repository's root. The contributor gate additionally builds, executes and proves
benchmark tasks.

#### Check the definition

```sh
# Expected duration: Seconds for local metadata and path checks; no native toolchain needed.
# Success criteria: Exit 0 and base32: valid.
python3 -m tools.contribution validate base32
```

Expected output for a completed utility, exit 0:

```text
base32: valid
```

Expected output for an untouched scaffold, exit 1:

```text
base32: source details are incomplete
```

This validates YAML/schema, completed source metadata, required files and paths.
The untouched scaffold must fail with `source details are incomplete`; that is
an expected unfinished state. This command does not analyze the Dafny entry
contract, prove the specification or generate a public task profile. Review the
specification, its includes and the intended editable/support boundary yourself;
keep tests and reference answers out of candidate-visible resources. The
integration repository owns analysis and public-profile release checks.

#### Build, test and verify

```sh
# Expected duration: Unknown; first GNU bootstrap/build depends on downloads and CPU.
# Success criteria: Exit 0 and _build/coreutils/src/base32 is executable.
make build-coreutils
```

Expected output, exit 0 (paths and build steps vary):

```text
...
make[1]: Leaving directory '/workspace/dafnyutils/_build/coreutils'
```

This builds the pinned original utilities. It may need network access for build inputs.

```sh
# Expected duration: Unknown; requires a complete Base32 implementation and .NET.
# Success criteria: Exit 0 and _build/bench/base32_bench.dll exists.
make -C bench/utils/base32 build
```

Expected output, exit 0:

```text
Dafny program verifier did not attempt verification
make: Leaving directory '/workspace/dafnyutils/bench/utils/base32'
```

```sh
# Expected duration: Unknown; depends on the new case population and Docker setup.
# Success criteria: Exit 0 with real, non-skipped runtime cases passing.
make -C bench/utils/base32 test
```

Expected output shape, exit 0 (names and counts depend on your cases):

```text
Base32Tests.<case>: PASSED
...
<count> passed, <count> deselected in <seconds>s
make: Leaving directory '/workspace/dafnyutils/bench/utils/base32'
```

```sh
# Expected duration: Unknown; depends on the conditions to prove and solver time.
# Success criteria: Exit 0 and zero Dafny verification errors for the project and all files it includes.
make -C bench/utils/base32 verify
```

Expected output, exit 0:

```text
Dafny program verifier finished with <count> verified, 0 errors
```

These commands check compilation, executable behavior and proof separately.
The local verifier selects all project `.dfy` files directly, verifies included
files, disables standard libraries, fixes the Boogie random seed to 42 and
supplies explicit core dependencies.
It does not inherit the project's `no-verify = true` build setting.
A build is not verification, and matching a finite test set is not proof of the
specification. On a timeout, locate the expensive condition and add local proof
guidance before considering a larger time limit.

The gate's `fuzzer` check runs both executables in a container on the host's Docker.
If the host has no fuzz image, the first run builds it, which takes a few minutes.

```sh
# Expected duration: Unknown; includes builds, runtime tests, 20 fuzz cases and proofs.
# Success criteria: Exit 0 and base32: checks passed; every required check completes.
python3 -m tools.contribution check base32
```

Expected final output after all required stages, exit 0:

```text
...
base32: checks passed
```

This is the local contribution gate. Required checks are `impl_layout`,
`implementation_tests`, `fuzzer`, `proof_layout` and `dafny_verify`, defined in
[checks.py](src/benchmarks/checks.py). The implementation report is
`_build/contribution_checks/base32/implementation-tests.xml`; it must contain an
executed, non-skipped case. The verification stage also runs the marked proof
tests in `Tests.py`. Missing tools, unsupported fuzzing, skipped required work
and timeouts are failures. Run this gate only after completing the utility;
the untouched scaffold is not a passing example.
The local gate does not perform native entry-contract analysis or produce
candidate profiles; maintainers run the integration release checks separately.

#### Open a pull request

Complete the [pull request template](.github/pull_request_template.md) after the
contributor gate and required fuzzing campaigns pass on the same revision.
[Show verification and fuzzing results](#show-verification-and-fuzzing-results)
describes the evidence to include. Maintainers also review whether the
specification describes GNU behavior and uses only approved library contracts.

## Prepare the change

Explain the problem, the intended behavior and the files affected. Keep specification, implementation, proof and evaluator changes distinct. Reuse model types and relations, and implement derived algorithms and proofs inside the item. Keep the approved inputs and native library assumptions unchanged.

Put the utility's scope, supported options and model limitations in
`bench/utils/<utility>/<utility>.md`. Include the source revision/license and
trusted API assumptions so reviewers can assess the contract.

For an upstream scenario, record the GNU source revision and test path. Keep evaluator cases and oracle material out of candidate-visible resources. Preserve original mismatch bundles and store post-fix expectations separately.

## Coding style

Follow the surrounding code and reuse existing helpers before adding new ones. Keep changes focused on the requested behavior. Fix the cause of a failure instead of hiding it behind a fallback. Ask maintainers before adding a package, library or new behavioral heuristic.

### Python

Use Python 3.12 or newer, four-space indentation, and the 100-character line length configured in [pyproject.toml](pyproject.toml). Add type annotations to new interfaces. Ruff checks include import order and complexity; the configured complexity limit is 10.

The [CI checks](.github/workflows/checks.yml) run only Python formatting, Python
lint, and Rust formatting on pull requests and pushes to `main`. Run the same
checks from the repository root:

```sh
ruff format --check .
ruff check .
cargo fmt --manifest-path tools/coreutils_fuzzer/Cargo.toml --all -- --check
```

The development container provides Ruff 0.15.12. CI reads Ruff's `required-version` from
`pyproject.toml`; keep the development dependency pin in sync when updating it.
Rustup uses Rust 1.94.0 and its bundled rustfmt from `rust-toolchain.toml` in both
the development container and CI. Python checks use the exclusions in
`pyproject.toml`; Rust formatting covers the repository's fuzzer crate.
CI does not run tests, Pyright, Dafny verification, or benchmark checks. Run the
applicable validation described in this guide and include its evidence in PRs.

If you enable the optional Git hook, it formats Dafny only when `.dfy` files are
staged. Python and documentation changes use Ruff and the standalone unit suite.
Staged Dafny changes still require an installed native Dafny formatter.

- Import a name from the module that defines it. For example, use `from benchmarks.definition import BenchmarkKind`, not a package-root re-export.
- Keep `__init__.py` empty. Do not use wildcard imports, `__all__`, `importlib` or import tricks to avoid redesigning a cyclic dependency.
- Use `dataclass` for structured internal data and Pydantic `BaseModel` for data read from or written to external JSON. See [definition.py](src/benchmarks/definition.py) for both patterns.
- Use `Enum` for a fixed set of string values, not `Literal`. Give a constant one canonical name; do not create a second constant that aliases it.
- Use triple double quotes (`"""`) for multiline strings and docstrings.
- Catch specific expected exceptions only around external operations such as file reads, API calls or external-data parsing. Do not wrap the whole workflow or suppress programming errors.

### Dafny and proofs

Read [DAFNYSTYLE.md](DAFNYSTYLE.md) and [bench/AGENTS.md](bench/AGENTS.md). Use the existing two-space indentation and write the contract before the implementation.

Keep utility schemas, declarative behavior and fixed user-facing text in `Spec/`, algorithms and entry points in `Impl/`, and connecting lemmas in `Proof/`. Keep the existing class-prefixed file and module names. Spec must not import Core, Proof or CLI. The entry `RunCore` must directly ensure its main specification, `Spec(...)`; a helper lemma alone is insufficient.

- List only the objects or fields needed in `reads` and `modifies`. Fields outside
  `modifies` already stay unchanged; do not repeat that fact as old/new equalities.
- Add `decreases` where required. Say whether a proof also shows termination or
  only shows that a returned result is correct.
- Reuse lemmas. Add local proof steps when they help Dafny prove a required condition.
  Find the slow condition before increasing a verification time limit.
- Never use assumptions, unchecked external calls or verification skips to obtain
  a successful result.

### Tests and documentation

Test one observable scenario per test, including a realistic input that could expose a bug. Put a one-line intention comment immediately above the function or its decorators. For example, the [comm port](docs/adding-test-cases.md#add-the-python-function) describes the boundary behavior above the function and places its `# upstream:` origin inside it.

Do not test LLM prompt substrings instead of behavior. When removing a feature, update or remove its old tests rather than adding a test solely to prove absence. Select checks for the affected behavior; do not run unrelated benchmark suites for a documentation change.

Write documentation in simple English. State the result or action first, then show a small complete example. Separate measured results from expected behavior and report failures or missing checks explicitly.

For every runnable command example, put its expected output in a fenced `text`
block directly below the command. Include the expected exit code in the nearby
text. Mark variable values with `<...>` and omitted lines with `...`; say when a
command is silent or an unfinished example is expected to fail. Keep internal
walkthrough and experiment logs out of public documentation.

## Naming conventions

Use descriptive names that follow the existing module and file structure. These examples show the repository's established patterns; keep existing public names stable.

| Item | Convention | Example |
| --- | --- | --- |
| Python modules, functions and variables | `snake_case` | `definition.py`, `validate_task_id`, `task_id` |
| Python classes and enum types | `PascalCase` | `BenchmarkDefinition`, `BenchmarkKind` |
| Python constants and enum members | `UPPER_SNAKE_CASE` | `LEGACY_TASK_IDS`, `COREUTILS` |
| Coreutils task ID and directory | Lowercase ID; hyphens separate words | `base32`, `bench/utils/base32/` |
| Algorithm task ID and directory | `algorithm-<number>`; numeric directory | `algorithm-123`, `bench/algorithm/123/` |
| Utility Dafny files and modules | Utility name plus responsibility in `PascalCase` | `Base32Spec.dfy`, `Base32Core`, `Base32Proof` |
| Dafny methods and lemmas | Descriptive `PascalCase`, following the surrounding module | `RunCore`, `CoreSummaryImpliesSpec` |
| Dafny parameters and fields | Follow the local lower-case or `camelCase` pattern | `raw`, `io`, `readErr`, `stdoutRegion` |
| Python tests | `test_` plus the behavior in `snake_case` | `test_show_ends_crlf_across_files` |
| Fuzzer utility modules | Utility name in a `.rs` file | `generators/cat.rs` |
| Case IDs | Stable, unique and descriptive within the case set | `upstream-cat-E-crlf-across-files` |

Task IDs accept lowercase alphanumeric segments separated by a single hyphen. Class-name mapping is shared by scaffolding and profiles: `sample-tool` becomes `SampleTool`, and `algorithm-123` becomes `Algorithm123`. Case IDs are not task IDs; the example preserves GNU's uppercase `-E` option spelling. Do not rename a stored case casually, because regression expectations refer to its ID.

Existing shared API names such as `io.stdout()` are intentional exceptions to a general naming pattern. Follow the adjacent C, C# and Rust code when editing adapters; do not rename their externally bound symbols as style cleanup.

## Commit messages

Keep each commit focused on one logical change, including related scope and
documentation updates. If an agent is helping, it must create commits only when
you explicitly request them.

Write the entire message in English. Use this subject format:

```text
[Subject] verb-first description
```

`Subject` is one short word naming the changed area. Start it with an uppercase letter and use no spaces. Start the description with a lowercase verb. Examples:

```text
[Proof] simplify the sequence preservation lemma
[Fuzzer] cover carriage returns across file operands
[Docs] explain contribution evidence requirements
```

After a blank line, write three or four short sentences explaining the problem,
the fix, affected boundaries and any important limitation. Put test commands and
execution evidence in the PR rather than the commit message.

Credit each material co-author, including Codex when it contributed, with an
accurate `Co-authored-by: Full Name <email>` trailer. Use the co-author's actual
identity and keep trailers at the end of the message.

Do not create merge commits. Integrate branches by rebasing onto the target branch (`git pull --rebase`) and land pull requests with GitHub's **Rebase and merge**.

## Show verification and fuzzing results

Report evidence in **tests → fuzzing → verification** order. Copy and paste actual stdout into the template's fenced `text` blocks, with the exact command and exit code alongside it. Include final summaries and explain failed, skipped, unrun or inapplicable work. A missing tool, timeout or skipped required check is not a pass.

- **Tests:** Show the affected runtime/source test results with passed, failed and skipped counts.
- **Fuzzing:** For each affected coreutils utility, run the command in the PR template. Replace `<utility_name>` with your utility name. Keep seeds `1,7,19` and **1,000 iterations per seed**. Every requested iteration must match, with zero mismatches, timeouts, incomplete coverage or other errors. Paste the full stdout from the command into one block without changes. No file attachments are needed. Include stderr in the comparison and use the same code revision. Fixed JSON cases do not meet this requirement. Record failed runs and fixes too.
- **Verification:** Show Dafny stdout with verified/error/timeout counts and the verified files, their included files, and whether termination was proved. Also report definition/layout checks and the final contribution gate. A build is not proof verification.

The short automatic gate currently runs 20 fuzz cases with seed 1; it does not satisfy the separate PR requirement of three campaigns with at least 1,000 iterations each. See [Collect PR evidence](docs/fuzzing.md#collect-pr-evidence) for the command.
Paste the actual output directly into the PR; example output in a guide is not
run evidence. Never include credentials or restricted evaluator payloads.

Algorithm tasks require build/layout checks, runtime cases and Dafny verification.
Their `cases.json` files remain benchmark data; local test helpers and the
integration evaluator run those cases with the declared output contract. Fuzzing is required only when the task
declares a fuzzer capability. Use `python3 -m tools.contribution check algorithm-<number>`
for the contributor gate. `make -C bench/algorithm/<number> test` runs
the runtime cases. For documentation-only changes, record link/content checks
and explain why runtime verification and fuzzing were not run.

## Open the pull request

Open the pull request only after the code is complete and verified, as described
in [Open a pull request](#open-a-pull-request). Use a short title and explain the
resulting behavior first. Complete the template's scope and evidence fields,
paste the command output, and list known limitations. Rerun affected checks
after code changes and identify the revision each result covers.

Maintainers check whether the specification describes the required behavior and
uses only approved library contracts, separately from automated checks. Leave
their review decision pending until a human reviewer records it. Passing tests,
fuzzing and Dafny verification does not automatically approve the specification.

## Test runner ownership

Benchmark `Tests.py` files import `tools.test_support` and
`tools.execution` from this repository. The contributor runner selects
its local pytest evidence plugin. Tests must not import evaluator, harness or
analysis-client modules, or execute their build callbacks.

When `EVAL_BENCH_DLL` is explicitly supplied, it selects a prebuilt candidate
artifact. The helper requires that file to exist and does not run a build script.
Without a selected artifact, task fixtures use the local contributor build command.
A legacy `EVAL_BENCH_BUILD_SCRIPT` request without a prebuilt artifact is an error;
external build callbacks are unsupported. Native versus .NET execution remains
selected by `EVAL_BENCH_EXECUTION_KIND`.
