# Common benchmark command-line layout

Every benchmark item is a command-line executable. Its CLI parses arguments or
standard input inside the executable, then the common runner protocol calls
`<Name>.<Name>BenchmarkItem.RunCore(raw, io)`. Coreutils and algorithm items use
the same candidate workspace, build entry, final specification obligation,
runtime evaluation stage and verification/scoring pipeline.

Task categories identify source provenance and organize discovery and
scaffolding. All categories use the common execution interface.

Utilities use `bench/utils/<task>/{Spec,Impl,Proof}/`. Descriptions, manifests,
oracle tests, Makefiles and project configuration stay at the task root.
Algorithm tasks use `bench/algorithm/<number>/` with a flat source layout and
the same runner interface.

| Utility source | Responsibility |
| --- | --- |
| `Spec/<Name>Schema.dfy` | Raw command datatype and input parsing |
| `Spec/<Name>Spec.dfy` | Declarative observable relation and fixed diagnostic text |
| `Impl/<Name>Core.dfy` | Executable implementation and its summary |
| `Proof/<Name>Proof.dfy` | Lemmas connecting the summary to Spec |
| `Impl/<Name>.dfy` | BenchmarkItem class; RunCore directly ensures Spec(raw, io, exit) |
| `Impl/<Name>Cli.dfy` | Native process entry and shared runner call |
| `Impl/CliSupport.dfy` | Fixed task-local parser, stream checks and process runner |
| `dfyconfig.toml` | Builds `Impl/<Name>Cli.dfy` with the common native IO adapter |
| `Tests.py` | Benchmark-owned executable behavior checks and proof probes using local helpers |

Put auxiliary specifications and mathematical models in `Spec/`, implementation
modules in `Impl/`, and connecting lemmas in `Proof/`. Spec must not import
implementation, proof or CLI modules. The final obligation is
`RunCore ==> Spec(...)`; a summary-to-Spec lemma supports this obligation but
does not replace it. See the [bench rules](../bench/AGENTS.md).

The common scaffold is in `tools/benchmark_templates/common`; category templates
provide descriptions, provenance and oracle examples. Task Makefiles expose
`build`, `test` and `verify` through local `tools.contribution` modules,
using the toolchain in the development container. See
[adding a utility](../CONTRIBUTING.md#extending-benchmark).
Scaffolds use the same fixed CLI protocol as registered items.

## Candidate-owned helpers

Core supplies system values, native observations and primitive contracts.
Utility algorithms and their connecting proofs belong in the task's editable
Core and Proof files. Shared support must not supply a solved implementation of
the computation that the candidate is asked to implement and prove.

A helper is a candidate obligation only when all of these hold:

- It is outside the fixed specification and CLI dependency closure.
- It is not copied or delivered as support.
- Its source is editable and collected with the submitted outputs.
- The generated workspace supplies a module placeholder rather than a solved body.
- Its reachable definitions are selected by both local and evaluated proof gates.

The evaluator fixes whole specification/support files. A `Core` filename or a
directory-wide writable mount does not override this classification. Keep Spec
relations separate from implementation and proof files. A fixed decoder must
not import a candidate helper, because that makes the helper's file immutable.
For example, Cp's decoder uses `CpSchema.TrimForDecode` independently of the
candidate-owned runtime path algorithm.

Tasks own map, filter, scan, fold, mode parsing and path/backup algorithms and
their proofs. They may reuse pure UTF-8, quoting, diagnostic, numeric/time and
lexical-path definitions from core or Spec. Native observations, filesystem transformations
and their proof witnesses are ghost. Shared validity proofs establish primitive
contracts, not utility correctness. Kernel lookup, removal and rename proof
internals are private to `IOContract`; task-specific proofs belong in the
editable task closure.

## Algorithm task contracts

Algorithm files use class-prefixed names. Their typed mathematical specification
is `Answer`; `Solve`, `AnswerSummary` and `AnswerSummaryImpliesAnswer` provide
the implementation and its connecting proof inside the task.

The principal `Spec(raw, io, exit)` existentially relates the same answer to its
encoded standard output. It binds the actual stream observation, including a
partially committed prefix and its errno. `RunCore` inspects write results and
returns 1 on an IO error. Malformed input or unsupported arguments produces
spec-owned diagnostic text and returns 2 after a successful diagnostic write;
a failed diagnostic write returns 1. The CLI checks input-read errors before
parsing, so a plausible partial input cannot turn a failed read into success.

The parsing code is local to each task's schema. It tokenizes ASCII whitespace,
parses unbounded signed decimal integers, checks the input shape, and passes the
decoded values to RunCore. Typed preconditions are expressed by `Valid`.
Where Core and Spec have separate validity predicates, the entry invokes the
validity bridge before calling the implementation.
The CLI accepts no command arguments for these stdin-only problems. These
contracts do not establish CLI termination: the shared runner permits
`decreases *`, while `Solve` retains its termination obligations.

## Oracle capabilities

`benchmark.yaml` can declare these capabilities:

| Capability | Effect |
| --- | --- |
| `fixed_cases: true` | Require evaluator-owned `cases.json`; run every positive raw input |
| `gnu_reference: true` | Build and isolate the task's GNU reference executable |
| `fuzzer: true` | Require the registered GNU fuzzer provider on the trusted host |
| `output_contract` | Interpret fixed-case stdout as tokens, integer, covering-cell or minimal-frame |

The `capabilities` mapping is required. Definitions without it fail validation.
Declare the providers needed by the task; do not remove existing oracle or
fuzzer requirements to make validation pass.

All items require `impl_layout`, `implementation_tests`, `proof_layout` and
`dafny_verify`. A declared fuzzer capability makes the `fuzzer` check mandatory
under the task's scoring rules. GNU reference construction and binary isolation are
provider prerequisites; neither changes candidate execution or proof scope.

Fixed datasets remain evaluator-owned. Their
`parser`, `parameters` and `input_count` metadata is validated as data and never
executed. Candidate workspaces hide `Tests.py`, `Tests.dfy`, `cases.json` and
Makefiles uniformly. Evaluator-only expected outputs are never public resources.

Integer results are compared numerically using signed decimal syntax. The
covering-cell and minimal-frame
checkers accept alternative witnesses allowed by the `Answer` relations:
the former checks every wall against the returned row/column; the latter checks
the exact frame rendering and the minimum side length witnessed by the
expected output. Every successful case also requires exit 0 and empty stderr.
The checkers do not compute a replacement solution.
