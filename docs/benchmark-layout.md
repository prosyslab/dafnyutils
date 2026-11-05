# Common benchmark command-line layout

Every benchmark item is a command-line executable. Its CLI parses arguments or
standard input inside the executable, then the common runner protocol calls
`<Name>.<Name>BenchmarkItem.RunCore(raw, io)`. Coreutils and algorithm items use
the same candidate workspace, build entry, final specification obligation,
runtime evaluation stage and verification/scoring pipeline.

Category directories and source provenance remain metadata. They do not select
another execution interface or a typed evaluator harness. Remaining category
checks select registry paths, list filters, scaffold provenance, GNU manual
extraction, or display labels/manual references. Execution, workspace generation,
principal contracts, verification and scoring use the common interface.

Utilities use `bench/utils/<task>/{Spec,Impl,Proof}/`, matching Leanutils' per-utility separation. Task IDs and file/module base names stay unchanged. Descriptions, manifests, oracle tests, Makefiles and project configuration stay at the task root. Algorithm tasks retain their existing flat source layout and the same runner interface.

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

Auxiliary Spec modules and shared mathematical models stay in `Spec/`. Auxiliary implementation modules stay in `Impl/`. Connecting lemmas stay in `Proof/`, including `DateCalendar.dfy`, `DateFormat.dfy` and `CpPathBridge.dfy`. Existing dependencies and proof obligations are preserved; directory placement does not change their trust status.

The common scaffold is in `tools/benchmark_templates/common`. Category overlays provide provenance, natural-language scope and oracle examples. The generator specializes source prefixes for nested utilities and flat algorithms. All supported item Makefiles expose `build`, `test` and `verify` through the existing repository modules.

## Algorithm migration

The ten existing algorithm tasks now use the class-prefixed source names above.
Their original typed mathematical specification is preserved as `Answer`, and
their original implementation and connecting proof remain in the task-owned
Core/Proof closure as `Solve`, `AnswerSummary` and
`AnswerSummaryImpliesAnswer`. No completed algorithm moved into shared support.

The principal `Spec(raw, io, exit)` existentially relates the same answer to its
encoded standard output. It binds the actual stream observation, including a
partially committed prefix and its errno. `RunCore` inspects write results and
returns 1 on an IO error. Malformed input or unsupported arguments produces
spec-owned diagnostic text and returns 2 after a successful diagnostic write;
a failed diagnostic write returns 1. The CLI checks input-read errors before
parsing, so a plausible partial input cannot turn a failed read into success.

The parsing code is local to each task's schema. It tokenizes ASCII whitespace,
parses unbounded signed decimal integers, checks the input shape, and passes the
decoded values to RunCore. Original typed preconditions are retained by `Valid`.
Where Core and Spec have separate validity predicates, the entry invokes the
existing validity bridge before calling the implementation.
The CLI accepts no command arguments for these stdin-only problems. These
changes do not establish CLI termination: the shared runner still permits
`decreases *`, while the original Solve termination obligations are preserved.

## Oracle capabilities

`benchmark.yaml` can declare these capabilities:

| Capability | Effect |
| --- | --- |
| `fixed_cases: true` | Require evaluator-owned `cases.json`; run every positive raw input |
| `gnu_reference: true` | Build and isolate the task's GNU reference executable |
| `fuzzer: true` | Require the registered GNU fuzzer provider on the trusted host |
| `output_contract` | Interpret fixed-case stdout as tokens, integer, covering-cell or minimal-frame |

The `capabilities` mapping is required. Older definitions without an explicit
mapping fail validation, so the migration cannot silently remove an existing
oracle or fuzzer requirement. All registered definitions declare their providers.

All items require `impl_layout`, `implementation_tests`, `proof_layout` and
`dafny_verify`. The fuzzer is an optional capability with its existing required
check and scoring behavior. GNU reference construction and binary isolation are
provider prerequisites; neither changes candidate execution or proof scope.

The fixed datasets are unchanged and remain evaluator-owned. Their legacy
`parser`, `parameters` and `input_count` metadata is validated as data and never
executed. Candidate workspaces hide `Tests.py`, `Tests.dfy`, `cases.json` and
Makefiles uniformly. Evaluator-only expected outputs are never public resources.

Integer results are compared numerically using signed decimal syntax. The
covering-cell and minimal-frame
checkers accept alternative witnesses allowed by the original Answer relations:
the former checks every wall against the returned row/column; the latter checks
the exact frame rendering and the minimum side length witnessed by the unchanged
expected output. Every successful case also requires exit 0 and empty stderr.
The checkers do not compute a replacement solution.

## Maintenance validation record

This repository maintenance began at `db4886ab3aefee4bf59bf1b519fb60d661d3a911`,
using the isolated branch `agent/trustbase-cli-20261020/cli` in
`/workspace/tmp/trustbase-cli-20261020/cli`. Runtime and proof validation uses
Python 3.12.3, tmux 3.4 and Dafny
`4.11.1+10dca3ba4a2909c11299176440401fc31413b53d`.

Initial checks temporarily borrowed the five core files World.dfy, IO.dfy,
IOContract.dfy, IOExtern.cs and BenchmarkItem.dfy from concurrent task 1 to check
the no-policy stream API. They were excluded from the task-2 commit and restored
before rebasing onto completed task 1. The final integration record below uses
the committed task-1 core rather than borrowed files.

Commands run from this worktree use `PYTHONPATH=$PWD/src` to prevent the installed
editable package from resolving the main checkout. Unit fixtures and transitive
helpers were audited before execution; new development cases use in-memory
observations only and create no temporary directories.

Initial evidence: algorithm-1 runtime executed all 278 unchanged positive inputs
plus malformed-input and unsupported-argument scenarios, passing 280 checks;
the three proof probes were deselected for this runtime tier. The initial full
gate identified a missing stream-result discriminator contract in the baseline
IO API. Task 1 added the proved equivalence between Ok and errno 0, after which
the focused new RunCore obligation passed without extra proof assertions.

All ten no-policy runtime targets passed: 1,589 executed checks, comprising every
one of the 1,569 unchanged positive inputs and twenty invalid-input/argument
scenarios. The serial development unit tier passed 113 tests with fifteen
integration tests deselected. Ruff 0.15.12 lint and format checks passed for
`src`, `tests` and `tools/benchmark_templates`. A read-only comparison against
the base revision confirmed the original computations and answer relations are
preserved modulo the documented declaration and include renames. One existing
algorithm-63 induction call was localized inside its calculation step to guide
the unchanged proof obligation.

The complete development integration tier initially passed twelve tests and
failed three. The common default library-analysis path was corrected, and its
focused integration test passed. Two integration cases were then blocked by the
temporary mixture of borrowed task-1 core and old task-1 cat/chmod sources.
After task 1 completed, the final complete development tier below passed both
previously blocked cases and all other integration scenarios.

The initial algorithm-59 full proof gate found that the migration had omitted
an existing Spec-to-Core validity bridge. The wrapper now calls that original
lemma, as do the four other tasks with distinct validity predicates, and the
implementation retains its original conditional precondition. The initial
algorithm-63 gate timed out on `OuterFoldCardinality`; moving its existing
induction call into the exact calculation justification proved all 24
conditions of that declaration. Neither correction changes an answer relation,
implementation algorithm, proof scope or time limit.

Commands and outcomes from this worktree:

| Command | Outcome |
| --- | --- |
| `PYTHONPATH=$PWD/src python3 -m benchmarks validate algorithm-1` | Passed definition, resource and final-entry contract validation |
| `PYTHONPATH=$PWD/src make build TASK=algorithm-1` | Passed native CLI build |
| `PYTHONPATH=$PWD/src PYTEST_ADDOPTS='-p no:cacheprovider' make test-unit` | 113 passed, 15 integration tests deselected |
| `ruff check --no-cache src tests tools/benchmark_templates` | Passed |
| `ruff format --no-cache --check src tests tools/benchmark_templates` | Passed |
| `PYTHONPATH=$PWD/src PYTEST_ADDOPTS='-p no:cacheprovider' make test TASK=algorithm-N` for all ten registered N | 1,589 runtime checks passed |
| `PYTHONPATH=$PWD/src make -C bench/algorithm/N verify` | All ten complete gates passed, 3,639 verification conditions and zero failures |
| `PYTHONPATH=$PWD/src PYTEST_ADDOPTS='-p no:cacheprovider' make test-integration` | Initial 12 passed, 3 failed; common analysis fix separately passed; two task-1 dependency cases remain |

The complete proof gates use the supported Make target's fixed random seed 42,
isolated assertions, 30-second condition limit and 100-second declaration
process limit. Runtime tests do not substitute for these proof results. CLI
and schema support have the same verification boundary as existing utilities;
the original typed Solve and connecting proof declarations are included in the
complete gate. Final condition counts are 243 (1), 148 (4), 188 (20), 187 (38),
359 (59), 188 (63), 698 (75), 1,001 (100), 182 (3690) and 445 (4004). For 38,
59 and 63 these results use the corrected full-gate recheck logs rather than
the earlier attempt in `status.tsv`.

The serial runtime/proof queue runs in tmux session `trustbase-cli-task2` using
`/workspace/tmp/trustbase-cli-20261020/run_cli_checks.sh`; full corrected gates
use `trustbase-cli-task2-recheck` and `trustbase-cli-task2-final`. Logs and exit
statuses are local artifacts in
`/workspace/tmp/trustbase-cli-20261020/cli-validation/`; they are not distributed
with the task and are unavailable outside this maintenance environment.

## Final integration validation

Task 1 completed as `b693b10f0779fd9fa2452e696888a30f0369ce39`. The single task-2
commit was rebased onto it without conflicts or code changes; Git range-diff
reported the patch as equal. The exact five borrowed files were restored only
after preserving their known diff, and the rebased worktree was clean.

The combined code was tested at
`61565b1e80c7974700d7144ef459a4aa3b98c784`; the following amendment changes only
this Markdown record. The only development-test change inherited from task 1
updates the real Chmod principal/specification dependency expectation; its
transitive fixture/helper graph was reviewed before execution. No temporary
directory workload, native build, dataset or score rule was added.

| Final command from this worktree | Outcome |
| --- | --- |
| `git diff --check b693b10..HEAD` | Passed |
| `ruff check --no-cache src tests tools/benchmark_templates` | Passed |
| `ruff format --no-cache --check src tests tools/benchmark_templates` | Passed, 86 files |
| `PYTHONPATH=$PWD/src DOTNET_PROCESSOR_COUNT=8 PYTEST_ADDOPTS='-p no:cacheprovider' make test-final` | Passed: 113 unit tests and 15 integration tests, no skips |
| `PYTHONPATH=$PWD/src DOTNET_PROCESSOR_COUNT=8 python3 -m benchmarks validate` | Passed: all 52 registered layouts and principal entry/resource contracts |

The test command's child soft descriptor limit was 2048, leaving the host and
other processes unchanged. Test unit/integration durations were 3.91 and 65.94
seconds. Tmux sessions `trustbase-cli-rebase-final` and
`trustbase-cli-rebase-layouts` preserve these runs; exact commands, code revision,
working directory, environment, durations and actual statuses are recorded in
`/workspace/tmp/trustbase-cli-20261020/task2-rebase/`. The complete algorithm
proof/runtime counts above remain tied to their earlier source pins; these
final development and contributor checks are separate results.

GNU differential cases and fuzzers were not repeated for task 2 because its
utility changes only add capability metadata; their existing mandatory
requirements remain enabled. No evaluated agent run or private reference-
solution inspection was performed.

## Contributor tooling

Task Makefiles use the local `benchmark_tools.contribution.make_tasks` and
`benchmark_tools.contribution.verify` modules. Benchmark `Tests.py` files use
`benchmark_tools.test_support` and `benchmark_tools.execution`; no evaluator or
analysis-client Python package is needed. Root evaluation remains responsible
for entry-contract analysis, isolated grading and scoring.
