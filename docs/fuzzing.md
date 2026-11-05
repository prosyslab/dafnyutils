# Run the coreutils fuzzer

The complete fuzzer is Dafnyutils benchmark-construction tooling. Its Rust
engine, Python launcher and Docker support remain in `tools/coreutils_fuzzer`.
Root owns submission grading and the policy for fuzzer checks, budgets and score
treatment. The benchmark definition supplies the target, and the root evaluator
invokes this launcher.

The fuzzer runs the **pinned GNU executable** and **your Dafny executable** on
the same generated inputs and reports any difference in output, exit status or
filesystem effects.

The typical loop looks like this:

1. Run a campaign. It stops at the first mismatch and saves a **repro bundle**.
2. Fix the cause (in the implementation, the specification, or the setup).
3. Add a **regression expectation** that shows the corrected behavior.
4. Rerun the campaign and paste the output into your PR.

> **What a pass means:** a matching campaign is finite runtime evidence. It is
> not a Dafny proof and does not approve the specification. Time-related
> behavior is not covered at all (see [What the fuzzer does not
> check](#what-the-fuzzer-does-not-check)).

## Contents

- [Quick start](#quick-start)
- [1. One-time setup](#1-one-time-setup)
- [2. Run a campaign](#2-run-a-campaign)
- [3. Collect PR evidence](#collect-pr-evidence)
- [4. When a campaign fails](#4-when-a-campaign-fails)
- [5. Pin a specific scenario](#5-pin-a-specific-scenario)
- [6. Inspect metrics](#6-inspect-metrics)
- [7. How targets are executed](#7-how-targets-are-executed)
- [8. Support a new utility](#support-a-new-utility)
- [Reference](#reference)

## Quick start

Already set up? Run these from the repository root in Bash or zsh:

```sh
# Is my utility supported?
python3 tools/coreutils_fuzzer/run.py capabilities

# Quick local check: 20 generated cases
python3 tools/coreutils_fuzzer/run.py fuzz cat --iterations 20 --seed 1

# PR evidence: 3 seeds x 1,000 cases
python3 tools/coreutils_fuzzer/run.py fuzz '<utility_name>' --seeds 1,7,19 --iterations 1000
```

If any of these fail with a missing binary, DLL or image, go through
[setup](#1-one-time-setup) first.

## 1. One-time setup

Run commands from this repository's root in the development container, with
Docker available. Clear any old
`REF_BIN_TEMPLATE`, `DUT_BIN_TEMPLATE`, `EVAL_REPO_ROOT` or `EVAL_TARGET_ROOT`
overrides so the fuzzer picks up the normal project artifacts.

You need three things. Build times depend on downloads and CPU; do not count
them as campaign time.

| What | Command | Done when |
| --- | --- | --- |
| Pinned GNU binary (reference) | `make build-coreutils` | `_build/coreutils/src/cat` exists and is executable |
| Dafny utility under test (DUT) | `make -C bench/utils/cat build` | `_build/bench/cat_bench.dll` exists |
| Execution image (needs Docker) | `docker compose -f tools/coreutils_fuzzer/docker-compose.yaml build` | Output ends with `Image dafnyutils-coreutils-fuzzer:latest Built` |

Replace `cat` with your utility. The wrapper builds its own Rust runner with
Cargo on first use, which may download dependencies on a fresh machine.

<details>
<summary>Expected output of each build step</summary>

`make build-coreutils`, exit 0:

```text
...
make[1]: Leaving directory '/workspace/dafnyutils/_build/coreutils'
```

`make -C bench/utils/cat build`, exit 0:

```text
Dafny program verifier did not attempt verification
make: Leaving directory '/workspace/dafnyutils/bench/utils/cat'
```

`docker compose ... build`, exit 0:

```text
...
Image dafnyutils-coreutils-fuzzer:latest Built
```

</details>

To check that the wrapper itself works (this runs no target and takes under a
second):

```sh
python3 tools/coreutils_fuzzer/run.py --help
# Usage: run.py [OPTIONS] COMMAND [ARGS]...
# Lists: capabilities, fuzz, regression, replay
```

## 2. Run a campaign

### Check that your utility is supported

```sh
python3 tools/coreutils_fuzzer/run.py capabilities
```

```text
cat fuzz=custom scenarios=yes
ls fuzz=custom scenarios=yes
Limitation: Time-related bugs are outside fuzzer coverage. Raw output differences caused by clocks or file timestamps are inconclusive.
```

If your utility is not listed, it has no generator yet. See
[Support a new utility](#support-a-new-utility). A manifest or a built DLL does
not register it; the registry lives in
`tools/coreutils_fuzzer/src/utils/capabilities.rs`. Before running, skim the
utility's generator, whether it has scenarios, and any reported limitations.

### Run generated inputs

```sh
python3 tools/coreutils_fuzzer/run.py fuzz cat \
  --iterations 20 --seed 1 --metrics-out /tmp/cat-seed1-metrics.json
```

This compares `_build/coreutils/src/cat` against `_build/bench/cat_bench.dll`,
generates 20 inputs, and **stops at the first non-match**. A passing run ends
like this (exit 0):

```text
Results
  Iterations : requested=20 submitted=20 completed=20 not_started=0 unfinished=0
  Outcomes   : match=20 mismatch=0 timeout=0 other_errors=0
  Elapsed    : <seconds>s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
```

Stdout has three sections per campaign:

- **Configuration**: seed, budget, target paths and kinds, input source,
  limits, stderr policy, work directory mode, container image and identity,
  metrics path.
- **Coverage**: which options, option pairs and semantic buckets the generated
  inputs hit, including gaps. This describes the *inputs*, not source-code
  coverage. A missing bucket can be normal (for example, `true` never creates
  files).
- **Results**: requested / submitted / completed iterations, matches,
  mismatches, timeouts, other errors, elapsed time and PASS/FAIL. Errors are
  never counted as matches. PASS is printed only after the metrics file (if
  requested) has been saved.

In Results, `not_started` counts cases never submitted and `unfinished` counts
submitted cases that produced no result.

### Useful options

| Option | Effect |
| --- | --- |
| `--seed N` | Repeatable input generation for the same runner and configuration. Does not freeze clocks, binaries or the host. |
| `--seeds 1,7,19` | Run several campaigns, one per seed. Each gets its own output name. |
| `--all-built` | Run every registered utility that has a built Dafny DLL. |
| `--metrics-out PATH` | Write per-case evidence. Use a fresh path; existing files are not overwritten. |
| `--process-timeout-seconds N` | Per-process limit for reference and DUT (default 10). A timeout is never treated as a match. |
| `--shrink-attempts 0` | Keep a failing case exactly as generated instead of minimizing it. |
| `--case-set FILE` | Run stored cases instead of generated ones. See [Pin a specific scenario](#5-pin-a-specific-scenario). |

**Comparing other artifacts.** Set `REF_BIN_TEMPLATE` and `DUT_BIN_TEMPLATE`
(each with a `{util}` placeholder) and pick `--ref-kind` / `--dut-kind`
(`native` or `dotnet-dll`). Mention these overrides in any report. Comparing
GNU with itself tests the harness only; it says nothing about a Dafny utility.

<a id="collect-pr-evidence"></a>

## 3. Collect PR evidence

For **each affected utility**, run **three distinct seeds with at least 1,000
iterations each**:

```sh
python3 tools/coreutils_fuzzer/run.py fuzz '<utility_name>' \
  --seeds 1,7,19 --iterations 1000
```

Every seed must end with (exit 0):

```text
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : <seconds>s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
```

That is, `requested`, `submitted`, `completed` and `match` all equal the budget,
and every error count is zero.

**Checklist**

- [ ] Same code revision for all three seeds.
- [ ] stderr comparison left on (the default).
- [ ] No mismatch, timeout, incomplete coverage or other error.
- [ ] Full stdout pasted, unedited and in order, into the single fuzzing `text`
      block of the [PR template](../.github/pull_request_template.md). No file
      attachments are needed.
- [ ] Command and process exit status recorded outside the block; stderr kept
      if it reports failure details.
- [ ] Failed campaigns and their fixes recorded too.

**Things that do not count**

- The fuzzer check inside root `make check-task TASK=<utility>` (20 cases, seed 1).
- A fixed JSON case set or regression suite. Those are separate checks.
- Picking three favorable seeds while leaving out failing ones.
- Missing output. A setup failure may stop before any Results section appears;
  that is never proof of success.
- A partially completed run. The wrapper stops when a seed fails, so later
  seeds still need to run after you fix the cause.

Use your own campaign logs as evidence.

## 4. When a campaign fails

### What the outcome means

Failures print `FUZZER_OUTCOME=<value>` when they can be classified.

| Outcome | What to do |
| --- | --- |
| `match` | Nothing to fix. Record the population and configuration; continue proof and review work. |
| `semantic_mismatch` | Keep the bundle. Work out whether the implementation or the contract is wrong. |
| `fuzzer_timeout` | Record the timed-out case and find out why it hit the deadline. |
| `fuzzer_unsupported_capability` | Implement or review the utility's generator registration. |
| `fuzzer_target_spawn_failure`, `fuzzer_dotnet_runtime_failure` | Fix the missing or unusable binary or runtime. |
| `fuzzer_infrastructure_failure`, `fuzzer_build_failure` | Fix Docker or build prerequisites and rerun. |
| `replay_not_reproduced` | A replay produced a different complete verdict than the saved one. |
| `regression_failure` | At least one fixed expectation failed. |

Always keep the original command, its log and the bundle. A setup error can
happen before any case metrics exist.

An early mismatch leaves the unused budget visible. A 1,000-case run that fails
on its first case reports one completed and 999 not started.

**Do not work around a mismatch.** Don't suppress stderr, add output rewriting,
relax the comparison, edit the expected output or modify the original bundle.
The comparator owns all normalization. Diagnose whether the problem is in the
utility, its specification, the adapter or the test setup.

### Replay a saved mismatch

Take the bundle path printed by the failed run:

```sh
python3 tools/coreutils_fuzzer/run.py replay /tmp/coreutils-fuzzer-repros/cat-example
```

Replay **always exits nonzero**, by design:

| You see | Meaning |
| --- | --- |
| `FUZZER_OUTCOME=semantic_mismatch` | The saved mismatch still reproduces exactly. |
| `FUZZER_OUTCOME=replay_not_reproduced` | The program now behaves differently, e.g. after your fix. |

Diagnostic wording and paths vary. To show that a fix works, add a
[regression expectation](#pin-it-as-a-regression); never rewrite the original
bundle.

Replay accepts bundle schema 8 only and rejects older schemas. The bundle keeps
raw metadata, typed process outcomes, the container image identity and numeric
target identity. Without an image override, replay uses the saved image. Bundles
are not signed, so they do not prove who created them.

### Rerun an input saved after an execution error

If a case stopped before a comparison was possible, the fuzzer saves an
**input-only bundle** in `FUZZ_REPRO_DIR` instead:

- `case-set.json`: the arguments, fixture, standard input and working directory.
- `manifest.json`: the error, original seed and iteration, execution context,
  and a `reproduce_one_liner`.

Run the `reproduce_one_liner` from the Dafnyutils repository root, with the
recorded binaries and image available. It runs that one input once through
`fuzz --case-set`; whether it fails again depends on whether the original error
recurs.

Keep in mind:

- These bundles use schema `coreutils-fuzzer.failure-input.v2`. `run.py replay`
  does not accept them.
- The rerun starts at iteration zero, so iteration-dependent settings (such as
  the `chmod` umask and read-only time anchor) can differ. Compare with the
  original values in `manifest.json`.
- A Docker stall may not reproduce.

## 5. Pin a specific scenario

Use this to reproduce one exact scenario (for example, from an upstream GNU
test), and later to lock in a fix. Stored cases are used unchanged and replace
random generation for that run. You don't need to edit the registry per case,
but the utility itself must already be registered.

The walkthrough below adapts split-CRLF behavior from
[coreutils/tests/cat/cat-E.sh](../coreutils/tests/cat/cat-E.sh). It assumes the
cat targets and image from [setup](#1-one-time-setup). For Python tests in a
utility's `Tests.py`, see [Add test cases](adding-test-cases.md) instead.

### Write a case set

Save as `/tmp/dafnyutils-cat-crlf.json`:

```json
{
  "schema_version": "coreutils-fuzzer.case-set.v1",
  "util": "cat",
  "cases": [
    {
      "id": "upstream-cat-E-crlf-across-files",
      "case": {
        "argv": ["-E", "in2", "in2b"],
        "fixture": {
          "directories": [],
          "files": [
            {"relative_path": "in2", "bytes": [49, 13], "mode": 420},
            {"relative_path": "in2b", "bytes": [10, 50, 13, 10], "mode": 420}
          ],
          "symlinks": [],
          "hardlinks": []
        },
        "stdin": [],
        "cwd": "."
      }
    }
  ]
}
```

Reading the fixture:

- `49` and `50` are `1` and `2`; `13` is CR and `10` is LF.
- Mode `420` is decimal for `0644`.
- Paths are relative to the fixture root.

Give each case a stable, unique ID. Put each scenario in its own case rather
than mixing unrelated success and error behavior.

To keep the case permanently, add it to
`tools/fixtures/coreutils_fuzzer/v1/cases/cat.json` without replacing existing
cases. It only runs when that file is selected with `--case-set`; the filename
alone does not add it to every campaign.

### Run it

Pass `--iterations` equal to the number of cases in the file, and disable
shrinking so the scenario stays unchanged:

```sh
python3 tools/coreutils_fuzzer/run.py fuzz cat \
  --case-set /tmp/dafnyutils-cat-crlf.json \
  --iterations 1 --shrink-attempts 0 \
  --metrics-out /tmp/pr-fuzzer-cat-crlf.json
```

```text
Results
  Iterations : requested=1 submitted=1 completed=1 not_started=0 unfinished=0
  Outcomes   : match=1 mismatch=0 timeout=0 other_errors=0
  Elapsed    : <seconds>s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
```

The stored input runs against the original GNU binary and the Dafny DLL, and
the usual comparator checks streams, process outcome and filesystem state. Use
a fresh metrics path for each run. If it mismatches, follow
[When a campaign fails](#4-when-a-campaign-fails).

To confirm the named case really completed as a match (not just that a metrics
file exists):

```sh
python3 - <<'CHECK'
import json
from pathlib import Path

report = json.loads(Path('/tmp/pr-fuzzer-cat-crlf.json').read_text())
assert report['schema_version'] == 'coreutils-fuzzer.metrics.v3'
assert report['completed'] == 1
case = report['cases'][0]
assert case['id'] == 'upstream-cat-E-crlf-across-files'
assert case['outcome'] == 'match'
assert case['durations'] and all(isinstance(v, int) for v in case['durations'].values())
print(case['id'], case['outcome'])
print(case['durations'])
CHECK
```

```text
upstream-cat-E-crlf-across-files match
{'source_ns': <int>, 'evaluation_ns': <int>, 'coverage_ns': <int>, 'shrink_ns': <int>, 'persist_ns': <int>, 'queue_wait_ns': <int>}
```

Durations are integers in nanoseconds and vary by run.

<a id="pin-it-as-a-regression"></a>

### Pin it as a regression

After a fix, or to keep the case as a stable parity check, save as
`/tmp/dafnyutils-cat-crlf-regression.json`:

```json
{
  "schema_version": "coreutils-fuzzer.regression-suite.v1",
  "util": "cat",
  "case_set": "dafnyutils-cat-crlf.json",
  "expectations": [
    {"case_id": "upstream-cat-E-crlf-across-files", "expect": "match"}
  ]
}
```

`case_set` is resolved relative to the suite file, not your shell's directory.
JSON does not allow trailing commas. For permanent storage, add the expectation
to `tools/fixtures/coreutils_fuzzer/v1/regressions/cat.json` with
`"case_set": "../cases/cat.json"`, keeping existing expectations.

```sh
python3 tools/coreutils_fuzzer/run.py regression /tmp/dafnyutils-cat-crlf-regression.json \
  --metrics-out /tmp/dafnyutils-cat-crlf-regression-metrics.json
```

```text
Regression suite passed for util=cat expectations=1
```

The regression asserts *current* GNU/Dafny parity. It does not replace the
original mismatch bundle, which stays as an unchanged historical record. After
a fix, it is expected that replaying the old bundle no longer reproduces while
this regression passes.

## 6. Inspect metrics

The metrics file (schema `coreutils-fuzzer.metrics.v3`) records the requested,
submitted, completed and abandoned counts, plus each case's ID, input
fingerprint, outcome and stage durations in nanoseconds. The
[check script above](#run-it) shows how to read them.

Only compare performance across runs with the same cases, binary and input
fingerprints, seeds, deadlines, comparison settings and host conditions. A
small run shows that execution and reporting work; it does not show a
performance improvement.

## 7. How targets are executed

### Container sandbox

For each run, the host starts one disposable Compose service, copies in the
runner and target artifacts, collects observations, and removes the service.
Both GNU and Dafny run inside it, including option discovery. There is no
fallback to running targets on the host, and no public `--work-root` option.

- Both targets share the service filesystem and staged executables. Docker is
  the only boundary; there is no extra per-target filesystem or oracle
  isolation.
- No Docker socket, no external network, read-only root, writable tmpfs mounts
  for staging and fixtures. The `/fuzz` fixture mount uses `noatime`, so reading
  a file or directory does not update its access timestamp. Explicit timestamp
  changes, such as those made by `touch`, still take effect.
- Default Docker seccomp/AppArmor and `no-new-privileges` stay on. Trusted setup
  uses limited ownership/identity capabilities; targets run as the runner's
  non-root user.

### Target environment

The environment is cleared and then set to fixed values, including `LANG=C`,
`LC_ALL=C`, `TZ=UTC0`, `TERM=dumb`, `QUOTING_STYLE=literal` and a fixed `PATH`.
Host credentials are not inherited. Unsafe fixture paths, symlinks that escape
the fixture, and invalid links are rejected.

### What is compared

Process outcomes, raw stdout/stderr, and filesystem contents, metadata and
identity transitions are compared. Both targets run sequentially at the same
absolute fixture path. The DUT reuses the reference's original objects only
when the raw pre/post states are exactly equal and observation and target
preparation leave metadata unchanged. Otherwise it receives a fresh copy of
the original fixture. Absolute host inode numbers are not compared across
independent copies.

<a id="what-the-fuzzer-does-not-check"></a>

### What the fuzzer does not check

**Time-related bugs are outside fuzzer coverage.** GNU and Dafny run at
different moments, and a shared seed does not synchronize clocks or file
timestamps. The fuzzer therefore does not validate current-time semantics,
timestamp updates, or time-dependent output and ordering. A match says nothing
about these behaviors.

In practice:

- Timestamps are still used to prepare fixtures, restore inputs and show raw
  diagnostics, but they are **excluded** from filesystem mismatch and replay
  decisions.
- Raw streams are still compared **exactly**. If a mismatch comes from a clock
  or timestamp difference, the result is inconclusive and needs manual
  investigation.
- There is no time tolerance, timestamp stripping or utility-specific time
  oracle.

Time-dependent inputs remain reachable. Read-only `ls -t -c` and
`ls -t --time=ctime` can reuse unchanged original objects on the `noatime`
fixture mount, so both targets see the same change timestamps. Timestamp
restoration avoids redundant writes: even setting atime/mtime to their existing
values with `utimensat` would advance ctime and invalidate exact reuse. The
saved ctime-order cases are checked by
`tools/fixtures/coreutils_fuzzer/v1/regressions/ls.json`.

This does not make clocks deterministic or allow ctime to be restored. If a
reference changes its fixture and requires an independent copy, time-dependent
stdout differences remain inconclusive under this policy. Excluding timestamps
from filesystem comparison does not exclude their effects on output bytes.

Generated option pools are restricted to the current benchmark scope, even
when informational output matches GNU's complete help text. The declared
scopes for `fold`, `seq`, `ls`, `stat`, `tee`, `tr` and `wc` apply to both
discovered options and an explicit `--opts` list. For example, character mode
(`fold -c`, `--characters`), custom numeric formats (`seq -f`, `--format`),
pipe/output-error policies (`tee -p`, `--output-error`), complement/truncation
(`tr -c`, `-C`, `-t`, `--complement`, `--truncate-set1`) and file-list input
(`wc --files0-from`) are outside these scopes. Supported options and malformed
uses of them remain eligible. Metrics record `generated_option_scope`,
`excluded_options` and the effective option pool; excluded options also appear
in the campaign log.

`stat` run cases retain an explicit `-c`/`--format` option during generation,
corpus mutation and shrinking. Help/version requests and missing format-value
errors remain eligible; default output without a format is not modeled. A
fixed case set is evaluated as supplied, so explicit diagnostic and historical
regression inputs are never silently removed.

Dafny specification and proof verification are separate checks.

<a id="support-a-new-utility"></a>

## 8. Support a new utility

All of a utility's input grammar and scenarios live in one module. Start from
[cat.rs](../tools/coreutils_fuzzer/src/fuzz/input/generators/cat.rs):

1. **Add the generator.** Create
   `tools/coreutils_fuzzer/src/fuzz/input/generators/<utility>.rs` and define
   `GENERATOR` with `PatternInputGenerator::patterned` (for a specialized
   `ARGV_PATTERN`) or `::generic` (when the common pattern fits). Include at
   least one deterministic, meaningful scenario.
2. **Declare the module** in
   [generators/mod.rs](../tools/coreutils_fuzzer/src/fuzz/input/generators/mod.rs).
3. **Register the capability** in
   [capabilities.rs](../tools/coreutils_fuzzer/src/utils/capabilities.rs), using
   the new generator and the required input/runtime policies.
4. **Try it.** Check that valid and error forms are reachable, run a real
   GNU/Dafny scenario through the wrapper, and confirm the new ID and duration
   fields appear in fresh metrics.

Then complete the
[utility contribution gate](../CONTRIBUTING.md#build-test-and-verify).

**Reuse shared helpers** (paths under `tools/coreutils_fuzzer/src/fuzz/`):

| Helper | Use for |
| --- | --- |
| `input/pattern.rs` | Argument assembly |
| `input/system_state.rs` | Shared filesystem inputs |
| `input/mutations.rs` | Common case and argument mutation |
| `input/support.rs` | Scalar values |

Keep utility-specific filesystem state and case constraints in the utility's
own module, wired in through `PatternInputGenerator` callbacks. A custom value
callback may generate one semantic value. Do not add another argument assembler
or utility-name dispatch to the common interpreter.

For example, a base32 contribution can adapt
[base64.rs](../tools/coreutils_fuzzer/src/fuzz/input/generators/base64.rs), a
small generic generator with fixed scenarios.

## Reference

### Where things live

| Path | Role |
| --- | --- |
| `tools/coreutils_fuzzer/run.py` | Contributor CLI and artifact discovery |
| `tools/coreutils_fuzzer/src/fuzz/` | Generation, execution, comparison, shrinking and evidence |
| `tools/coreutils_fuzzer/src/fuzz/input/generators/` | Per-utility patterns and deterministic scenarios |
| `tools/coreutils_fuzzer/src/utils/capabilities.rs` | Supported utility registry |
| `tools/coreutils_fuzzer/docker-compose.yaml` | Shared container execution policy |
| `tools/fixtures/coreutils_fuzzer/v1/` | Persistent case sets and fixed regression expectations |

### Schema versions and removed features

| Artifact | Current version |
| --- | --- |
| Capabilities | schema 4 (reports the time limitation) |
| Metrics | `coreutils-fuzzer.metrics.v3` (no time classifications) |
| Replay bundle | schema 8 (no checker/anchor provenance) |
| Failure-input bundle | `coreutils-fuzzer.failure-input.v2` (new execution context) |
| Case set | `coreutils-fuzzer.case-set.v1` |
| Regression suite | `coreutils-fuzzer.regression-suite.v1` |
| Private container protocol | 2 (no trace/anchor fields) |

The implementation-dependent `observed_spec_checker`, syscall tracing and clock
adapter have been removed, and `--checker`, `--ls-checker` and `--stat-checker`
are no longer supported. Old replay bundles must be rerun from their saved
inputs with `--case-set`; keep the original bundles.

### Maintenance validation: time checker removal (2026-09-30)

This is contributor-maintenance evidence, not an authorized input snapshot for
an evaluated benchmark run. Tested the working tree based on
`2f7558765e59dcbfe9862f3931ee0ff542801ad7`, including pre-existing concurrent
changes; no commit was created. Commands below ran from
`/workspace/dafnyutils/tools/coreutils_fuzzer` with Rust/Cargo 1.94.0,
Python 3.12.3, pytest 9.1.1 and Ruff 0.15.12.

- `cargo test --offline`: exit 0; 480 unit tests and two CLI integration tests
  passed. An initial run passed 480 tests and failed
  `chmod_explicit_mtime_mutation_is_detected`; that test depended on the removed
  timestamp verdict and was removed with the feature, then the suite passed.
- `PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -n0 -p no:cacheprovider
  /workspace/dafnyutils/tests/core/test_fuzzer_capabilities.py
  /workspace/dafnyutils/tests/core/test_benchmark_contribution.py
  /workspace/dafnyutils/tests/evaluation/test_fuzzer_outcomes.py
  --junitxml=target/maintenance/time-checker-removal/python-tests.xml`:
  exit 0; 50 tests passed, including real capability-producer/consumer
  conformance, malformed limitation rejection and legacy-schema rejection.
- `cargo fmt --all -- --check` and `git diff --check`: exit 0.
- `ruff check --no-cache` and `ruff format --check --no-cache` on
  `native/build.py`, `/workspace/dafnyutils/src/benchmarks/contribution.py` and
  `/workspace/dafnyutils/tests/core/test_fuzzer_capabilities.py`: exit 0.

Logs and the Python JUnit report are under
`tools/coreutils_fuzzer/target/maintenance/time-checker-removal/`. This maintenance
change does not alter benchmark specifications, implementations or their proofs.
No Dafny verification, `tests/bench` regression or GNU/Dafny benchmark campaign
was run; runtime tests do not establish proof success. The removed standalone
Dafny checker has no remaining verification target. Work is complete with no
blocking checks; the next operational step is to regenerate inputs/results for
any legacy replay bundle that needs to be rerun under schema 8.
