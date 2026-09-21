# Run the coreutils fuzzer

Use the fuzzer to compare the pinned GNU executable with your built Dafny executable under the same generated inputs. Keep a mismatch bundle, fix the cause, and use a separate regression expectation to show the corrected behavior.

A matching campaign is finite runtime evidence. It is not a Dafny proof or approval of the specification.

## Contents

- [Prepare the targets and runner](#prepare-the-targets-and-runner)
- [Run a campaign](#run-a-campaign)
  - [Check capability support](#check-capability-support)
  - [Compare generated inputs](#compare-generated-inputs)
  - [Collect PR evidence](#collect-pr-evidence)
  - [Run an exact scenario](#run-an-exact-scenario)
- [Read the result and preserve evidence](#read-the-result-and-preserve-evidence)
  - [Interpret outcomes](#interpret-outcomes)
  - [Replay the original mismatch](#replay-the-original-mismatch)
  - [Inspect metrics](#inspect-metrics)
- [Create an exact case set](#create-an-exact-case-set)
- [Run and inspect the comparison](#run-and-inspect-the-comparison)
- [Record a fixed regression](#record-a-fixed-regression)
- [Understand execution limits](#understand-execution-limits)
- [Support a new utility](#support-a-new-utility)

## Prepare the targets and runner

Use the [setup guide](../README.md#setup). Run commands in Bash or zsh from the repository root. Clear any old `REF_BIN_TEMPLATE`, `DUT_BIN_TEMPLATE`, `EVAL_REPO_ROOT` or `EVAL_TARGET_ROOT` overrides before comparing normal project artifacts.

```sh
# Expected duration: Usually under a second after setup.
# Success criteria: Exit 0 and capabilities, fuzz, regression and replay appear.
python3 tools/coreutils_fuzzer/run.py --help
```

This checks the Python wrapper without executing a target. Expected usage line:

```text
Usage: run.py [OPTIONS] COMMAND [ARGS]...
```

Build prerequisites separately; do not count setup time as campaign time.

```sh
# Expected duration: Unknown; first GNU build depends on downloads and CPU.
# Success criteria: Exit 0 and _build/coreutils/src/cat exists and is executable.
make build-coreutils
```

Expected final output, exit 0:

```text
...
make[1]: Leaving directory '/workspace/dafnyutils/_build/coreutils'
```

```sh
# Expected duration: Unknown; depends on Dafny translation and .NET restore/build.
# Success criteria: Exit 0 and _build/bench/cat_bench.dll exists.
make -C bench/utils/cat build
```

Expected output, exit 0:

```text
Dafny program verifier did not attempt verification
make: Leaving directory '/workspace/dafnyutils/bench/utils/cat'
```

```sh
# Expected duration: Unknown; requires Docker access and image/dependency downloads.
# Success criteria: Exit 0 and dafnyutils-coreutils-fuzzer:latest is built.
docker compose -f tools/coreutils_fuzzer/docker-compose.yaml build
```

Expected final output, exit 0:

```text
...
Image dafnyutils-coreutils-fuzzer:latest Built
```

The first command builds the pinned GNU binary. The second builds the utility
under test (DUT). The third builds the execution image. The wrapper also builds
its Rust runner with Cargo when needed, which may download dependencies on a
fresh machine.

| Path | Role |
| --- | --- |
| `tools/coreutils_fuzzer/run.py` | Contributor CLI and artifact discovery |
| `tools/coreutils_fuzzer/src/fuzz/` | Generation, execution, comparison, shrinking and evidence |
| `tools/coreutils_fuzzer/src/fuzz/input/generators/` | Per-utility patterns and deterministic scenarios |
| `tools/coreutils_fuzzer/src/utils/capabilities.rs` | Supported utility registry |
| `tools/coreutils_fuzzer/docker-compose.yaml` | Shared container execution policy |
| `tools/fixtures/coreutils_fuzzer/v1/` | Persistent case sets and fixed regression expectations |

## Run a campaign

### Check capability support

```sh
# Expected duration: Estimated < 1 sec with a built runner; first Cargo build is extra.
# Success criteria: Exit 0 and a registry entry for your utility.
python3 tools/coreutils_fuzzer/run.py capabilities
```

Expected output, exit 0:

```text
cat fuzz=custom scenarios=yes time-coverage=none
ls fuzz=custom scenarios=yes time-coverage=exact_per_execution
```

Read the utility's generator, scenario support and time-coverage requirement before
running it. A manifest or DLL does not register a new fuzzer capability. The
registry is defined in `src/utils/capabilities.rs` within the fuzzer tree.

### Compare generated inputs

```sh
# Expected duration: Unknown; 20 paired executions plus possible mismatch shrinking.
# Success criteria: Exit 0, all 20 cases match, and fresh metrics are written.
python3 tools/coreutils_fuzzer/run.py fuzz cat   --iterations 20 --seed 1 --metrics-out /tmp/cat-seed1-metrics.json
```

Expected Results section for a passing run, exit 0:

```text
Results
  Iterations : requested=20 submitted=20 completed=20 not_started=0 unfinished=0
  Outcomes   : match=20 mismatch=0 timeout=0 incomplete_coverage=0 other_errors=0
  Elapsed    : <seconds>s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
```

This selects `_build/coreutils/src/cat` and `_build/bench/cat_bench.dll`, generates
inputs, and stops at the first non-match. The runner prints Configuration,
Coverage and Results sections and writes per-case evidence to the metrics file.
Use a fresh output path: metrics are not overwritten.

`--seed` makes input generation repeatable under the same runner and configuration. It does not freeze clocks, binary contents or the host environment. Use `--seeds 1,7,19` for several campaigns; multiple seeds or utilities receive separate output names. `--all-built` selects registered utilities with built Dafny DLLs.

Default process timeout is 10 seconds per reference/DUT process. `--process-timeout-seconds` changes that limit; it does not turn a timeout into a semantic match. `--shrink-attempts 0` disables minimization when you want the exact case unchanged.

To compare other artifacts, set `REF_BIN_TEMPLATE` and `DUT_BIN_TEMPLATE` with a `{util}` placeholder and choose the correct `--ref-kind`/`--dut-kind` (`native` or `dotnet-dll`). Report these overrides. Comparing GNU with itself can check the harness but is not evidence about a Dafny utility.

### Collect PR evidence

Run **three distinct seeds with at least 1,000 iterations per seed** for each affected coreutils utility. Every requested iteration must complete as a match, with no mismatch, timeout, incomplete coverage or other error. Keep the same code revision and include stderr comparison. Record unsuccessful campaigns and fixes too; do not search for three favorable seeds while omitting failures.

```sh
# Expected duration: Unknown; at least 3,000 paired target executions, plus any shrinking.
# Success criteria: Exit 0; all three seeds complete 1,000 matches each, with no failures.
python3 tools/coreutils_fuzzer/run.py fuzz comm \
  --seeds 1,7,19 --iterations 1000 \
  --metrics-out '/tmp/comm-pr-{seed}.json'
```

Expected Results section **for each of seeds 1, 7 and 19**, exit 0:

```text
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 incomplete_coverage=0 other_errors=0
  Elapsed    : <seconds>s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
```

Keep each seed's Configuration and Coverage sections too; they are omitted here
only to make the expected completion counts easier to find.

Replace `comm` with the affected utility and choose fresh metrics paths. This
selects seeds 1, 7 and 19 and writes one JSON file per seed. The automatic
`make check` gate uses only 20 cases and seed 1, so it cannot replace this evidence.
A fixed JSON case set is a separate regression check and does not satisfy the
generated-campaign requirement.

Stdout now groups each campaign into **Configuration**, **Coverage** and **Results**:

- Configuration identifies the seed, requested budget, target paths/kinds, input source, limits, stderr policy, work directory mode, container image/identity and metrics path.
- Coverage shows observed option singles/pairs and semantic buckets, including gaps. These are generated-input coverage measures, not source-code coverage or proof of all behavior.
- Results shows requested/submitted/completed iterations, unstarted/unfinished work, matches, mismatches, timeouts, incomplete observations, other errors, elapsed time and PASS/FAIL. Completed errors are not matches. PASS is printed only after any requested metrics file is successfully saved.

Copy each seed's complete report into its `text` block in the [PR template](../.github/pull_request_template.md), after the test stdout and before the verifier stdout. Record command and process exit status separately. Keep stderr if it reports failure details. A setup failure may stop before a result report; missing output is never proof of success. The wrapper stops when a seed fails, so unstarted later seeds still need execution after the cause is fixed.

For a passing run, `requested`, `submitted`, `completed` and `match` must all
equal the requested budget, with every error count zero. `not_started` counts
cases never submitted; `unfinished` counts submitted cases with no result.

Option percentages count observed options and pairs. Semantic buckets count
observed behaviors. A missing bucket can be normal (for example, `true` does not
create files). An `incomplete_coverage` outcome instead means a required
observation is missing, so that case cannot count as a match.

Use your own campaign logs as PR evidence.


### Run an exact scenario

Use the complete [split-CRLF example](#create-an-exact-case-set) to reproduce one upstream scenario. Pass its JSON with `--case-set` and set `--iterations` to the exact number of stored cases. Explicit cases are consumed unchanged. They replace random generation for that run and need no per-case registry edit.

## Read the result and preserve evidence

### Interpret outcomes

The runner compares process outcomes, stdout/stderr evidence, filesystem contents/metadata and identity transitions in independent fixture trees. Its comparator owns normalization; do not suppress stderr or add output rewriting to obtain a pass. In particular, do not compare absolute host inode numbers across separate fixtures.

| Result | Contributor action |
| --- | --- |
| `match` | Record the completed population and configuration; continue required proof/review work |
| `semantic_mismatch` | Preserve the bundle and determine which implementation or contract is wrong |
| `incomplete_coverage` | Obtain the missing observation; do not report a match |
| `fuzzer_timeout` | Record the timed-out case and diagnose the deadline |
| `fuzzer_unsupported_capability` | Implement/review the utility's generator registration |
| `fuzzer_target_spawn_failure`, `fuzzer_dotnet_runtime_failure` | Fix the missing/unusable binary or runtime |
| `fuzzer_infrastructure_failure`, `fuzzer_build_failure` | Fix Docker/build prerequisites and rerun |
| `replay_not_reproduced` | New complete verdict differs from the saved verdict |
| `regression_failure` | At least one fixed expectation failed |

Failure output uses `FUZZER_OUTCOME=<value>` where classified. Keep the original command and log as well as the bundle. A setup error can happen before case metrics exist.

On an early mismatch, the report keeps the unused budget visible. For example,
a 1,000-case run that stops on its first mismatch has one completed case and 999
not started. Keep stderr and the original bundle too; a partially completed
campaign does not meet the PR requirement.

### Replay the original mismatch

Copy the bundle path printed by the failed run. In the following command, replace `/tmp/coreutils-fuzzer-repros/cat-example` with that real path.

```sh
# Expected duration: Unknown; depends on the saved case and target startup.
# Success criteria: The complete saved mismatch verdict is reproduced, with a nonzero exit.
python3 tools/coreutils_fuzzer/run.py replay /tmp/coreutils-fuzzer-repros/cat-example
```

Expected classified outcome when the saved mismatch is reproduced (nonzero exit;
diagnostic wording and paths vary):

```text
...
FUZZER_OUTCOME=semantic_mismatch
...
```

Exact reproduction reports `semantic_mismatch` and exits nonzero by design.
A corrected program that now matches reports `replay_not_reproduced`, also nonzero.
Test fixed behavior with a [regression suite](#record-a-fixed-regression), not by
rewriting the original bundle.

Replay accepts current schema 6 only. It retains raw metadata, typed process outcomes, container-image identity and numeric target identity. Old schemas are rejected. Without an image override, replay uses the saved image identity. Bundles have no signature, so they do not prove who created them.

### Inspect metrics

Metrics schema `coreutils-fuzzer.metrics.v1` records requested/submitted/completed/abandoned counts and each case's ID, input fingerprint, outcome and stage durations in nanoseconds. Inspect these fields with the [complete result-checking example](#run-and-inspect-the-comparison).

Compare performance only with the same cases, binary/input fingerprints, seeds, deadlines, comparison settings and host conditions. A small run establishes execution and reporting; it does not establish a performance improvement.

## Create an exact case set

This optional fuzzer example adapts split-CRLF behavior from [coreutils/tests/cat/cat-E.sh](../coreutils/tests/cat/cat-E.sh). Prepare the Cat targets and execution image as described above. Python tests in a utility's `Tests.py` are explained in [Add test cases](adding-test-cases.md).

Save this complete file as `/tmp/dafnyutils-cat-crlf.json`:

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

`49` and `50` are `1` and `2`; `13` is CR and `10` is LF. Mode `420` is decimal `0644`. Paths are relative to the fixture root. Use a stable unique ID. Add a second scenario as a separate case rather than mixing unrelated success and error behavior into one case.

For a permanent contribution, add the case to `tools/fixtures/coreutils_fuzzer/v1/cases/cat.json` without replacing existing cases. Explicit `--case-set` selection loads it; a filename alone does not add it to every campaign. The utility must already have a capability registration. If the selected set has N cases, pass `--iterations N`.

## Run and inspect the comparison

```sh
# Expected duration: Unknown; requires built targets and an accessible Docker daemon/image.
# Success criteria: Exit 0, one completed match, and metrics containing the new case ID.
python3 tools/coreutils_fuzzer/run.py fuzz cat \
  --case-set /tmp/dafnyutils-cat-crlf.json \
  --iterations 1 --shrink-attempts 0 \
  --metrics-out /tmp/pr-fuzzer-cat-crlf.json
```

Expected Results section for this one stored case, exit 0:

```text
Results
  Iterations : requested=1 submitted=1 completed=1 not_started=0 unfinished=0
  Outcomes   : match=1 mismatch=0 timeout=0 incomplete_coverage=0 other_errors=0
  Elapsed    : <seconds>s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
```

This executes the exact stored inputs against the original GNU binary and the Dafny DLL. Shrinking is disabled to keep this scenario unchanged. It compares streams, process outcome and filesystem observations through the existing comparator. Choose a fresh metrics path for another run.

```sh
# Expected duration: Estimated < 1 sec; reads one local JSON result.
# Success criteria: Exit 0, the expected ID is match, and integer duration fields are present.
python3 - <<'CHECK'
import json
from pathlib import Path

report = json.loads(Path('/tmp/pr-fuzzer-cat-crlf.json').read_text())
assert report['schema_version'] == 'coreutils-fuzzer.metrics.v1'
assert report['completed'] == 1
case = report['cases'][0]
assert case['id'] == 'upstream-cat-E-crlf-across-files'
assert case['outcome'] == 'match'
assert case['durations'] and all(isinstance(v, int) for v in case['durations'].values())
print(case['id'], case['outcome'])
print(case['durations'])
CHECK
```

Expected output shape, exit 0 (integer timings vary):

```text
upstream-cat-E-crlf-across-files match
{'source_ns': <int>, 'evaluation_ns': <int>, 'coverage_ns': <int>, 'shrink_ns': <int>, 'persist_ns': <int>, 'queue_wait_ns': <int>}
```

This checks that the named case actually completed as a match, not just that
a metrics file exists. Durations are measured in nanoseconds and vary by run.

On a mismatch, keep the generated repro bundle and log. Diagnose whether the problem is in the utility, its specification, the adapter, or the test setup. Do not rewrite the expected output, ignore stderr, relax comparison, or modify the original bundle to obtain a match. See [replay semantics](#replay-the-original-mismatch).

## Record a fixed regression

Save this complete file as `/tmp/dafnyutils-cat-crlf-regression.json` after a fix or when retaining the case as a stable parity expectation:

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

`case_set` is relative to the suite file, not the shell's directory. JSON must not have trailing commas. For permanent storage, put the expectation in `tools/fixtures/coreutils_fuzzer/v1/regressions/cat.json` and use `../cases/cat.json`; preserve existing expectations.

```sh
# Expected duration: Unknown; one paired execution with the prepared Docker targets.
# Success criteria: Exit 0 and the named match expectation passes.
python3 tools/coreutils_fuzzer/run.py regression /tmp/dafnyutils-cat-crlf-regression.json \
  --metrics-out /tmp/dafnyutils-cat-crlf-regression-metrics.json
```

Expected success message:

```text
Regression suite passed for util=cat expectations=1
```

The suite asserts current GNU/Dafny parity. It does not replace the immutable historical mismatch bundle. A replay can stop reproducing after a fix while this separate regression passes.

## Understand execution limits

The host manages one disposable Compose service, copies the runner and target artifacts into it, collects observations, and removes that service. GNU and Dafny execute inside it, including option discovery. There is no host-target fallback and no public wrapper `--work-root` option.

Both targets share the service filesystem and staged executables. Docker provides the host boundary; there is no extra per-target filesystem or oracle isolation. The service has no Docker socket, no external network, a read-only root, and writable staging/fixture tmpfs mounts. It retains default Docker seccomp/AppArmor protections and `no-new-privileges`. Trusted setup uses limited ownership/identity capabilities; target children run under the runner's non-root identity.

The target environment is cleared and then receives controlled values including `LANG=C`, `LC_ALL=C`, `TZ=UTC0`, `TERM=dumb`, `QUOTING_STYLE=literal` and a fixed `PATH`. Host credentials are not inherited. Unsafe fixture paths, escaping symlinks and invalid links are rejected.

GNU and Dafny start at different times. A common seed does not synchronize their clocks. `ls` and `stat` require exact per-execution time evidence; missing evidence is `incomplete_coverage`. The optional clock adapter alone does not supply complete campaign capture. Do not disable timestamp comparisons to make a case pass.

## Support a new utility

Keep input grammar and scenarios in one utility module. Start from [cat.rs](../tools/coreutils_fuzzer/src/fuzz/input/generators/cat.rs), then:

1. Add `src/fuzz/input/generators/<utility>.rs` in the fuzzer tree. Define its `GENERATOR` with `PatternInputGenerator::patterned` for a specialized `ARGV_PATTERN`, or `::generic` when the common pattern fits. Include at least one deterministic meaningful scenario.
2. Declare the module in [generators/mod.rs](../tools/coreutils_fuzzer/src/fuzz/input/generators/mod.rs).
3. Add the utility's capability record in [capabilities.rs](../tools/coreutils_fuzzer/src/utils/capabilities.rs), using the new generator and the required observation policy.
4. Check reachable valid/error forms and run a real GNU/Dafny scenario through the wrapper. Verify the new ID and duration fields in fresh metrics.

Reuse `input/pattern.rs` for argument assembly, `input/fixtures.rs` for fixtures,
and `input/support.rs` for scalar values. For a base32 contribution,
[base64.rs](../tools/coreutils_fuzzer/src/fuzz/input/generators/base64.rs) is a small
example of a generic generator with fixed scenarios; adapt its inputs to base32.
A custom value callback may generate one semantic value; do not add another
argument assembler or utility-name dispatch to the common interpreter. Complete
the [utility contribution gate](../CONTRIBUTING.md#build-test-and-verify) after registration.
