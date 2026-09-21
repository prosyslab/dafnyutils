## Change and scope

Describe the problem and resulting behavior. Give a small before/after example when useful.

- Task ID(s) and kind (coreutils / algorithm / tooling / documentation):
- Tested commit and any uncommitted changes:
- Working directory, OS/container image and tool versions:
- Changed specification / implementation / proof / evaluator / dataset boundaries:
- GNU source revision, URL/license and upstream test scenarios:
- Accepted input/environment/observation scope and trusted model/API revision:

Keep the evidence sections below in **tests → fuzzing → verification** order. Copy and paste actual stdout into each fenced `text` block. Include the command and exit code outside the block. Keep stderr separately if it contains warnings or failures; do not omit failed or skipped work. Use `not run` or `not applicable` with a reason instead of fabricated output. Attach full logs when an excerpt is necessary.

## 1. Test results

Run the affected utility's tests (for example, `make -C bench/utils/comm test`) and any affected source tests. Include the final passed/failed/skipped counts. A collected, deselected or all-skipped run is not passing evidence.

- Exact command(s):
- Exit code(s):
- Passed / failed / skipped; skipped-case reasons:
- Log / JUnit artifact links, or reason not run / not applicable:

```text
Paste actual test stdout here, including the final result summary.
```

## 2. Fuzzing results

For **each affected coreutils utility**, run generated campaigns with **three distinct seeds and at least 1,000 completed iterations per seed** (at least 3,000 total). All requested iterations must match, with **zero mismatches, timeouts, incomplete coverage and other errors**, and each run must exit 0. Use the same revision and full comparison settings, including stderr. A fixed JSON case set, repeating one seed, an early-stopped run or the short automatic contribution gate does not satisfy this requirement.

For example, select three seeds with `--seeds 1,7,19 --iterations 1000`. Keep `--metrics-out` evidence as well. Repeat this section for multiple utilities. For changes without an applicable coreutils campaign, state why; do not mark missing prerequisites as not applicable.

- Utility and exact command:
- Three distinct seeds and requested iterations **per seed**:
- GNU reference and DUT artifact paths, kinds and fingerprints:
- Fuzzer revision, container image identity and metrics/log links:
- Exit code(s), or reason not run / not applicable:

Paste the complete **Configuration, Coverage and Results** report for each seed. Keep the resolved limits, comparison settings, coverage gaps, requested/completed counts and final status visible. These runs show no mismatch within the tested population, not a proof of all behavior.

### Seed 1

```text
Paste actual stdout for the first seed here.
```

### Seed 2

```text
Paste actual stdout for a different second seed here.
```

### Seed 3

```text
Paste actual stdout for a different third seed here.
```

If a mismatch was fixed, also link the unchanged original bundle, replay command/verdict and separate fixed-regression stdout. Exact mismatch replay intentionally exits nonzero; its evidence is separate from the three successful campaigns above. Record failures and fixes rather than selecting only favorable seeds.

## 3. Verification results

Run Dafny verification for the affected files and all files they include (for example, `make -C bench/utils/comm verify`). Paste its stdout with the verified/error/timeout summary. A build or runtime test is not proof verification. Also report definition/layout validation and the final `make check TASK=<task-id>` gate; keep these results clearly labeled.

- Exact verification command and exit code:
- Verified files, included files, and termination limits:
- Verified / errors / timeouts:
- Definition/layout validation and final gate commands, outcomes and log links:
- Conditions still to prove, or reason not run / not applicable:

```text
Paste actual verification stdout here, including the final verifier summary.
```

## Contribution checks

- [ ] Code style, names and commit messages follow CONTRIBUTING.md; material co-authors are credited.
- [ ] Test, fuzzing and verification stdout is pasted in order, with commands and exit codes.
- [ ] Each affected coreutils utility has three distinct seeds with at least 1,000 completed matches each and no failures, or an explicit explanation of missing/inapplicable evidence.
- [ ] Evidence identifies the tested revision; affected checks were rerun after later code changes.
- [ ] Logs are accessible and contain no credentials or restricted evaluator payloads.
- [ ] Evaluator-only cases and oracle material are not public task resources.
- [ ] Specifications, allowed inputs and required checks were not weakened; no unchecked externs, assumptions or verification skips were added to obtain a pass.

## Human specification review (maintainers)

- Reviewer:
- Accepted scope and positive/negative specification evidence:
- Declarative specification and trusted-library boundary assessment:
- Proof/termination limits and required corrections:
- Decision (pending / changes requested / approved / not applicable with reason): pending

Passing automated checks does not approve this review. This template records evidence; it does not itself run or enforce CI checks.
