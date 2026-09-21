## Change and scope

Describe the problem and resulting behavior. Give a small before/after example when useful.

- Task ID(s) and kind (coreutils / algorithm / tooling / documentation):
- Tested commit and any uncommitted changes:
- Working directory, OS/container image and tool versions:
- Changed specification / implementation / proof / evaluator / dataset boundaries:
- GNU source revision, URL/license and upstream test scenarios:
- Accepted input/environment/observation scope and trusted model/API revision:

Keep the evidence sections below in **tests → fuzzing → verification** order. Copy and paste actual stdout into each fenced `text` block. Include the command and exit code outside the block. Keep stderr separately if it contains warnings or failures; do not omit failed or skipped work. Use `not run` or `not applicable` with a reason instead of fabricated output.

## Options left out due to IO.dfy

Leave out options that cannot be implemented with the current API in
`bench/core/IO.dfy`. List each option and explain what API support is missing.
Keep this list in the utility's scope document too. If an option is already
required by an agreed task, ask a maintainer to review the scope or API change
before implementation. Write `None` if no options were left out for this reason.

| Utility | Option left out | Missing API support |
| --- | --- | --- |
| | | |

## 1. Test results

Run the commands below from the repository root in the contributor container.
Replace `<utility_name>` with your utility name before running each command.

```sh
make -C 'bench/utils/<utility_name>' test
```

Also run any affected source tests. Include the final passed/failed/skipped counts.
A run with no tests executed does not count as a pass.

- Exact command(s):
- Exit code(s):
- Passed / failed / skipped; skipped-case reasons:
- Reason not run / not applicable, if any:

```text
Paste actual test stdout here, including the final result summary.
```

## 2. Fuzzing results

For **each affected coreutils utility**, run generated campaigns with **three distinct seeds and at least 1,000 completed iterations per seed** (at least 3,000 total). All requested iterations must match, with **zero mismatches, timeouts, incomplete coverage and other errors**, and each run must exit 0. Use the same revision and full comparison settings, including stderr. A fixed JSON case set, repeating one seed, an early-stopped run or the short automatic contribution gate does not satisfy this requirement.

Run this command from the repository root in the contributor container after
building the utility. Replace `<utility_name>` with your utility name.
Keep all other values unchanged. Do not choose other seeds.

```sh
python3 tools/coreutils_fuzzer/run.py fuzz '<utility_name>' \
  --seeds 1,7,19 --iterations 1000
```

Each seed must report 1,000 completed matches, no errors and exit code 0.
Paste the full stdout below without changes. No file attachments are needed.
Repeat this section for each affected utility. If fuzzing does not apply,
explain why. Missing tools or files are a reason for `not run`, not `not applicable`.

- Utility and exact command:
- Required seeds: `1,7,19`; requested iterations per seed: `1000`.
- GNU reference and DUT artifact paths, kinds and fingerprints:
- Fuzzer revision and container image identity:
- Exit code(s), or reason not run / not applicable:

Paste the full stdout from the command above into this one block.
The command runs seeds `1`, `7` and `19` in order and prints their results together.
Do not split or edit the output. If the command fails, paste its stdout too and
report the exit code above. Keep any stderr in a separate block.

```text
Paste the full stdout from the fuzzing command here.
```

If a mismatch was fixed, keep the original bundle unchanged locally. Paste the replay command, its result and the stdout from the test after the fix. Exact mismatch replay intentionally exits nonzero; its evidence is separate from the three successful campaigns above. Record failures and fixes rather than selecting only favorable seeds.

## 3. Verification results

Run Dafny verification for the affected files and all files they include:

```sh
make -C 'bench/utils/<utility_name>' verify
```

Paste its stdout with the verified/error/timeout summary.
A build or runtime test is not proof verification.

Check the utility definition:

```sh
python3 -m benchmarks validate '<utility_name>'
```

Run the final checks, including layout checks:

```sh
make check TASK='<utility_name>'
```

Report the output and exit code for each command. Keep the results separate.

- Exact verification command and exit code:
- Verified files, included files, and termination limits:
- Verified / errors / timeouts:
- Definition/layout validation and final gate commands and results:
- Conditions still to prove, or reason not run / not applicable:

```text
Paste actual verification stdout here, including the final verifier summary.
```
