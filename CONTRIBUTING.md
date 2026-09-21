# Contributing to Dafnyutils

Submit a focused change with reproducible code verification and fuzzing results. Use the four guides below for implementation details, then report the results in the [pull request template](.github/pull_request_template.md).

## Contents

- [Choose a guide](#choose-a-guide)
- [Prepare the change](#prepare-the-change)
- [Coding style](#coding-style)
  - [Python](#python)
  - [Dafny and proofs](#dafny-and-proofs)
  - [Tests and documentation](#tests-and-documentation)
- [Naming conventions](#naming-conventions)
- [Commit messages](#commit-messages)
- [Show verification and fuzzing results](#show-verification-and-fuzzing-results)
- [Open the pull request](#open-the-pull-request)

## Choose a guide

| Your task | Guide |
| --- | --- |
| Set up the environment and add a utility through review | [Add a utility](docs/adding-utilities.md) |
| Use shared APIs and understand what the proof trusts | [Core API and library assumptions](docs/core-api.md) |
| Run campaigns, inspect metrics and replay failures | [Use the fuzzer](docs/fuzzing.md) |
| Port a GNU scenario into a utility’s Python tests | [Add differential test cases](docs/adding-test-cases.md) |

Start with the [setup guide](README.md#setup). For a new utility, check [TODOLIST.csv](TODOLIST.csv) and follow the [scope review step](docs/adding-utilities.md#agree-on-the-observable-behavior) before implementation. Follow [repository instructions](AGENTS.md), [bench rules](bench/AGENTS.md) and [Dafny style](DAFNYSTYLE.md).

## Prepare the change

Explain the problem, the intended behavior and the files affected. Keep specification, implementation, proof and evaluator changes distinct. Reuse shared helpers and keep the approved inputs and library assumptions unchanged.

Use a draft PR for the work plan and maintainer discussion. Put the accepted
utility scope in `bench/utils/<utility>/<utility>.md`. Keep progress notes in the
draft PR using these fields: **completed work, remaining work, blockers, commands
and results, artifact links, next action**. Before a PR exists, local notes may
live under `_build/contribution-notes/`; copy relevant evidence into the PR so
reviewers can access it. No separate wiki or plan directory is required.

These are contributor-maintenance records. Evaluated benchmark runs must follow
their own permitted-input and artifact rules; do not feed these notes into a run
unless its protocol permits them.

For an upstream scenario, record the GNU source revision and test path. Keep evaluator cases and oracle material out of candidate-visible resources. Preserve original mismatch bundles and store post-fix expectations separately.

## Coding style

Follow the surrounding code and reuse existing helpers before adding new ones. Keep changes focused on the requested behavior. Fix the cause of a failure instead of hiding it behind a fallback. Ask maintainers before adding a package, library or new behavioral heuristic.

### Python

Use Python 3.12 or newer, four-space indentation, and the 100-character line length configured in [pyproject.toml](pyproject.toml). Add type annotations to new interfaces. Ruff checks include import order and complexity; the configured complexity limit is 10. Follow the existing [CI checks](.github/workflows/benchmark.yml), which also run Pyright.

- Import a name from the module that defines it. For example, use `from benchmarks.definition import BenchmarkKind`, not a package-root re-export.
- Keep `__init__.py` empty. Do not use wildcard imports, `__all__`, `importlib` or import tricks to avoid redesigning a cyclic dependency.
- Use `dataclass` for structured internal data and Pydantic `BaseModel` for data read from or written to external JSON. See [definition.py](src/benchmarks/definition.py) for both patterns.
- Use `Enum` for a fixed set of string values, not `Literal`. Give a constant one canonical name; do not create a second constant that aliases it.
- Use triple double quotes (`"""`) for multiline strings and docstrings.
- Catch specific expected exceptions only around external operations such as file reads, API calls or external-data parsing. Do not wrap the whole workflow or suppress programming errors.

### Dafny and proofs

Read [DAFNYSTYLE.md](DAFNYSTYLE.md) and [bench/AGENTS.md](bench/AGENTS.md). Use the existing two-space indentation and write the contract before the implementation.

Keep declarative behavior and fixed user-facing text in `*Spec.dfy`, algorithms in `*Core.dfy`, and connecting lemmas in `*Proof.dfy`. Spec must not import Core, Proof or CLI. The entry `RunCore` must directly ensure its main specification, `Spec(...)`; a helper lemma alone is insufficient.

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
documentation updates. Keep the work record in the draft PR as described above.
If an agent is helping, it must create commits only when you explicitly request them.

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

After a blank line, include a detailed body explaining the problem, approach, affected boundaries, validation commands and actual results, and remaining limitations or follow-up work. This is a message template, not a record of completed checks:

```text
[Docs] explain contribution evidence requirements

Problem: <what was unclear or incorrect>
Approach: <what changed and why>
Boundaries: <specification, implementation, proof, evaluator or dataset impact>
Validation: <exact commands, tested revision, results and artifact links>
Limitations: <unrun checks, remaining risks or follow-up; say none if appropriate>

Co-authored-by: Full Name <email>
```

Replace the template fields with facts. Include an accurate `Co-authored-by: Full Name <email>` trailer for every material co-author, including Codex when it contributed. Use the contributor's actual configured identity; do not invent an email or copy the placeholders. Keep required trailers at the end of the message.

## Show verification and fuzzing results

Report evidence in **tests → fuzzing → verification** order. Copy and paste actual stdout into the template's fenced `text` blocks, with the exact command and exit code alongside it. Include final summaries and explain failed, skipped, unrun or inapplicable work. A missing tool, timeout or skipped required check is not a pass.

- **Tests:** Show the affected runtime/source test results with passed, failed and skipped counts, plus a log or JUnit link.
- **Fuzzing:** For each affected coreutils utility, use three distinct seeds with at least **1,000 completed iterations per seed**. Every requested iteration must match, with zero mismatches, timeouts, incomplete coverage or other errors. Paste each seed's Configuration, Coverage and Results stdout and retain metrics. Use generated campaigns, full comparison including stderr, and the same code revision. Repeated seeds and fixed JSON cases do not meet this requirement. Record failures and fixes rather than selecting only favorable runs.
- **Verification:** Show Dafny stdout with verified/error/timeout counts and the verified files, their included files, and whether termination was proved. Also report definition/layout checks and the final contribution gate. A build is not proof verification.

The short automatic gate currently runs 20 fuzz cases with seed 1; it does not satisfy the separate PR requirement of three campaigns with at least 1,000 iterations each. See [Collect PR evidence](docs/fuzzing.md#collect-pr-evidence) for the command.
For example, a one-case differential run should identify its case ID and completed outcome; a proof result should identify the verified files, their included files, and the verifier summary. Copy actual results from the run. Do not treat example output in a guide as evidence for your PR.

See [validation commands](docs/adding-utilities.md#validate-and-submit) and the [metrics example](docs/fuzzing.md#run-and-inspect-the-comparison). Link uploaded PR or CI artifacts that reviewers can access; a local `/tmp` path alone is not a shared log. Never include credentials or restricted evaluator payloads.

Algorithm tasks do not require the coreutils fuzzer; report their case tests instead and explain `not applicable` in the fuzzing section. For documentation-only changes, record link/content checks and explain why runtime verification and fuzzing were not run.

## Open the pull request

Use a short title and explain the resulting behavior first. Complete the template's scope and evidence fields, attach relevant reports, and list remaining failures or limitations. Rerun affected checks after code changes and identify the revision each result covers.

Maintainers check whether the specification describes the required behavior and
uses only approved library contracts, separately from automated checks. Leave
their review decision pending until a human reviewer records it. Passing tests,
fuzzing and Dafny verification does not automatically approve the specification.
