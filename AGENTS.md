# Repository Agent Instructions

## Purpose

This repository is a verification-oriented benchmark workspace for evaluating
coding agents that use Dafny to produce program specifications, implementations,
and proofs, including tasks involving GNU coreutils.

Preserve the boundaries between specification, implementation, proof, evaluation,
and benchmark integrity. Passing tests alone is not the objective.

## Instruction scope

- Follow applicable repository and directory-level instructions, subject to
  higher-priority instructions and execution permissions.
- Read additional instructions governing files you will edit.
- Subdirectory instructions may specialize this workflow, but must not silently
  weaken its evidence or benchmark-integrity requirements.
- Do not modify instructions merely to bypass a restriction on the current task.

## Required workflow: inspect -> implement -> verify -> document

### 1. Inspect and recover context

- Establish whether the task is repository maintenance or an evaluated benchmark
  run. Apply the evaluation-memory boundary below before reading prior records.
- Inspect the working tree and relevant source, specifications, tests, and build
  configuration. Preserve unrelated and pre-existing changes.
- Search for existing helpers, types, lemmas, and similar behavior before designing
  replacements.
- Resolve unclear requirements by inspecting available evidence. If behavior,
  scope, or constraints remain unclear, ask the user before implementing. Do not
  silently choose an interpretation that changes the task's meaning.

### 2. Implement

- Keep changes small and focused on the requested task.
- Obtain any newly required approval before making the corresponding change.
- Capture useful findings and failed approaches with evidence as they occur.

### 3. Verify and preserve knowledge

- Run the relevant checks and record commands, working directories, relevant
  versions, tested revision or working-tree state, outcomes, and skipped checks
  with reasons. Distinguish test success from Dafny verification success.
- If a code change invalidates documented knowledge, update that knowledge or
  mark it `stale` with a reason in the same change set.

### 4. Close or hand off accurately

- Review the final diff against the requested scope.
  Remove unrelated edits without discarding pre-existing user changes.
- Report completion only when acceptance criteria and required checks are
  satisfied, or an authorized scope change explicitly removes a requirement.
  An environment blocker or an unrun required check is not a passing result.
- Before stopping, record completed work, remaining work, blockers, relevant
  process/artifact locations, and the next concrete action.
- Report changes, validation results, and limitations in the final response.
  Do not claim work is complete merely because a process started.

## Benchmark integrity and evaluation-memory boundary

- Treat task-provided specifications, allowed inputs, expected behavior, proof
  scope, evaluator behavior, and scoring rules as fixed unless the task explicitly
  authorizes changes to those layers. Identify affected layers.
- Do not weaken specifications, remove meaningful checks, narrow benchmark inputs,
  hardcode benchmark answers, or change evaluation behavior to obtain a pass.
- Do not introduce unproved assumptions, trust annotations, or verification skips
  to manufacture proof success. Preserve the intended proof obligations.
- Do not inspect or copy evaluator-only tests, hidden expected outputs, reference
  solutions, or other prohibited material into candidate-visible files or prompts.
- Development memory is not automatically authorized benchmark input.
  Prior proofs and solutions can disclose answers. This restriction includes
  their index entries, not just document bodies.
- In an evaluated run, read only records explicitly permitted by the evaluation
  protocol. If memory permissions are unspecified, stop and clarify before reading
  prior task-specific records. A document label does not grant access permission.
- Use run-isolated documentation snapshots unless the protocol explicitly permits
  shared memory. Record the permitted document snapshot and material read in the
  run's authorized manifest. Do not silently feed new findings into later
  evaluation runs or alter a running evaluation's inputs.
- Keep restricted findings in the protocol's authorized artifact location.
  Permission to share development knowledge is not permission to
  contaminate benchmark evaluation.

## Implementation and dependencies

- Reuse existing helpers, data types, abstractions, and lemmas. Do not duplicate
  behavior merely because its current location is inconvenient.
- Fix root causes instead of masking failures with fallback behavior. Add a new
  behavioral heuristic only with explicit human approval.
- Use exception handling only at external boundaries such as API calls, file I/O,
  or external-data parsing. Catch specific, expected exceptions around the smallest
  relevant operation. Do not wrap an entire workflow or suppress programming bugs.
- Do not add speculative exception handling for failures without a concrete basis.
- Request approval before adding a package or library. Do not evade that approval
  by reimplementing a library-sized substitute from scratch.
- Creating an independent Git worktree is allowed, subject to execution
  permissions. Preserve other worktrees and unrelated changes; never remove or
  reset another task's work as cleanup.

## Build

- If the relevant project has a `Makefile`, use its supported build targets.
  Inspect the file and project documentation; do not invent target names.
- Prefer existing test and verification targets when they provide the required
  scope. If a required target or prerequisite is unavailable, record the blocker
  and resolve it rather than silently bypassing the build procedure.

## Python

- Import names from their defining modules; do not create package-root re-export
  facades. Keep `__init__.py` files empty, and do not use wildcard imports or
  define `__all__`.
- Give each constant one canonical name. Do not create aliases by assigning one
  constant to another constant.
- Use `dataclass` for structured internal data and Pydantic `BaseModel` for models
  read from or written to external JSON. Dependency approval still applies if
  Pydantic is not already available.
- Use `"""` for multiline strings.
- Use `Enum`, not `Literal`, for a type representing a fixed set of string values.
- Never use `importlib` or import-related tricks. Resolve cyclic imports by
  redesigning module boundaries.

## Tests

- Add realistic, bug-triggerable tests of observable behavior. Do not add ad hoc
  cases merely to exercise the implementation you just wrote.
- Each test must cover one scenario, either a normal case or an error case.
  Add a one-line intention comment immediately above the test or its decorators.
- Do not test whether a prompt substring appears or does not appear in an LLM
  payload. Test the relevant behavior or structured contract instead.
- If no Dafny source file changes, exclude `tests/bench` from routine regression
  testing. This does not excuse skipping checks affected by changes to generated
  specifications, verifier invocation, toolchains, or evaluation code. Use focused
  checks, or obtain approval for a necessary benchmark run.
- When removing a feature, update or remove its existing tests as appropriate.
  Do not add a new test whose sole purpose is to prove that the feature is absent.

## Dafny and proofs

- Read `DAFNYSTYLE.md` before modifying Dafny code. If it is unavailable, report
  the blocker instead of inventing its contents.
- On a verification timeout, first identify the expensive proof obligation. Guide
  the verifier with local `assert ... by { ... }` blocks, existing lemmas, or small
  reusable lemmas before changing the time limit.
- Increase a verification time limit only after proof guidance is insufficient or
  the remaining cost is inherent. Record the obligation, attempts, evidence, and
  justification.
- Do not hide instability by widening verification ranges, changing scope to mask
  the failure, or skipping the timed-out obligation. Preserve proof coverage and
  report exactly what was and was not verified.

## Experiments

- Run experiments in `tmux`. Record the session name, command, configuration,
  relevant versions, logs, exit status, and result artifacts. If `tmux` is
  unavailable, report the blocker rather than silently changing execution mode.
- For experiments requiring the OpenAI API, use an approved network-capable
  environment. If sandbox restrictions prevent access, request the approved
  outside-sandbox execution path. Never bypass permissions or disable safeguards.
- Never put credentials or sensitive API payloads in documentation or logs.
  Do not fabricate API results when credentials or permissions are unavailable.

## Commits

- Create commits only when requested. Keep each commit small, cohesive, and focused
  on one logical change.
- Use `[Subject] <verb-first description>`.
- `Subject` must be one short word without spaces, begin with an uppercase letter,
  and name the changed area. The description must begin with a lowercase verb.
- Example: `[Proof] simplify the sequence preservation lemma`.
- Write the entire commit message in English. Include a detailed body after the
  subject that explains the problem, approach, affected specification,
  implementation, proof, evaluation, or benchmark boundaries, validation
  commands and results, and known limitations or follow-up work.
- Include an accurate `Co-authored-by: Full Name <email>` trailer for every
  co-author who materially contributed including Codex.

## Explanations

- Present the key result first, then concrete supporting evidence and limitations.
- In Korean explanations, write the Korean term first and the English term in
  parentheses when needed. Do not casually mix untranslated English into Korean.
- Preserve exact code identifiers, paths, commands, and externally defined names.
  Follow the existing language of source code and repository documentation.
