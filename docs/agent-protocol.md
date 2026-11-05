# Benchmark agent protocol v1

Use this contract when integrating an agent with the
[`cosyn-experiment` evaluator](https://github.com/prosyslab/cosyn-experiment).
`AgentProtocolVersion.V1` identifies this contract. The JSON payload versions are
`benchmark.agent-task.v2` and `benchmark.agent-result.v7`. Any incompatible wire
change must bump the corresponding version and update conformance tests in the
integration repository and harness.

## Task delivery

`evaluation.agent.protocol.AgentTaskPayload` contains the validated public task
profile plus `submission`, the task roots and archive exclusions from the public
release manifest. The released `tasks/<task-id>/task.json` is a fixed file; agent
delivery writes a separate payload and a public `task.md` guide to
`/workspace/task`, and copies only manifest-declared public resources beneath it.
Each copy is read without following links and checked against the manifest hash.
Delivery never rewrites the release. The `submission` field tells the receiver
which workspace roots to collect. Agents do not package an archive.

## Trusted-host Dafny proof reuse

A public check may include the optional `proof_reuse` object with protocol
`benchmark.dafny-proof-reuse.v1`. Its `proof_roots` identify the
workspace-relative source paths passed as native Dafny roots,
`verification_options` is the ordered native policy, and `describe_argv` and
`compile_argv` are explicit command vectors. Proof reuse is optional. Unknown protocol versions,
absolute or traversing roots, empty options, and empty command vectors are
invalid task payloads.

The describe command writes exactly one JSON object to standard output. It repeats
the protocol, proof roots and verification options, adds a lowercase SHA-256
`source_identity`, and lists every final native target as an exact
`source_path`/`symbol` pair. The descriptor uses the same native target and
ambiguity checks as full verification. The identity binds the manifest,
project configuration, candidate Dafny sources, and analyzed immutable support
dependencies. Empty scopes, duplicate or ambiguous targets, forbidden bodyless
declarations, and source changes fail closed without a partial descriptor.

This capability authorizes only a trusted runtime host to reuse conclusive native
proof results whose source, target and complete ordered option identities match
the final descriptor. The trusted Cosyn runtime selects the native proof producer;
this authorization does not claim that its producer is equivalent to the
benchmark owner's independent verifier. The host retains its own native proof
provenance and repeats the source and scope checks after compilation. A target
may have zero obligations, but
the complete reused scope must still contain at least one conclusive obligation,
matching the full verifier's nonvacuous-success rule. Candidate output and
candidate-created receipts never establish proof success.

After complete proof coverage, the host may run `compile_argv`. The owner validates
the same source identity before and after one explicitly no-verify build and does
not call proof verification in this mode. Compilation has its own
`DAFNY_COMPILE_OUTCOME` records and cannot be interpreted as proof evidence. The
ordinary public check and independent benchmark evaluator build and natively
verify the complete target scope rather than trusting reused
agent results.

## Results and workspace

`evaluation.agent.protocol.AgentReport` is the `benchmark.agent-result.v7` JSON
contract. It records run, comparison, task, agent and backend identity labels;
status, exit code, timing and observed turn/token usage; public resource/rule/check
consumption; and optional artifacts. Identity labels are opaque strings to the
benchmark. Agents report workspace outputs rather than submission archives.
Turn usage records only `used_turns`, without a turn allowance. Cosyn defines the separate invocation
wire and validates invocation-specific consistency.

The default `CandidateLayout` mounts a public workspace at `/workspace`, the
agent task at `/workspace/task` read-only and model scratch at
`/workspace/.agent` writable. Temporary and tool cache paths used by model-side
commands live under that scratch directory. The launcher is `/workspace/agent`; the agent runs from
`/workspace` using `./agent exec --prompt=<prompt>`. Candidate editable paths
are writable bind mounts. Public task and fixed inputs are read-only mounts.
The private run directory, artifact directory, runtime bundle, home and temporary
directory remain outside the model's permitted file view, while the harness may
execute tools from them. The evaluator's oracle executable is blocked by the candidate
mount plan.

The benchmark lifecycle owns the sequence from preparation through execution,
confirmed container termination and host collection. A preparation failure,
timeout, nonzero exit, invalid report or unconfirmed termination prevents
collection. Diagnostic retention never retains running candidate containers.
After normal agent exit and confirmed container termination, the host packages
the declared roots without following links, rejects hard links and special
entries, and applies the manifest's exclusions. Submission acceptance checks
archive limits, released fixed-file hashes and
required outputs before evaluator checks. A missing required output therefore
causes a receiver error, `required outputs missing`, even if the agent report
said `completed`.

For host integrations, use `evaluation.agent.runtime.run_candidate_lifecycle`.
It coordinates preparation, execution, shutdown and host collection, returns
structured failure status, and attempts cleanup after execution exceptions.
Unexpected execution exceptions propagate without collecting an archive. See the
[runtime API](https://github.com/prosyslab/cosyn-experiment/blob/main/src/evaluation/agent/runtime.py)
for callback types and integration parameters.
