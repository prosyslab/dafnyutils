# Utility implementations and proof ideas

This guide explains how each of the 48 utilities in `bench/utils` computes its
result and why that result meets its main specification. It is for developers
who can read ordinary code but do not need to follow every Dafny lemma. The
linked source files define the exact behavior; these notes emphasize the
algorithm and the most important proof obligations.

## Read the implementation beside the contract

Each utility has three main responsibilities:

- **Implementation:** Core modules parse utility-specific values, transform
  bytes or values, perform IO, and choose diagnostics and exit status.
- **Specification:** Spec modules describe acceptable results using relations
  over inputs, output bytes and system state. They express what must hold,
  independently of the implementation's loops and intermediate variables.
- **Proof:** Proof modules connect the values and effects constructed by Core
  to those relations. Some utilities establish their final contract directly
  inside Core; others use a separate bridge lemma.

The public entry point in `<Utility>.dfy` must directly ensure `Spec(raw, io,
exit)`. A helper's `CoreSummary` is an intermediate result, not a replacement
for this final obligation. For a concrete example, read
[`Head.HeadBenchmarkItem.RunCore`](../bench/utils/head/Impl/Head.dfy), then
[`HeadCore`](../bench/utils/head/Impl/HeadCore.dfy),
[`HeadSpec`](../bench/utils/head/Spec/HeadSpec.dfy) and
[`HeadProof`](../bench/utils/head/Proof/HeadProof.dfy).
The fixed CLI parser and process runner sit outside this principal proof
boundary; see [the entry and CLI contract](core-api.md#entry-and-cli-contract).

For a loop, the main proof idea is usually to relate the processed prefix to
the accumulated result. For a recursive traversal, it is to relate child
results and intermediate states to the parent result. The entries below name
the utility-specific relation that makes that argument useful, rather than
listing all supporting assertions.

## What the proof relies on

[`BenchIO`](../bench/core/IO.dfy) exposes IO operations with contracts from
[`IOContract`](../bench/core/IOContract.dfy). Utility proofs rely on these
contracts for native results and filesystem effects; they do not prove the
operating system or GNU implementations correct. The utility still has to
prove that it calls the appropriate operations in the appropriate order and
combines their results into the specified observable behavior.

An IO contract can describe a failed read that retains some bytes or a failed
write that commits only a prefix. A filesystem operation can fail after earlier
operands have already succeeded. Consequently, correctness includes the
specified partial effects, diagnostic bytes and exit status, as well as the
successful result. `modifies` and `reads` clauses also delimit the mutable IO
regions and the state on which a predicate depends.

These notes describe the current source and its proof structure. They do not
report a new Dafny verification run or GNU comparison run. Utilities implement
the benchmark's supported slices; an omitted GNU option is not implicitly
covered. Methods declared with `decreases *` establish their postconditions on
return without establishing termination. See
[implementation notes](implementation-notes.md) for contribution examples and
[the core API guide](core-api.md) for the underlying contracts.

## Find a utility

Each linked entry has an **Implementation** section and a **Proof idea** section.

| Group | Utilities |
| --- | --- |
| [Streams and records](utility-streams.md) | [base64](utility-streams.md#base64), [cat](utility-streams.md#cat), [comm](utility-streams.md#comm), [csplit](utility-streams.md#csplit), [cut](utility-streams.md#cut), [dd](utility-streams.md#dd), [expand](utility-streams.md#expand), [fold](utility-streams.md#fold), [head](utility-streams.md#head), [join](utility-streams.md#join), [nl](utility-streams.md#nl), [paste](utility-streams.md#paste), [tail](utility-streams.md#tail), [tee](utility-streams.md#tee), [tr](utility-streams.md#tr), [tsort](utility-streams.md#tsort), [uniq](utility-streams.md#uniq), [wc](utility-streams.md#wc) |
| [Filesystem operations and observations](utility-filesystem.md) | [chmod](utility-filesystem.md#chmod), [cp](utility-filesystem.md#cp), [du](utility-filesystem.md#du), [link](utility-filesystem.md#link), [ln](utility-filesystem.md#ln), [ls](utility-filesystem.md#ls), [mkdir](utility-filesystem.md#mkdir), [mkfifo](utility-filesystem.md#mkfifo), [mv](utility-filesystem.md#mv), [rm](utility-filesystem.md#rm), [rmdir](utility-filesystem.md#rmdir), [stat](utility-filesystem.md#stat), [touch](utility-filesystem.md#touch), [truncate](utility-filesystem.md#truncate), [unlink](utility-filesystem.md#unlink) |
| [Values, paths and environment](utility-values.md) | [basename](utility-values.md#basename), [date](utility-values.md#date), [dirname](utility-values.md#dirname), [echo](utility-values.md#echo), [expr](utility-values.md#expr), [factor](utility-values.md#factor), [false](utility-values.md#false), [logname](utility-values.md#logname), [printenv](utility-values.md#printenv), [printf](utility-values.md#printf), [pwd](utility-values.md#pwd), [readlink](utility-values.md#readlink), [realpath](utility-values.md#realpath), [seq](utility-values.md#seq), [true](utility-values.md#true) |
