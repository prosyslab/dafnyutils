# chmod benchmark

This benchmark specifies GNU `chmod` over the repository's normalized `World`
model. The public declarative relation covers numeric and symbolic modes,
ordered multi-operand continuation, reference-mode capture before mutation,
`-c`/`-v`/`-f` diagnostics, recursive traversal with `-H`/`-L`/`-P`,
`--preserve-root`, ancestry cycles, directory-handle restoration, and exact
filesystem, stdout, stderr, and exit results.

The Dafny structure keeps the mathematical `Spec`, executable `Core`, and
refinement `Proof` independent. Recursive behavior is stated with valid plans
and visit schedules even where directly computing the relation would be
impractical; runtime implementations refine that relation through the proof
modules.

Specification fuzzing, executable certificates, and parser witnesses are not
part of the correctness argument. Correctness is established by Dafny
verification and direct regressions; compiled implementation fuzzing against
the pinned GNU oracle remains a separate validation layer.
