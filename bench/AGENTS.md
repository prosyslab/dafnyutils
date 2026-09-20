# Bench Verification Rules

## Final Specification Obligation

- In each utility entry point `<Utility>.dfy`, `RunCore` must have the specification entry point `Spec(...)` as its postcondition.
- The final proof obligation is `RunCore ==> Spec(...)`. A `CoreSummary ==> Spec(...)` lemma may support this proof, but does not replace it.

## IO Frames

- Declare every IO field that `RunCore` may change in its `modifies` clause, using the narrowest frame that matches its effects.
- Declare every IO object or field on which a predicate depends in its `reads` clause.
- Express IO field invariance only through `modifies` and `reads` frames. Do not use `old(...)`, unchanged-field predicates, or equivalent before/after equalities to restate frame-derived invariance.

## Spec/Core Boundary

- Define fixed user-facing text, such as help messages, version messages, and error messages, only in the spec module. Core modules should import and reuse the spec definitions instead of duplicating those strings.
- Specifications must describe observable behavior mathematically and declaratively.
- Prefer `exists`, `forall`, assign-such-that (`:|`), value relations, index and partition properties, sets and multisets, arithmetic properties, inductive judgments, `IOContract.*ContractFields`, and existential intermediate states.
- Do not compute specification results algorithmically or expose an algorithm through accumulator or index recursion, prefix-processing pipelines, recursive-descent parsers, execution state machines, or helpers that mirror Core control flow.
- Fixed text, direct classifications, natural mathematical functions, and direct map lookups may remain executable general functions.
- Core owns execution algorithms; Proof connects Core behavior to the declarative specification and discharges the final `RunCore ==> Spec(...)` obligation.
- Add a shared helper only after the same relation appears in two completed conversions. Do not add an executable-function audit tool or a shared Spec DSL.
- Implementation modules may import the spec module only to state or reuse contract summaries; spec modules must not import implementation, proof, or CLI modules.
- Keep implementation-only witnesses needed for executable construction in the implementation module and bridge them to the specification in the proof module.

## Proof Minimalism

- Minimize unnecessary `assert` statements and proof blocks. Keep only proof guidance that discharges a real verifier obligation or documents a non-obvious reasoning step.
