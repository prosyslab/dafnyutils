# {{TASK_ID}}

## Scope prepared by maintainers

- Reference: TODO pinned upstream revision, behavior source, and license.
- Model/API revision: TODO reviewed minimum syscall interface and model checks.
- AllowedInput: TODO options, combinations, byte/text/path domain, and invalid-input behavior.
- EnvironmentProfile: TODO locale, credentials/groups, umask, time, filesystem kinds, and supported errors.
- Observation: TODO exit statuses, stream bytes, input consumption, contents, metadata, aliases, and partial effects.
- TrustedOperations: TODO supplied primitive operations and the algorithms the contributor must implement and prove.

## Specification and proof

- SpecificationEntry: TODO principal `*.Spec` and its natural-language behavior mapping.
- Frame: TODO changed regions and constraints within those regions.
- TerminationPolicy: TODO finite-input termination, correctness on return, or explicit streaming progress.
- CLI boundary: TODO parsing, early exits, and the direct `RunCore ==> Spec(...)` obligation.
- Normal, boundary, and error behavior: TODO declarative requirements without mirroring Core algorithms.

## Contribution and review evidence

TODO record commands, versions, scenario coverage, seeds/budgets, proof scope,
positive conformance, and negative specification-adequacy checks in the pull
request. Keep evaluator-only regression inputs and reference answers outside the
public description/profile. Report model gaps to maintainers. The final
specification-quality decision belongs to a human maintainer.
