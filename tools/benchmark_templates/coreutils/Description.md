# {{TASK_ID}}

## Scope for maintainer review

Fill this section after init, then link it from a draft PR for scope review.
Record the maintainer's decision in that PR before implementation.

- Reference: TODO pinned upstream revision, behavior source, and license.
- Model/API revision: TODO shared IO contract revision and relevant model checks.
- AllowedInput: TODO options, combinations, byte/text/path domain, and invalid-input behavior.
- EnvironmentProfile: TODO locale, credentials/groups, umask, time, filesystem kinds, and supported errors.
- Observation: TODO exit statuses, stream bytes, input consumption, contents, metadata, aliases, and partial effects.
- TrustedOperations: TODO supplied primitive operations and the algorithms the contributor must implement and prove.

## Specification and proof

- SpecificationEntry: TODO main `*.Spec` and the behavior each part describes.
- Frame: TODO changed regions and constraints within those regions.
- TerminationPolicy: TODO finite-input termination, correctness on return, or explicit streaming progress.
- CLI boundary: TODO parsing, early exits, and the direct `RunCore ==> Spec(...)` obligation.
- Normal, boundary, and error behavior: TODO declarative requirements without mirroring Core algorithms.

## Contribution and review evidence

TODO record commands, versions, test scenarios, seeds, case counts and verified
files in the pull request. Include examples of correct behavior and wrong outputs
that the specification rejects. Keep evaluator-only regression inputs and
reference answers outside this public description/profile. Report model gaps to
maintainers. A human maintainer makes the final specification-review decision.
