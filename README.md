# Dafnyutils

Dafnyutils is a benchmark workspace for specifying, implementing and proving command-line utilities in Dafny, then comparing their behavior with pinned GNU coreutils.

Read [CONTRIBUTING.md](CONTRIBUTING.md) for the contribution process and required PR evidence. Use these four guides for detailed tasks:

| Your task | Guide |
| --- | --- |
| Add a utility from setup through review | [Add a utility](docs/adding-utilities.md) |
| Understand shared contracts and the trust boundary | [Use the core API](docs/core-api.md) |
| Run generated cases and reproduce mismatches | [Use the fuzzer](docs/fuzzing.md) |
| Port upstream GNU scenarios into utility Python tests | [Add test cases](docs/adding-test-cases.md) |

Use the [development container](.devcontainer/devcontainer.json) for the supported contributor environment. [TODOLIST.csv](TODOLIST.csv) records utility status and initial scope.

`bench/utils/` contains utility tasks, `bench/algorithm/` contains algorithm tasks, `bench/core/` supplies shared contracts, and `src/` contains authoring and evaluation tooling. `coreutils/` is a pinned upstream submodule. `dafny/` contains the bundled Dafny source; see [source provenance and build instructions](docs/dafny-source.md). Builds create `_build/`.

Runtime parity, Dafny verification and human specification review provide different evidence; none replaces the others. Follow [repository instructions](AGENTS.md), [bench rules](bench/AGENTS.md) and [Dafny style](DAFNYSTYLE.md).
