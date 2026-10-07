# sort

## Scope for maintainer review

- Reference: GNU coreutils `src/sort.c` at `2cf491412c199e2211880ec3f4ba387026638a33`;
  `doc/coreutils.texi`, `@node sort invocation`. License: GPL-3.0-or-later.
- Model/API revision: `bench/core` at `a98d11a`.
- AllowedInput:
  - `-r`, `-u`, `-s`, `-c`, `-C`, `-z`, their long spellings (`--reverse`,
    `--unique`, `--stable`, `--zero-terminated`,
    `--check[=diagnose-first|quiet|silent]`), grouped short options and `--`.
  - `--help` and `--version`.
  - Zero or more file operands; no operand or `-` reads standard input.
  - Records are arbitrary bytes ended by newline, or NUL with `-z`. A final
    record without a delimiter is output with one.
  - Check mode (`-c`, `-C`) takes exactly one regular file operand.
- EnvironmentProfile: Linux, C locale, `TZ=UTC0`, fixed non-root user; regular
  files, directories, missing and unreadable paths in the test tree. Standard
  output write failures are out of scope.
- Observation: stdout and stderr bytes, exit status (0 success, 1 disorder in
  check mode, 2 failure) and standard input consumption.
- TrustedOperations: `bench/core/IO.dfy` read, write, errno-text and quoting
  operations. Record splitting, ordering, duplicate removal, disorder
  detection, diagnostics and exit status are implemented and proved.

### Options left out due to IO.dfy

| Option | Missing API support |
| --- | --- |
| `-c` / `-C` on standard input | GNU stops reading at the first disorder; `IO.dfy` reads standard input only as a whole. |

Other GNU options, such as keys, other orderings, `-m` and `-o`, are outside
this scope.

### Errors

- A file operand that is a directory fails with `read failed`; any other
  unreadable operand fails with `cannot read` (`open failed` in check mode).
- `cannot read` is checked for every operand before any input is read, so it
  takes precedence over `read failed`. Standard input is read only if no
  operand fails with `cannot read` and `-` comes before the first operand that
  fails with `read failed`.
- A failed read produces no stdout.

### Examples

Files: `unsorted` = `b\na\nc\na\n`, `sorted` = `a\nb\nc\n`,
`dupsorted` = `a\na\nb\n`, `nonl` = `b\na`, `zrecs` = `b\0a\0c`; `dir` is a
directory and `nofile` does not exist.

| Command | stdout | stderr | exit |
| --- | --- | --- | --- |
| `sort unsorted` | `a\na\nb\nc\n` | | 0 |
| `sort nonl` | `a\nb\n` | | 0 |
| `sort -r unsorted` | `c\nb\na\na\n` | | 0 |
| `sort -u unsorted` | `a\nb\nc\n` | | 0 |
| `sort -z zrecs` | `a\0b\0c\0` | | 0 |
| `sort dir nofile` | | `sort: cannot read: nofile: No such file or directory` | 2 |
| `sort dir` | | `sort: read failed: dir: Is a directory` | 2 |
| `sort -c unsorted` | | `sort: unsorted:2: disorder: a` | 1 |
| `sort -c -u dupsorted` | | `sort: dupsorted:2: disorder: a` | 1 |
| `sort -c -z zrecs` | | `sort: zrecs:2: disorder: a\0` | 1 |
| `sort -C unsorted` | | | 1 |
| `sort -c nofile` | | `sort: open failed: nofile: No such file or directory` | 2 |
| `sort -c sorted unsorted` | | `sort: extra operand 'unsorted' not allowed with -c` | 2 |
| `sort -c -C sorted` | | `sort: options '-cC' are incompatible` | 2 |

## Specification and proof

- SpecificationEntry: `SortSpec.Spec`. The output records are a permutation of
  the input records, ordered by bytes (reversed by `-r`). With `-u`, they are
  the set of input records in strict order. `-s` has no observable effect,
  because equal records are identical.
- Check mode: the input is sorted if every adjacent pair is ordered (strictly
  with `-u`); otherwise `-c` reports the first out-of-order record and `-C`
  prints nothing.
- Frame: standard input, stdout and stderr only.
- TerminationPolicy: finite input; `RunCore` terminates.
- CLI boundary: invalid options, incompatible options and extra operands exit
  early; `RunCore` directly ensures `Spec(...)`.
- Normal, boundary, and error behavior: rejected outputs include `a\nb\nc\n`
  for `sort unsorted`, `a\nb` for `sort nonl`, and any stdout for
  `sort sorted nofile`.

## Contribution and review evidence

Recorded in the pull request.
