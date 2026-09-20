# uniq NL Specification

Source:
- `coreutils/doc/coreutils.texi`
- `@node uniq invocation`
- Source line range: 5210-5378

## `uniq`: Uniquify Files

`uniq` writes the unique lines from an input file, or from standard input if no
input is given or the input operand is `-`.

Synopsis:

```text
uniq [option]... [input [output]]
```

By default, `uniq` writes each input line except that adjacent repeated lines
are merged to the first line in the repeated group. Non-adjacent duplicate lines
are not detected. The input does not need to be sorted, but sorting is needed if
the caller wants equal lines to become adjacent before running `uniq`.

GNU `uniq` comparisons are documented as locale-sensitive through
`LC_COLLATE`. This benchmark slice runs in the deterministic C-locale subprocess
environment and models byte lines with ASCII-only case folding for
`--ignore-case`.

### Supported Benchmark Slice

This benchmark implements newline-delimited adjacent-line grouping:

- no operands: read all standard input and write the filtered result to standard
  output
- input operand `-`: read standard input
- file input operand: read that file and write the filtered result to standard
  output
- output operand `-`: write to standard output
- default mode: print the first line from every adjacent group
- `-c` / `--count`: prefix each printed group with the occurrence count in the
  GNU-compatible right-aligned count field
- `-d` / `--repeated`: print only groups that occur more than once, once per
  group
- `-u` / `--unique`: print only groups that occur exactly once
- combined `-d -u`: suppress all grouped output, matching POSIX/GNU behavior
- `-i` / `--ignore-case`: compare adjacent lines with ASCII case folding while
  preserving the original first line in output
- NUL bytes inside newline-delimited records are ordinary bytes, not record
  separators
- traditional obsolete skip-character operands such as `+1` are rejected as
  unsupported rather than treated as input file names
- missing, unreadable, or directory input operands produce GNU-style diagnostics
  and exit with status 1
- extra operands produce a GNU-style diagnostic and exit with status 1
- parse failures for unsupported options produce GNU-style option diagnostics
- `--help` and `--version` print requested metadata and exit with status 0

The supported slice exits with status 0 for successful filtering, help, and
version output. It exits with status 1 for unsupported non-`-` output operands,
extra operands, parse failures, or input read errors.

### Deferred GNU Behavior

The following GNU behavior is documented or covered by upstream tests but is
outside this benchmark slice:

- `-f N` / `--skip-fields=N`, traditional `-N`, `-s N` /
  `--skip-chars=N`, traditional `+N`, and `-w N` / `--check-chars=N` are not
  implemented. Upstream coverage includes `coreutils/tests/uniq/uniq.pl` cases
  `obs30`, `31`-`65`, `91`-`94`, `121`-`122`, and `uniq-perf.sh`. Supporting
  them requires field/character skipping, width-limited comparison, obsolete
  option syntax, overflow handling, and multibyte character counting.
- `-z` / `--zero-terminated` is not implemented. Upstream coverage includes
  `coreutils/tests/uniq/uniq.pl` cases `2z`-`20z`, `123`-`124`, and generated
  `*-z` variants. Supporting it requires NUL-delimited record parsing and NUL
  output delimiters.
- `-D` / `--all-repeated[=METHOD]` and `--group[=METHOD]` are not implemented.
  Upstream coverage includes `coreutils/tests/uniq/uniq.pl` cases `110`-`119`
  and `128`-`145`, plus option-alias coverage in
  `coreutils/tests/misc/option-aliases.sh`. Supporting them requires delimiter
  modes, all-repeated output, invalid-delimiter diagnostics, and mutual
  exclusion checks with `-c`, `-d`, and `-u`.
- Non-`-` output operands are intentionally rejected. GNU writes to the named
  output file, including truncation and output-is-input handling in the
  `triple_test` file-output variants from `coreutils/tests/uniq/uniq.pl`.
  Supporting this requires `World`/`IO` file write and truncation effects.
- Locale-sensitive collation, locale blank classification, and multibyte
  character/case behavior are not modeled. Upstream coverage includes
  `coreutils/tests/uniq/uniq-collate.sh`, the `schar` locale case in
  `coreutils/tests/uniq/uniq.pl`, and the generated `*-mb` plus `w1-mb` cases.
- Write failures and injected host IO faults are not modeled. Upstream coverage
  includes `coreutils/tests/misc/io-errors.sh` and
  `coreutils/tests/misc/write-errors.sh` entries for `uniq`, which require
  surfaces such as `/dev/full`, closed pipes, or injected EIO.

Example:

```text
uniq -c input
```
