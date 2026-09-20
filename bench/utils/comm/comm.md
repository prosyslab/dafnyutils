# comm NL Specification

Source:
- `coreutils/doc/coreutils.texi`
- `@node comm invocation`
- Source line range: 5381-5521

## `comm`: Compare Two Sorted Files Line By Line

`comm` compares two sorted input files and writes lines that are unique to each
file or common to both files.

Synopsis:

```text
comm [option]... file1 file2
```

With no options, GNU `comm` produces three output columns:

- column 1: lines unique to `file1`
- column 2: lines unique to `file2`
- column 3: lines common to both files

Columns are separated by a single TAB by default. GNU requires input sorted in
the active `LC_COLLATE` collation order. In this benchmark slice, tests run in
the deterministic C locale and the formal model compares newline-delimited byte
lines directly.

### Supported Benchmark Slice

This benchmark implements the sorted byte-record subset:

- exactly two operands are accepted for normal comparison
- at most one operand may be `-`; a single `-` reads standard input
- repeated stdin operands (`comm - -`) are rejected with a benchmark diagnostic
  rather than modeling GNU's second descriptor read failure
- both files must be sorted in the benchmark's byte-line order; unsorted input
  is rejected with a benchmark diagnostic
- by default each input is split into newline-delimited records; a final
  unterminated record is treated as a record and printed with an output newline
- `-z` / `--zero-terminated`: split input on NUL bytes and terminate output
  records with NUL
- default output has three TAB-positioned columns
- `--output-delimiter=STR`: position later columns with `STR`; an empty `STR`
  follows GNU behavior and uses NUL as the output delimiter
- specifying the same output delimiter more than once is accepted; conflicting
  delimiter values fail with `comm: multiple output delimiters specified`
- `--total`: append a summary row with counts for column 1, column 2, and
  column 3, followed by `total`
- `-1`: suppress lines unique to the first file
- `-2`: suppress lines unique to the second file
- `-3`: suppress lines common to both files
- bundled suppression options such as `-12` and `-123`
- missing operand, missing operand after one file, and extra operand diagnostics
  with exit status 1
- unreadable, missing, or directory file diagnostics with exit status 1
- `--help` and `--version` print requested metadata and exit with status 0

Successful comparisons exit with status 0. Operand-count failures, parse
failures, and file-read failures exit with status 1.

### Deferred GNU Behavior

The following documented or upstream-tested behavior remains outside this
benchmark slice:

- Repeated stdin operands (`comm - -`) are not modeled. GNU attempts to read
  standard input more than once and can emit a file-descriptor diagnostic after
  partial output. The current `World` model represents stdin as a consumable byte
  stream, not as a reusable file descriptor with host read errors.
- GNU's precise sortedness diagnostics are not implemented. Upstream coverage includes
  `coreutils/tests/misc/comm.pl` cases `ooo`, `ooo2`, `ooo3`, `ooo4`, `ooo5`,
  `ooo5b`, `ooo5c`, `ooo6`, `ooo7`, and `ooo-prefix`. This benchmark rejects
  unsorted inputs without modeling GNU's partial output and file-specific
  diagnostics. Full support requires modeling default disorder detection plus `--check-order` and
  `--nocheck-order`.
- Locale-sensitive collation and multibyte behavior are not modeled. The
  benchmark relation intentionally uses deterministic byte ordering for sorted
  newline- or NUL-delimited inputs.
- Host write failures and low-level IO faults are not modeled by this utility
  slice; output is represented through the shared benchmark `World` stdout and
  stderr transitions.
