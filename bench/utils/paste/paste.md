# paste NL Specification

Source:
- `coreutils/doc/coreutils.texi`
- `@node paste invocation`
- Source line range: 6235-6370

## `paste`: Merge lines of files

`paste` writes lines made from the sequentially corresponding lines of each
input file. Fields are separated by a delimiter, TAB by default. A file operand
of `-`, or no operands at all, means standard input.

Synopsis:

```text
paste [option]... [file]...
```

### Supported Benchmark Slice

This benchmark covers the line-oriented GNU behavior used by the executable
parity tests:

- no operands: read standard input and write its lines unchanged
- file operands: read each file as a sequence of newline-terminated records,
  or NUL-terminated records when `-z` is present; a final unterminated suffix
  counts as a record
- `-` operands: read standard input at that operand position
- repeated `-` operands in parallel mode share one standard-input stream
  row-wise, matching GNU `paste - -`; in serial mode, the first `-` consumes
  standard input and later `-` operands see the exhausted stream
- `-z` / `--zero-terminated`: treat ASCII NUL, rather than newline, as the
  input record delimiter and output record terminator
- default parallel mode: merge corresponding records from all operands,
  replacing each non-final input record delimiter in the row with the active
  field delimiter
- `-s` / `--serial`: merge records within each input independently, one input
  after another
- `-d LIST` / `--delimiters=LIST`: cycle through LIST instead of TAB; an empty
  LIST behaves as an empty delimiter
- delimiter escapes: `\0`, `\n`, `\t`, `\\`, `\b`, `\f`, `\r`, `\v`, and GNU's
  rule that an unrecognized escaped character means that character
- delimiter lists ending in an unescaped backslash: write a GNU-style diagnostic
  and exit with status 1
- unreadable file operands: write GNU-style diagnostics and exit with status
  1 if any read failed; in parallel mode, file-open failures report the first
  failing operand and suppress merged stdout, while directory read failures
  preserve rows formed from readable operands and report each directory failure;
  in serial mode, processing continues through operands, diagnostics are
  reported for each failure, directory read failures emit an empty record, and
  successful per-file output is preserved
- `--help` and `--version`: print requested metadata and exit with status 0

### Deferred GNU Behavior

The following documented behavior is outside this benchmark slice:

- terminal text/binary-mode distinctions on non-Unix platforms
- locale-sensitive diagnostics beyond the deterministic `LC_ALL=C` parity
  environment
- detailed host filesystem effects not represented in the benchmark `World`
  model

### Exit Status

The supported slice exits with status 0 for successful output, help, and
version output. It exits with status 1 for delimiter-list syntax errors or if
any file operand cannot be read.
