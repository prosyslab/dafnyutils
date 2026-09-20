# cut NL Specification

Source:
- `coreutils/doc/coreutils.texi`
- `@node cut invocation`
- Source line range: 6123-6244

## `cut`: Print selected parts of lines

`cut` writes selected parts of each input line to standard output. Input comes
from each named file, from standard input when no files are given, or from
standard input for an operand of `-`.

Synopsis:

```text
cut OPTION... [FILE]...
```

The byte, character, and field lists are one or more numbers or ranges
separated by commas. Positions are numbered starting at 1. A range `N-M`
selects positions from `N` through `M`; `-M` means `1-M`; and `N-` means
`N` through the end of the line or final field. Repeated or overlapping list
elements select output only once, and output remains in input order.

The benchmark slice supports:

- `-b LIST`
- `--bytes=LIST`
Select only the listed byte positions from each line.

- `-c LIST`
- `--characters=LIST`
Select only the listed character positions. In the deterministic benchmark
environment this is modeled with the same byte-position semantics as `-b`.

- `--complement`
Select bytes or characters not listed by `-b` or `-c`.

- `-n`
Accepted for GNU compatibility. In this deterministic byte-oriented benchmark
slice it is a no-op.

- `--output-delimiter=STRING`
When selecting bytes or characters, insert `STRING` between selected range
groups. An empty `STRING` is modeled as GNU's NUL output delimiter. Overlapping
ranges are merged before delimiters are inserted; adjacent but non-overlapping
ranges remain separate groups.

- `-z`
- `--zero-terminated`
Use NUL as the input record delimiter and output record terminator instead of
newline.

- `--help`
Display help text and exit successfully.

- `--version`
Display version text and exit successfully.

If no list is provided, more than one byte/character list is provided, or a
list contains invalid positions or ranges, `cut` exits with status 1 and writes
a diagnostic to standard error.

For file operands that cannot be read, `cut` writes a diagnostic to standard
error, continues with later operands, and exits with status 1 if any operand
failed.

### Exit Status

Exit status is 0 for successful processing and for `--help` or `--version`.
Exit status is 1 for parse/list diagnostics or unreadable input operands.
