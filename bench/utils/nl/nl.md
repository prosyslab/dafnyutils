# nl NL Specification

Source:
- `coreutils/doc/coreutils.texi`
- `@node nl invocation`
- Source line range: 1859-2002

## `nl`: Number lines and write files

`nl` writes each file (`-` means standard input), or standard input if none
are given, to standard output with line numbers added to some or all lines.

Synopsis:

```text
nl [option]... [file]...
```

GNU `nl` treats all input files as a single document; it does not reset line
numbers between file operands. If input does not end with a newline, GNU `nl`
prints the final line with a terminating newline.

### Supported Benchmark Slice

This benchmark implements line numbering for ordinary body text and rejects
logical-page delimiters until their section semantics are modeled:

- no operands: read standard input
- `-` operand: read standard input at that operand position
- file operands: read files left to right
- multiple operands: treat all inputs as one document and continue numbering
  across operand boundaries
- `-b STYLE` / `--body-numbering=STYLE`: support `a` for all lines, `t` for
  nonempty lines, and `n` for no lines
- `-n FORMAT` / `--number-format=FORMAT`: support `ln`, `rn`, and `rz`
- `-s STRING` / `--number-separator=STRING`: use `STRING` after a rendered
  number; the default separator is TAB
- line numbers start at 1, increment by 1, and render in width 6
- unnumbered lines still receive the blank prefix width used by GNU `nl`
- missing file operands and other read failures: write a GNU-style diagnostic,
  continue processing later operands, and exit with status 1
- default logical page delimiter lines (`\:\:\:`, `\:\:`, and `\:`): reject
  with a benchmark diagnostic and suppress rendered stdout until logical-page
  semantics are modeled
- `--help` and `--version`: print requested metadata and exit with status 0

### Deferred GNU Behavior

The following GNU `nl` behavior is documented but intentionally outside this
small benchmark slice:

- logical page sections, including replacing delimiters with empty output lines
- `-d CD` / `--section-delimiter=CD`
- `-f STYLE` / `--footer-numbering=STYLE`
- `-h STYLE` / `--header-numbering=STYLE`
- `-i NUMBER` / `--line-increment=NUMBER`
- `-l NUMBER` / `--join-blank-lines=NUMBER`
- `-p` / `--no-renumber`
- `-v NUMBER` / `--starting-line-number=NUMBER`
- `-w NUMBER` / `--number-width=NUMBER`
- `-b pBRE`, `-f pBRE`, and `-h pBRE` regular-expression numbering styles
- locale-sensitive regular expression and diagnostic behavior

These features require parser coverage and semantic models for logical pages,
numeric option parsing, and regular expressions that are not present in the
current `World`-compatible benchmark slice.

### Exit Status

The supported slice exits with status 0 on successful output, help, and version
requests. It exits with status 1 for invalid supported option values or if any
file operand cannot be read.

Example:

```text
# Number nonempty lines from standard input using the default format.
nl

# Number every input line with zero-padded numbers and a custom separator.
nl -b a -n rz -s ': ' file
```
