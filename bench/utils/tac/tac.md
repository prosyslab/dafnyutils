# tac Literal Separator Specification

Source:
- `coreutils/doc/coreutils.texi`
- `@node tac invocation`
- Source line range: 1802-1856

## `tac`: Concatenate and write files in reverse

`tac` copies each file (`-` means standard input), or standard input if
none are given, to standard output while reversing records in each input
separately. With the default options, records are lines separated by newline,
and the separator stays attached to the end of the record it follows.

Synopsis:

```text
tac [option]... [file]...
```

### Supported Benchmark Slice

This benchmark implements literal separator record modes:

- no operands: read standard input and print its records last line first
- `-` operand: read standard input at that operand position
- file operands: read each file and reverse that file independently
- multiple operands: process operands left to right, appending each operand's
  reversed output
- `-s STRING` / `--separator=STRING`: use `STRING` as a literal separator;
  an empty separator is ASCII NUL
- `-b` / `--before`: attach separators to the following record rather than
  the preceding record
- missing file operands and other open failures: write a GNU-style diagnostic of
  the form `tac: failed to open 'FILE' for reading: ERR` to stderr, continue
  processing later operands, and exit with status 1
- directory operands: write a GNU-style read-error diagnostic to stderr,
  continue processing later operands, and exit with status 1
- `--help` and `--version`: print requested metadata and exit with status 0

### Deferred GNU Behavior

The following GNU `tac` behavior is documented but intentionally outside this
small benchmark slice:

- `-r` / `--regex`: treats the separator string as a regular expression.
  Supporting this would require a regex model or a trusted parser/executor
  boundary that the current `World` model does not provide.
- Locale-sensitive, non-ASCII separators from `coreutils/tests/tac/tac-locale.sh`
  are deferred with locale modeling.
- Non-seekable input buffering to `$TMPDIR`, temporary-storage failures, procfs
  and sysfs quasi-seekable files, and closed-stdin behavior are not represented
  in the current benchmark `World` or subprocess runner.

On systems like MS-DOS that distinguish text and binary files, GNU `tac` reads
and writes in binary mode. The benchmark subprocess tests run with deterministic
Unix-like byte streams.

### Exit Status

The supported slice exits with status 0 on successful reversal, help, and
version output. It exits with status 1 if any file operand cannot be read.

Example:

```text
# Reverse a file by literal `--`-delimited records.
tac -s -- file
```
