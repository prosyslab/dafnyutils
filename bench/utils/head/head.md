# head NL Specification

Source:
- `coreutils/doc/coreutils.texi`
- `@node head invocation`
- Source line range: 2942-3009

## `head`: Output the first part of files

`head` prints the first part of each file. It reads standard input if no
files are given or when an operand is `-`.

Synopsis:

```text
head [option]... [file]...
```

If more than one input is specified, GNU `head` prints a one-line header before
the output for each input:

```text
==> file name <==
```

### Supported Benchmark Slice

This benchmark implements the deterministic line and byte selection behavior:

- no operands: read standard input
- `-` operand: read standard input at that operand position
- file operands: read and print the selected prefix of each file
- multiple operands: process operands left to right and print GNU-style headers
  before successful input output
- default selection: print the first 10 newline-delimited lines
- `-n NUM` and `--lines=NUM`: print the first decimal `NUM` lines
- `-n -NUM` and `--lines=-NUM`: print all but the last decimal `NUM` lines
- `-c NUM` and `--bytes=NUM`: print the first decimal `NUM` bytes
- `-c -NUM` and `--bytes=-NUM`: print all but the last decimal `NUM` bytes
- GNU count multiplier suffixes that select a finite prefix or finite tail
  elision: `b`, decimal `KB` through `QB`, binary `K` through `Q`, and binary
  `KiB` through `QiB`
- obsolete first-option syntax `-[NUM][bkmclqvz]...`, when it is the first
  user argument after `head`; plain `-NUM` selects lines, `c` selects bytes,
  `b`/`k`/`m` select bytes with the legacy multiplier, `l` selects lines,
  and `q`/`v`/`z` apply the corresponding quiet, verbose, and NUL-delimited
  options
- `-z` and `--zero-terminated`: in line mode, use NUL-delimited records
  instead of newline-delimited records
- `-q`, `--quiet`, and `--silent`: never print file name headers
- `-v` and `--verbose`: always print file name headers
- missing, unreadable, or directory operands: write a GNU-style diagnostic,
  continue processing later operands, and exit with status 1
- invalid decimal count arguments: write a GNU-style count diagnostic and exit
  with status 1
- `--help` and `--version`: print requested metadata and exit with status 0

Counts are parsed as decimal, including leading zeroes, before any supported
multiplier suffix is applied. Line mode treats newline as the record separator
by default, or NUL when `-z`/`--zero-terminated` is supplied. A final
non-delimited suffix counts as a record for purposes of negative line elision.

### Unsupported GNU Inventory

The following GNU behavior is documented or covered by upstream tests but is
outside this benchmark slice:

- `coreutils/tests/head/head.pl` obsolete syntax cases beyond
  `-[NUM][bkmclqvz]...`: unsupported trailing letters still produce a
  GNU-style diagnostic and are not modeled as successful selections.
- `coreutils/tests/head/head.pl` disabled overflow cases: overflow diagnostics
  for very large counts require GNU `uintmax_t` overflow behavior; this
  benchmark uses unbounded mathematical counts for deterministic finite
  stream selection instead.
- `coreutils/tests/misc/write-errors.sh` entry `head -z -n-1 /dev/zero`:
  `/dev/zero` and write-failure behavior require unbounded device input and
  write-failure effects not exposed by the current runner.
- `coreutils/tests/head/head-c.sh`: shell sequencing observes a shared stdin
  file offset across multiple commands; the current subprocess parity runner
  executes one benchmark command at a time. The same file also checks memory
  limits for huge negative byte counts and procfs/sysfs quasi-seekable files,
  which are outside the `World` model.
- `coreutils/tests/head/head-pos.sh`: requires observing the input descriptor
  position after `head` exits and includes large seekable-file positioning
  stress cases.
- `coreutils/tests/head/head-elide-tail.pl` expensive and
  `---presume-input-pipe` variants: these exercise internal buffering strategy
  and compile-time pipe assumptions rather than the benchmark's observable
  file/stdin/stdout relation.
- `coreutils/tests/head/head-write-error.sh` and
  `coreutils/tests/misc/io-errors.sh` entry for `head`: `/dev/full`, closed
  pipes, and injected EIO behavior require write-failure and fault-injection
  effects not exposed by the current runner.
- Exact generated help/version text is not used as a parity oracle; the
  benchmark checks that the requested metadata path succeeds and emits output.

### Exit Status

The supported slice exits with status 0 on successful output, help, and version
requests. It exits with status 1 for invalid counts or if any file operand
cannot be read.

Examples:

```text
# Print the first 10 lines of a file.
head file

# Print all but the last two bytes from standard input.
head -c -2
```
