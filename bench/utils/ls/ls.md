# ls

## Supported behavior

This benchmark implements a deterministic, verification-oriented subset of GNU
`ls` over the modeled file system.

- With no operand, it lists `.`. Regular operands are printed directly and
  directory operands are expanded.
- Output uses one entry per line. Name order uses scalar character order rather
  than locale collation.
- `-a`/`--all` includes hidden names and the implied `.` and `..` entries.
- `-A`/`--almost-all` includes hidden names but not implied `.` and `..`.
- `-d`/`--directory` lists directory operands themselves.
- `-n`/`--numeric-uid-gid` selects numeric long output containing type and
  permissions, link count, numeric owner and group, size, a UTC timestamp, and
  the displayed name.
- `--time-style` accepts `full-iso`, `long-iso`, `iso`, `locale`, `+%s`, and
  their `posix-` named variants. In the fixed C locale the `posix-` variants
  use the default C format. Other custom `+FORMAT` strings are outside this
  benchmark.
- `-s`/`--size` prefixes each entry with its allocated size. A positive integer
  `--block-size` takes precedence over `LS_BLOCK_SIZE`, `BLOCK_SIZE`, and
  `BLOCKSIZE`, in that order. The default allocated-size unit is 1024 bytes.
  Numeric-long file sizes are rounded up in the `--block-size`, `LS_BLOCK_SIZE`,
  or `BLOCK_SIZE` unit; without one of those settings they remain byte counts.
  Supported command-line and environment units are positive decimal integers.
- `-S` sorts by apparent size, `-t` sorts by the selected timestamp, and `-r`
  reverses the complete ordering. `-u` selects access time and `-c` selects
  change time; modification time is the default.
- By default, a command-line symbolic link is expanded only when its target is
  a directory; dangling and file-target links are listed as links themselves.
- `-H` follows symbolic links named as command-line operands, while `-L` follows
  symbolic links everywhere.
- A name-only `-L` directory scan keeps an implicitly encountered dangling
  symbolic link printable. GNU's `?` placeholder and minor exit status for
  metadata-required dangling entries are outside this benchmark.
- `-R` recursively lists directories. Recursion uses inode identity to detect
  cycles.
- Multiple operands and recursive directory sections use a blank line between
  sections and a `PATH:` heading where GNU `ls` would otherwise be ambiguous.
- `--help` and `--version` exit successfully without touching the file system.

The time zone is fixed to UTC and the locale is fixed to C so results do not
depend on host settings.

## Outside this benchmark

Terminal-width columns, color, quoting styles, ACL and security-context marks,
human-readable suffixes, locale collation, owner/group name lookup, indicator
suffixes, hyperlinks, tab stops, directory-ignore patterns, device major/minor
rendering, and arbitrary date-format strings are outside this benchmark.

## Exit status

The exit status is 0 when every requested listing succeeds and 2 when an
operand, directory read, followed metadata lookup, recursion cycle, block-size
argument, or a time-style argument used with `-n` fails. A time style is ignored
without long output. An invalid `--time` selector exits 1, matching GNU `ls`.
