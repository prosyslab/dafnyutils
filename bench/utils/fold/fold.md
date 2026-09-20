# fold

`fold` wraps long input lines from standard input or named files and writes the
transformed byte stream to standard output.

Supported behavior in this benchmark slice:

- With no file operand, or with `-`, read standard input.
- With file operands, read each file in order, report unreadable files on
  standard error, and continue with later operands.
- By default, wrap lines after 80 display columns in the LC_ALL=C model:
  NUL is zero-width, backspace moves one column left, carriage return resets to
  column zero, and tab advances to the next 8-column stop.
- `-w WIDTH` and `--width=WIDTH` use a positive decimal width instead of 80.
- `-b` and `--bytes` count bytes rather than columns.
- `-s` and `--spaces` wrap at the last blank byte that fits before the
  selected byte or column width boundary when one exists.
- Existing newline bytes are preserved and reset the current column.
- The vendored GNU `fold` scanner treats byte `0xff` as end-of-input; this
  benchmark mirrors that behavior for parity.

Deferred GNU behavior:

- Locale-sensitive multibyte display widths are not modeled. The implementation
  and formal relation intentionally use LC_ALL=C columns.
- Zero-width combining characters are not modeled separately from their bytes.
