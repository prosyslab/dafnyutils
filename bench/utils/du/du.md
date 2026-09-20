# du

Benchmark slice for `du`, focused on apparent-size byte counts for named
regular files.

Supported behavior:

- `-b` / `--bytes`, equivalent to apparent size with block size 1.
- `--apparent-size --block-size=1`.
- `-s` / `--summarize` is accepted for regular-file operands; it has the same
  observable output for this slice.
- Multiple named regular-file operands are processed in argv order.
- Each successful file prints `<byte-count>\t<path>\n`.
- Missing or unreadable operands report `du: cannot access '<path>': <error>`.
- `--help`, `--version`, and GNU-style unknown-option diagnostics.

Deferred GNU behavior:

- Default block usage without `-b` is rejected with an explicit benchmark
  diagnostic because the current slice does not model allocated block counts.
- Recursive directory traversal, hard-link deduplication, inode mode,
  dereference policy, mount/device boundaries, excludes, thresholds, totals,
  timestamps, max-depth, and sparse-file/device behavior are outside the current
  `World` metadata model.
- `--files0-from` and NUL-delimited operand streams are not implemented.
