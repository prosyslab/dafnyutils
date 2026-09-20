# tee

`tee` copies standard input to standard output and to each named output file.
This benchmark slice supports:

- `-a` and `--append`, appending to existing regular files and creating missing outputs.
- `-i` and `--ignore-interrupts` as parsed no-op options.
- `--help` and `--version`.
- Any number of regular output path operands representable by `BenchWorld`.

Deferred GNU behavior:

- Signal handling for `-i` is outside the current `World` model.
- Pipe-error policy, `--output-error`, and special host devices such as `/dev/full`
  require unmodeled descriptor/device effects.
- Host write failures after a modeled path is accepted are not represented by
  `WriteFileContract`; modeled diagnostics cover path and node-kind failures.
