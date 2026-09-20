# tail

This benchmark slice models GNU `tail` for finite byte streams in the existing
World model.

Supported behavior:

- With no operand, or with operand `-`, read standard input.
- With file operands, read each named file in order.
- By default, write the last 10 newline-delimited lines of each input.
- `-n NUM` and `--lines=NUM` write the last `NUM` lines.
- `-n +NUM` and `--lines=+NUM` write from the one-based line `NUM`; `+0`
  is treated like `+1`.
- Leading obsolete line-count forms `-NUM`, `+NUM`, `-NUMl`, `+NUMl`,
  `-l`, and `+l` are accepted as finite selections when they appear in the
  GNU-compatible leading-count position.
- `-z` and `--zero-terminated` make line mode use NUL-delimited records
  instead of newline-delimited records.
- `-c NUM` and `--bytes=NUM` write the last `NUM` bytes.
- `-c +NUM` and `--bytes=+NUM` write from the one-based byte `NUM`; `+0`
  is treated like `+1`.
- Leading obsolete byte-count forms `-NUMc`, `+NUMc`, `-NUMb`, `+NUMb`,
  `-b`, `+c`, and `+b` are accepted as finite selections when they appear in
  the GNU-compatible leading-count position.  The `b` marker multiplies the
  count by 512.
- Count suffixes support GNU's deterministic finite multipliers through exa
  scale: `b`, `k`, `K`, `KiB`, `kB`, `KB`, `m`, `M`, `MiB`, `MB`, `G`, `GiB`,
  `GB`, `T`, `TiB`, `TB`, `P`, `PiB`, `PB`, `E`, `EiB`, and `EB`.
- `-q`, `--quiet`, and `--silent` suppress file headers.
- `-v` and `--verbose` always print file headers.
- `--help`, `--version`, invalid decimal counts, missing files, and directory
  read errors follow the benchmark's coreutils-style diagnostic model.

Deferred GNU behavior:

- Follow mode (`-f`, `--follow`), PID waiting, retry, and inotify behavior are
  outside the finite World input model.
- Obsolete forms with follow markers, such as `-1f`, are outside this finite
  slice.
- GNU's `Z`, `Y`, `R`, and `Q` suffix families are overflow-sensitive on the
  reference platform for nonzero counts and remain outside this finite-count
  model.
- Sparse files, special devices, procfs/sysfs, descriptor-position effects, and
  huge seek stress cases require host effects not represented by World.
