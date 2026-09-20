# base64

This benchmark slice models GNU `base64` as a single-input byte transformer.
It supports stdin, `-`, or one named input file; encoding by default; decoding
with `-d`/`--decode`; `-i`/`--ignore-garbage` while decoding; and
`-w`/`--wrap`.

Encoding uses RFC 4648 base64. The default wrap width is 76 columns, and
`-w 0` disables wrapping. Decoding accepts embedded newlines, unpadded final
groups in the GNU-compatible cases covered by the parity tests, and skips
non-alphabet bytes when `--ignore-garbage` is set.

Deferred GNU behavior: the broader `basenc` alphabet family, streaming memory
stress behavior for very large inputs, and exact partial-output diagnostics for
every malformed decode edge case are intentionally left outside this benchmark
slice.
