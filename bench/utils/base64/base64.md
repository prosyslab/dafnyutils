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

File-read error receipts retain the bytes returned before failure. A close
failure after encoding preserves the encoded output and reports the operand;
a read failure uses the GNU read-error diagnostic. Output failures retain the
committed prefix and produce a nonzero status.

On a decoding read error, only completed 4096-byte input buffers contribute
output. Garbage filtering precedes the buffer-full decision when requested;
quartets can span buffers, and a failed read does not flush an unfinished
quartet as EOF. A close error follows ordinary EOF decoding. Invalid input in
an already completed buffer takes precedence over a later read or close error,
and valid decoded bytes preceding an invalid character are retained. Broader
stream-ordering and finalization limits are recorded in
[the API model limits](../../../docs/core-api.md#trust-limits-and-api-changes).
