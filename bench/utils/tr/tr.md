# tr

This benchmark slice models `tr` as a stdin-only byte transformer. It supports:

- `tr SET1 SET2` translation
- `tr -d SET1` deletion
- `tr -s SET1` squeezing repeated bytes
- `tr -d -s SET1 SET2` deletion followed by squeezing bytes from `SET2`

Sets are limited to literal ASCII bytes and ordered ASCII ranges such as `a-z`.
When `SET1` is longer than `SET2` during translation, the final byte of `SET2`
is reused, matching the GNU default behavior covered by this benchmark.

Deferred GNU behavior: bracket character classes such as `[:lower:]`, equivalence
classes, repeat constructs, escapes, complement modes, truncate mode, locale
behavior, and multibyte characters are intentionally rejected with visible
benchmark diagnostics until they are modeled explicitly in the formal spec.
