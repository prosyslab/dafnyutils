from __future__ import annotations

import hashlib
from pathlib import Path

import pytest

from analysis.models import (
    DafnyFingerprintRegion,
    DafnyFingerprintSpan,
)
from analysis.source_fingerprints import dafny_source_fingerprints


def _region(
    region_id: str,
    source: Path,
    *,
    included_span: tuple[int, int] | None = None,
    excluded_spans: tuple[tuple[int, int], ...] = (),
) -> DafnyFingerprintRegion:
    return DafnyFingerprintRegion(
        id=region_id,
        sourcePath=str(source),
        includedSpan=(
            DafnyFingerprintSpan(start=included_span[0], end=included_span[1])
            if included_span is not None
            else None
        ),
        excludedSpans=tuple(
            DafnyFingerprintSpan(start=start, end=end) for start, end in excluded_spans
        ),
    )


# One fingerprint batch must preserve complete UTF-8 tokens and exclude complete statements.
def test_source_fingerprint_preserves_selected_and_excluded_token_regions(tmp_path: Path) -> None:
    source = tmp_path / "Unicode.dfy"
    source.write_text(
        "method Probe() {\n  // 설명\n  var café := 1;\n}\n",
        encoding="utf-8",
    )
    source_bytes = source.read_bytes()
    token_start = source_bytes.index("café".encode())
    token_end = token_start + len("café".encode())
    whitespace_start = source_bytes.index(b"\n")
    with_extra = tmp_path / "WithExtra.dfy"
    with_extra.write_text(
        "method Probe() { assert true; assert false; }\n",
        encoding="utf-8",
    )
    expected = tmp_path / "Expected.dfy"
    expected.write_text("method Probe() { assert true; }\n", encoding="utf-8")
    extra_bytes = with_extra.read_bytes()
    excluded_start = extra_bytes.index(b"assert false")
    excluded_end = excluded_start + len(b"assert false;")

    fingerprints = dafny_source_fingerprints(
        (
            _region("identifier", source, included_span=(token_start, token_end)),
            _region(
                "whitespace",
                source,
                included_span=(whitespace_start, whitespace_start + 1),
            ),
            _region(
                "excluded",
                with_extra,
                excluded_spans=((excluded_start, excluded_end),),
            ),
            _region("expected", expected),
        ),
        cwd=tmp_path,
    )

    assert fingerprints["identifier"] != hashlib.sha256(b"").hexdigest()
    assert fingerprints["whitespace"] == hashlib.sha256(b"").hexdigest()
    assert fingerprints["excluded"] == fingerprints["expected"]


# A byte range cutting through a token must retain the existing explicit failure.
def test_source_fingerprint_rejects_split_token_region(tmp_path: Path) -> None:
    source = tmp_path / "Split.dfy"
    source.write_text("method Probe() {}\n", encoding="utf-8")
    source_bytes = source.read_bytes()
    token_start = source_bytes.index(b"Probe")

    with pytest.raises(RuntimeError, match="span splits a token"):
        dafny_source_fingerprints(
            (
                _region(
                    "split",
                    source,
                    included_span=(token_start + 1, token_start + len(b"Probe")),
                ),
            ),
            cwd=tmp_path,
        )
