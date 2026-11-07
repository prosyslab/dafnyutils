"""Test that regenerating a utility description keeps its hand-written scope section."""

from __future__ import annotations

from benchmarks.extract_nl_specs import SCOPE_HEADING, keep_scope_section

GENERATED = "# comm NL Specification\n\n## `comm`: Compare sorted files\n\nNew manual text.\n"
SCOPE = f"\n{SCOPE_HEADING}\n\n- `--check-order`: not implemented.\n"


# A description written by hand below the generated text survives regeneration unchanged.
def test_regeneration_keeps_the_scope_section() -> None:
    existing = "# comm NL Specification\n\nOld manual text.\n" + SCOPE

    assert keep_scope_section(GENERATED, existing) == GENERATED + SCOPE


# A description without a scope section is replaced by the newly generated text.
def test_regeneration_without_a_scope_section_uses_the_generated_text() -> None:
    existing = "# comm NL Specification\n\nOld manual text.\n"

    assert keep_scope_section(GENERATED, existing) == GENERATED


# A utility whose description does not exist yet gets exactly the generated text.
def test_first_generation_uses_the_generated_text() -> None:
    assert keep_scope_section(GENERATED, None) == GENERATED
