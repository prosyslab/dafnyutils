"""Test that regenerating a utility description keeps its hand-written scope section."""

from __future__ import annotations

from benchmarks.extract_nl_specs import (
    SCOPE_HEADING,
    convert_texinfo_to_markdown,
    keep_scope_section,
)

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


# An operand item such as dd's `if=FILE` keeps its name and parameter in the description.
def test_operand_item_keeps_name_and_parameter() -> None:
    lines = ["@optItem{dd,conv,=@var{conversion}[@comma{}@var{conversion}]@dots{}}"]

    assert convert_texinfo_to_markdown(lines) == ["- `conv=conversion[,conversion]...`"]


# Sentence-ending `@.` and its sibling markup disappear from the converted prose.
def test_sentence_end_marker_is_removed() -> None:
    assert convert_texinfo_to_markdown(["table specified by POSIX@."]) == [
        "table specified by POSIX."
    ]


# Markup inside the sub-list argument of the --files0-from macro is converted.
def test_files_zero_from_macro_converts_its_sub_list_argument() -> None:
    lines = ["@filesZeroFromOption{du,, with the @option{--total} (@option{-c}) option}"]

    expected = "with the `--total` (`-c`) option for each sublist rather than for the entire list."

    assert expected in convert_texinfo_to_markdown(lines)
