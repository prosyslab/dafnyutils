use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice};
use super::super::{fixtures, mutation, support, PatternInputGenerator};
use crate::fuzz::GeneratedCase;

const SUMMARY: Element = Element::optional(35, Atom::Option(OptionChoice::available(&["-s"])));
const FILES: Element = Element::repeated(1, 3, Atom::Operand(OperandSource::ExistingFileUnique));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::requiring(
        1,
        &["--bytes"],
        &[Element::once(Atom::Literal("--bytes")), SUMMARY, FILES],
    ),
    Alternative::requiring(
        1,
        &["--apparent-size", "--block-size"],
        &[
            Element::once(Atom::Literal("--apparent-size")),
            Element::once(Atom::Literal("--block-size=1")),
            SUMMARY,
            FILES,
        ],
    ),
    Alternative::requiring(
        1,
        &["-b"],
        &[Element::once(Atom::Literal("-b")), SUMMARY, FILES],
    ),
    Alternative::weighted(2, &[Element::once(Atom::Literal("-b")), SUMMARY, FILES]),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutation::regenerate_argv);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::line_fixture();
    Some(match iteration {
        0 => support::case(vec!["-b", "a.txt"], fixture, b""),
        1 => support::case(vec!["--bytes", "empty.txt", "payload.bin"], fixture, b""),
        2 => support::case(
            vec!["--apparent-size", "--block-size=1", "payload.bin"],
            fixture,
            b"",
        ),
        3 => support::case(vec!["-b", "-s", "a.txt"], fixture, b""),
        4 => support::case(vec!["-b", "missing.txt"], fixture, b""),
        _ => return None,
    })
}
