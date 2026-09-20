use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource};
use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[Element::repeated(
    0,
    3,
    Atom::Operand(OperandSource::Stream {
        existing_weight: 4,
        missing_weight: 1,
        stdin_weight: 1,
        allow_repeated_stdin: true,
    }),
)])]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::line_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b"a\nb\nc\n"),
        1 => support::case(vec!["a.txt"], fixture, b""),
        2 => support::case(vec!["a.txt", "b.txt"], fixture, b""),
        3 => support::case(vec!["a.txt", "-"], fixture, b"stdin\n"),
        4 => support::case(vec!["missing.txt", "a.txt"], fixture, b""),
        5 => support::case(vec!["-b", "-s", "--"], fixture, b"a---b"),
        _ => return None,
    })
}
