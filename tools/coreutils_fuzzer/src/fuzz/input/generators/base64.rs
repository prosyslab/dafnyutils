use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::line_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b"hello\n"),
        1 => support::case(vec!["--decode"], fixture, b"aGVsbG8K"),
        2 => support::case(vec!["--decode", "--ignore-garbage"], fixture, b"Y W!F\tu\n"),
        3 => support::case(vec!["--wrap=4"], fixture, b"abcdefghi"),
        4 => support::case(vec!["--wrap=0"], fixture, b"abcdefghi"),
        5 => support::case(vec!["payload.bin"], fixture, b""),
        6 => support::case(vec!["--decode"], fixture, b"a"),
        7 => support::case(vec!["--wrap=bad", "--help"], fixture, b""),
        8 => support::case(vec!["one", "two"], fixture, b""),
        _ => return None,
    })
}
