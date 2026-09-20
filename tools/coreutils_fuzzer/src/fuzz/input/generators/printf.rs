use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => support::case(vec!["hello"], fixture, b""),
        1 => support::case(vec![r"line\nnext\tindent\\slash"], fixture, b""),
        2 => support::case(vec![r"%s:%s\n", "left", "right"], fixture, b""),
        3 => support::case(vec![r"%s,", "a", "b", "c"], fixture, b""),
        4 => support::case(vec![], fixture, b""),
        _ => return None,
    })
}
