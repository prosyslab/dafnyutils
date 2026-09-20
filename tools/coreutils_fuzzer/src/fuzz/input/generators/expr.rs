use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => support::case(vec!["1", "+", "2"], fixture, b""),
        1 => support::case(vec!["5", ">", "3"], fixture, b""),
        2 => support::case(vec!["substr", "abcdef", "2", "3"], fixture, b""),
        3 => support::case(vec![], fixture, b""),
        _ => return None,
    })
}
