use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => support::case(vec!["3"], fixture, b""),
        1 => support::case(vec!["1", "2", "5"], fixture, b""),
        2 => support::case(vec!["-s,", "1", "3"], fixture, b""),
        3 => support::case(vec!["-w", "8", "10"], fixture, b""),
        4 => support::case(vec!["a"], fixture, b""),
        _ => return None,
    })
}
