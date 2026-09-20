use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b"9\t+7\n0008 1\n"),
        1 => support::case(vec!["-h", "3000"], fixture, b""),
        2 => support::case(vec!["9", "a", "7"], fixture, b""),
        3 => support::case(vec!["  +7", "0009"], fixture, b""),
        _ => return None,
    })
}
