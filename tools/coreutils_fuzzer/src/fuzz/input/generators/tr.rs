use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => support::case(vec!["a-a", "z"], fixture, b"abc"),
        1 => support::case(vec!["-d", "a-z"], fixture, b"abc $code"),
        2 => support::case(vec!["-s", "a-z"], fixture, b"aabbcc"),
        3 => support::case(vec!["-d", "-s", "a", "b"], fixture, b"aabbbcc"),
        4 => support::case(vec![], fixture, b""),
        _ => return None,
    })
}
