use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b""),
        1 => support::case(vec!["hello", "world"], fixture, b""),
        2 => support::case(vec!["-n", "hello"], fixture, b""),
        3 => support::case(vec!["-e", r"a\nb"], fixture, b""),
        4 => support::case(vec!["--help"], fixture, b""),
        _ => return None,
    })
}
