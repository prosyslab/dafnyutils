use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b""),
        1 => support::case(vec!["d/f/"], fixture, b""),
        2 => support::case(vec!["a/b", "c/d"], fixture, b""),
        3 => support::case(vec!["-z", "/tmp/sample.txt", "plain"], fixture, b""),
        4 => support::case(vec!["--bogus"], fixture, b""),
        _ => return None,
    })
}
