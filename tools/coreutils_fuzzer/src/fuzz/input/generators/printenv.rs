use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => support::case(vec!["LC_ALL", "LANG"], fixture, b""),
        1 => support::case(vec!["LC_ALL", "MISSING", "LANG"], fixture, b""),
        2 => support::case(vec!["--null", "LC_ALL", "LANG"], fixture, b""),
        3 => support::case(vec!["-0", "LC_ALL", "LANG"], fixture, b""),
        4 => support::case(vec!["--", "-DASH"], fixture, b""),
        _ => return None,
    })
}
