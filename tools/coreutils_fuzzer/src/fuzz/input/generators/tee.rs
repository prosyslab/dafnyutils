use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::line_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b"line\n"),
        1 => support::case(vec!["out"], fixture, b"line\n"),
        2 => support::case(vec!["-a", "target.txt"], fixture, b"line 2\n"),
        3 => support::case(vec!["one", "two", "three"], fixture, b"payload\n"),
        4 => support::case(vec!["dir/out"], fixture, b"nested\n"),
        _ => return None,
    })
}
