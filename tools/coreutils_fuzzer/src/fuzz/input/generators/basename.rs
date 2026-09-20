use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b""),
        1 => support::case(vec!["/tmp/sample.txt"], fixture, b""),
        2 => support::case(vec!["/tmp/sample.txt", ".txt"], fixture, b""),
        3 => support::case(
            vec!["-a", "-s", ".txt", "-z", "dir/file.txt", "other.txt"],
            fixture,
            b"",
        ),
        4 => support::case(vec!["--suffix"], fixture, b""),
        5 => support::case(vec!["a", "b", "c"], fixture, b""),
        _ => return None,
    })
}
