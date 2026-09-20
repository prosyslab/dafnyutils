use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

pub(crate) static GENERATOR: PatternInputGenerator = PatternInputGenerator::generic(scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::line_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"),
        1 => support::case(vec!["-b", "-w", "4", "a.txt"], fixture, b""),
        2 => support::case(vec!["-s", "-w", "8"], fixture, b"aa bb ccdd\n"),
        3 => support::case(vec!["--width", "-b"], fixture, b""),
        4 => support::case(vec!["a.txt", "missing.txt", "b.txt"], fixture, b""),
        _ => return None,
    })
}
