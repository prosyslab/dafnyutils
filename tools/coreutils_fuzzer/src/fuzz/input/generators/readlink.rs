use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice};
use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;
use std::path::PathBuf;

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    Element::repeated(
        0,
        2,
        Atom::Option(OptionChoice::available(&[
            "-n",
            "--no-newline",
            "-q",
            "--quiet",
            "-s",
            "--silent",
            "-v",
            "--verbose",
            "-z",
            "--zero",
        ])),
    ),
    Element::up_to_budget(
        1,
        Atom::Operand(OperandSource::Target {
            existing_percent: 100,
        }),
    ),
])]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => GeneratedCase {
            argv: vec!["a-link".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        1 => GeneratedCase {
            argv: vec!["-v".to_string(), "a.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        2 => GeneratedCase {
            argv: vec![
                "-n".to_string(),
                "a-link".to_string(),
                "missing.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        3 => GeneratedCase {
            argv: vec!["-z".to_string(), "a-link".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        4 => support::case(vec![], fixture, b""),
        5 => support::case(vec!["a-link", "a-link"], fixture, b""),
        6 => support::case(vec!["-q", "a.txt"], fixture, b""),
        _ => return None,
    })
}
