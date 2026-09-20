use super::super::fixtures;
use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice};
use super::super::PatternInputGenerator;
use crate::fuzz::GeneratedCase;
use std::path::PathBuf;

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    Element::repeated(
        0,
        2,
        Atom::Option(OptionChoice::available(&[
            "-A",
            "--show-all",
            "-b",
            "--number-nonblank",
            "-E",
            "--show-ends",
            "-n",
            "--number",
            "-s",
            "--squeeze-blank",
            "-T",
            "--show-tabs",
            "-v",
            "--show-nonprinting",
        ])),
    ),
    Element::repeated(
        0,
        3,
        Atom::Operand(OperandSource::Stream {
            existing_weight: 3,
            missing_weight: 1,
            stdin_weight: 1,
            allow_repeated_stdin: true,
        }),
    ),
])]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => GeneratedCase {
            argv: Vec::new(),
            fixture,
            stdin: b"stdin line\n".to_vec(),
            cwd: PathBuf::from("."),
        },
        1 => GeneratedCase {
            argv: vec!["a.txt".to_string(), "b.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        2 => GeneratedCase {
            argv: vec!["-".to_string(), "a.txt".to_string()],
            fixture,
            stdin: b"prefix\n".to_vec(),
            cwd: PathBuf::from("."),
        },
        3 => GeneratedCase {
            argv: vec!["a.txt".to_string(), "missing.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        _ => return None,
    })
}
