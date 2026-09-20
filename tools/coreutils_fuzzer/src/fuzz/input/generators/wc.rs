use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice};
use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;
use std::path::PathBuf;

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    Element::repeated(
        0,
        3,
        Atom::Option(OptionChoice::available(&[
            "-c", "--bytes", "-l", "--lines", "-m", "--chars", "-w", "--words",
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
            stdin: b"stdin words\n".to_vec(),
            cwd: PathBuf::from("."),
        },
        1 => GeneratedCase {
            argv: vec!["a.txt".to_string(), "b.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        2 => GeneratedCase {
            argv: vec!["-lwm".to_string(), "-".to_string(), "a.txt".to_string()],
            fixture,
            stdin: b"prefix\nline\n".to_vec(),
            cwd: PathBuf::from("."),
        },
        3 => GeneratedCase {
            argv: vec![
                "-L".to_string(),
                "a.txt".to_string(),
                "missing.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        4 => support::case(vec!["-c", "a.txt"], fixture, b""),
        5 => support::case(vec!["-m", "payload.bin"], fixtures::line_fixture(), b""),
        6 => support::case(vec!["-w", "-", "missing.txt"], fixture, b"\0\x01"),
        7 => support::case(vec!["-", "-"], fixture, b"only once\n"),
        _ => return None,
    })
}
