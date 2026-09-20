use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice};
use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    Element::repeated(
        0,
        2,
        Atom::Option(OptionChoice::available(&[
            "-c",
            "--count",
            "-d",
            "--repeated",
            "-u",
            "--unique",
            "-i",
            "--ignore-case",
        ])),
    ),
    Element::optional(
        75,
        Atom::Operand(OperandSource::Stream {
            existing_weight: 6,
            missing_weight: 1,
            stdin_weight: 3,
            allow_repeated_stdin: false,
        }),
    ),
])]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::line_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b"a\na\nb\n"),
        1 => support::case(vec!["-c", "dups.txt"], fixture, b""),
        2 => support::case(vec!["-d", "dups.txt"], fixture, b""),
        3 => support::case(vec!["-u", "dups.txt"], fixture, b""),
        4 => support::case(vec!["-i", "case.txt"], fixture, b""),
        5 => support::case(vec!["missing.txt"], fixture, b""),
        _ => return None,
    })
}
