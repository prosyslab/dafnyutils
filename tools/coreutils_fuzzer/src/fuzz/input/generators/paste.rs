use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueSource,
};
use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    Element::optional(
        35,
        Atom::Option(OptionChoice::available(&["-s", "--serial"])),
    ),
    Element::optional(
        35,
        Atom::Option(OptionChoice::available(&["-z", "--zero-terminated"])),
    ),
    Element::optional(
        45,
        Atom::OptionValue(OptionValue::new(
            &[
                OptionValueForm::separate("-d"),
                OptionValueForm::separate("--delimiters"),
            ],
            ValueSource::Values(&["\t", ",", "|:", "\\0", "ab"]),
        )),
    ),
    Element::repeated(
        0,
        4,
        Atom::Operand(OperandSource::Stream {
            existing_weight: 4,
            missing_weight: 1,
            stdin_weight: 1,
            allow_repeated_stdin: true,
        }),
    ),
])]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::line_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b"a\nb\n"),
        1 => support::case(vec!["a.txt", "b.txt"], fixture, b""),
        2 => support::case(vec!["-s", "a.txt", "b.txt"], fixture, b""),
        3 => support::case(vec!["-d", ",", "a.txt", "-"], fixture, b"x\ny\n"),
        4 => support::case(vec!["a.txt", "missing.txt", "b.txt"], fixture, b""),
        5 => support::case(vec!["-z", "-s", "-"], fixture, b"a\0\0b"),
        6 => support::case(
            vec!["--zero-terminated", "-d", "|:", "-", "empty.txt"],
            fixture,
            b"x\0\0y",
        ),
        _ => return None,
    })
}
