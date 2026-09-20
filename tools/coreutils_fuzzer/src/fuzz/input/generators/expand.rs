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
        Atom::Option(OptionChoice::with_fallback(&["-i", "--initial"], "-i")),
    ),
    Element::optional(
        80,
        Atom::OptionValue(OptionValue::new(
            &[
                OptionValueForm::attached("-t"),
                OptionValueForm::equals("--tabs"),
                OptionValueForm::separate("-t"),
                OptionValueForm::separate("--tabs"),
            ],
            ValueSource::Values(&[
                "3", "3,6,9", "3 6 9", "1,/5", "1,+5", "/5", "+5", "a", "0", "3,3", "/3,6,8", "3/",
            ]),
        )),
    ),
    Element::repeated(
        0,
        3,
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
        0 => support::case(vec!["--tabs=3", "-i"], fixture, b" \ta\tb\n"),
        1 => support::case(vec!["--tabs=1,/5"], fixture, b"\ta\tb\tc"),
        2 => support::case(vec!["--tabs=1,+5"], fixture, b"\ta\tb\tc"),
        3 => support::case(
            vec!["--tabs=4", "a.txt", "-", "b.txt"],
            fixture,
            b"stdin\tfield\n",
        ),
        4 => support::case(vec![], fixture, b"aaa\x08\x08\x08c\td\n"),
        5 => support::case(vec!["--tabs=/3,6,8"], fixture, b"a\tb\n"),
        _ => return None,
    })
}
