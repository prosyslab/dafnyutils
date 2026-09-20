use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueSource,
};
use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

const COMPLEMENT: Element =
    Element::optional(35, Atom::Option(OptionChoice::available(&["--complement"])));
const NO_SPLIT: Element = Element::optional(30, Atom::Option(OptionChoice::available(&["-n"])));
const ZERO_TERMINATED: Element = Element::optional(
    30,
    Atom::Option(OptionChoice::available(&["-z", "--zero-terminated"])),
);
const OUTPUT_DELIMITER: Element = Element::optional(
    35,
    Atom::OptionValue(OptionValue::new(
        &[OptionValueForm::separate("--output-delimiter")],
        ValueSource::Values(&[":", "|", "_._", ""]),
    )),
);
const STREAMS: Element = Element::repeated(
    0,
    3,
    Atom::Operand(OperandSource::Stream {
        existing_weight: 4,
        missing_weight: 1,
        stdin_weight: 1,
        allow_repeated_stdin: true,
    }),
);

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::weighted(
        100,
        &[
            Element::once(Atom::OptionValue(OptionValue::new(
                &[
                    OptionValueForm::separate("-b"),
                    OptionValueForm::separate("--bytes"),
                    OptionValueForm::separate("-c"),
                    OptionValueForm::separate("--characters"),
                ],
                ValueSource::Values(&[
                    "1",
                    "1-3",
                    "2-",
                    "-4",
                    "1,3-5",
                    "1-2,3-4",
                    "1-3,2-4,6",
                    "1-3,2-4,6-",
                    "4-,2-3",
                    "2,1-3",
                    "2-,3,4-4,5",
                    "0",
                    "5-2",
                ]),
            ))),
            COMPLEMENT,
            NO_SPLIT,
            ZERO_TERMINATED,
            OUTPUT_DELIMITER,
            STREAMS,
        ],
    ),
    Alternative::new(&[
        Element::once(Atom::Literal("-b")),
        Element::once(Atom::Literal("1-3")),
        COMPLEMENT,
        NO_SPLIT,
        ZERO_TERMINATED,
        OUTPUT_DELIMITER,
        STREAMS,
    ]),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::line_fixture();
    Some(match iteration {
        0 => support::case(vec!["-b", "1-3"], fixture, b"abcdef\n"),
        1 => support::case(vec!["-c", "2-", "a.txt"], fixture, b""),
        2 => support::case(
            vec!["-b", "1,3-5", "a.txt", "-", "b.txt"],
            fixture,
            b"stdin\n",
        ),
        3 => support::case(vec!["-b", "0", "a.txt"], fixture, b""),
        4 => support::case(vec!["--complement", "-b", "2-3"], fixture, b"abcd\nxy\n"),
        5 => support::case(vec!["-z", "-c", "1"], fixture, b"ab\0cd"),
        6 => support::case(
            vec!["-b", "1-2,3-4", "--output-delimiter=:"],
            fixture,
            b"abcd\n",
        ),
        7 => support::case(
            vec!["--output-delimiter", ":", "-c", "1-3,2-4,6-"],
            fixture,
            b"abcdefg\n",
        ),
        8 => support::case(
            vec!["--complement", "-b", "3,4-4,5,2-"],
            fixture,
            b"123456\n",
        ),
        9 => support::case(vec!["-n", "-b", "1,3"], fixture, b"abc\n"),
        10 => support::case(vec!["-b", "1", "-", "-"], fixture, b"once\n"),
        _ => return None,
    })
}
