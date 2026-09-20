use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionValue, OptionValueForm,
    ValueSource,
};
use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;

const STREAMS: Element = Element::repeated(
    0,
    2,
    Atom::Operand(OperandSource::Stream {
        existing_weight: 4,
        missing_weight: 1,
        stdin_weight: 1,
        allow_repeated_stdin: true,
    }),
);

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::new(&[
        Element::once(Atom::OptionValue(OptionValue::new(
            &[
                OptionValueForm::separate("-b"),
                OptionValueForm::separate("--body-numbering"),
            ],
            ValueSource::Values(&["a", "n", "t", "q"]),
        ))),
        STREAMS,
    ]),
    Alternative::new(&[
        Element::once(Atom::OptionValue(OptionValue::new(
            &[
                OptionValueForm::separate("-n"),
                OptionValueForm::separate("--number-format"),
            ],
            ValueSource::Values(&["ln", "rn", "rz", "bad"]),
        ))),
        STREAMS,
    ]),
    Alternative::new(&[
        Element::once(Atom::OptionValue(OptionValue::new(
            &[
                OptionValueForm::separate("-s"),
                OptionValueForm::separate("--number-separator"),
            ],
            ValueSource::Values(&[":", "|", "\t", "  "]),
        ))),
        STREAMS,
    ]),
    Alternative::new(&[STREAMS]),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::line_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b"one\n\ntwo\n"),
        1 => support::case(vec!["-b", "a", "a.txt"], fixture, b""),
        2 => support::case(
            vec!["-n", "ln", "-s", ":", "a.txt", "-"],
            fixture,
            b"stdin\n",
        ),
        3 => support::case(vec!["-b", "n", "a.txt"], fixture, b""),
        4 => support::case(vec!["-n", "bad", "a.txt"], fixture, b""),
        _ => return None,
    })
}
