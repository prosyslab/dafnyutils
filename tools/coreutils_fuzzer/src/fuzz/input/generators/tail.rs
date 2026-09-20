use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueSource,
};
use super::super::{fixtures, mutation, support, PatternInputGenerator};
use crate::fuzz::GeneratedCase;

const TAIL_STREAMS: Element = Element::repeated(
    0,
    3,
    Atom::Operand(OperandSource::Stream {
        existing_weight: 4,
        missing_weight: 1,
        stdin_weight: 1,
        allow_repeated_stdin: true,
    }),
);
const TAIL_LEGACY_STREAM: Element = Element::repeated(
    0,
    1,
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
                OptionValueForm::separate("-n"),
                OptionValueForm::separate("--lines"),
                OptionValueForm::separate("-c"),
                OptionValueForm::separate("--bytes"),
            ],
            ValueSource::Values(&[
                "0", "1", "2", "10", "-1", "+2", "1k", "1KiB", "1G", "1GiB", "1EB", "m", "bad",
                "9x",
            ]),
        ))),
        TAIL_STREAMS,
    ]),
    Alternative::new(&[
        Element::once(Atom::Value(ValueSource::Values(&[
            "-1", "+2", "+2c", "-1c", "-1l", "+2l", "-l", "-b", "+c", "+l",
        ]))),
        TAIL_LEGACY_STREAM,
    ]),
    Alternative::new(&[
        Element::repeated(
            0,
            2,
            Atom::Option(OptionChoice::available(&[
                "-q",
                "--quiet",
                "--silent",
                "-v",
                "--verbose",
                "-z",
                "--zero-terminated",
            ])),
        ),
        TAIL_STREAMS,
    ]),
    Alternative::weighted(3, &[TAIL_STREAMS]),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutation::regenerate_argv);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::line_fixture();
    Some(match iteration {
        0 => support::case(vec!["-z", "-n", "2"], fixture, b"a\0b\0c\0"),
        1 => support::case(vec!["+2c"], fixture, b"abcd"),
        2 => support::case(vec!["-1c"], fixture, b"abcd"),
        3 => support::case(vec!["-1"], fixture, b"x\ny\n"),
        4 => support::case(vec!["-l"], fixture, b"x\ny\ny\ny\ny\ny\ny\ny\ny\ny\ny\nz"),
        5 => support::case(vec!["-b"], fixture, b"abcdef"),
        6 => support::case(vec!["-c", "1G", "a.txt"], fixture, b""),
        7 => support::case(vec!["-n", "m", "a.txt"], fixture, b""),
        _ => return None,
    })
}
