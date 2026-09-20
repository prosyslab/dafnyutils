use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueSource,
};
use super::super::{fixtures, mutation, support, PatternInputGenerator};
use crate::fuzz::{FixtureBlueprint, GeneratedCase};
use rand::rngs::StdRng;
use rand::Rng;

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case).with_mutator(mutate_argv);

const HEAD_MODES: Element = Element::repeated(
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
);
const HEAD_STREAMS: Element = Element::repeated(
    0,
    3,
    Atom::Operand(OperandSource::Stream {
        existing_weight: 4,
        missing_weight: 1,
        stdin_weight: 1,
        allow_repeated_stdin: false,
    }),
);
const HEAD_LEGACY_STREAM: Element = Element::repeated(
    0,
    1,
    Atom::Operand(OperandSource::Stream {
        existing_weight: 4,
        missing_weight: 1,
        stdin_weight: 1,
        allow_repeated_stdin: false,
    }),
);

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::new(&[
        Element::once(Atom::Value(ValueSource::Values(&[
            "-1", "-08", "-1c", "-2b", "-1k", "-1q", "-1v", "-1z",
        ]))),
        HEAD_MODES,
        HEAD_LEGACY_STREAM,
    ]),
    Alternative::new(&[
        Element::once(Atom::OptionValue(OptionValue::new(
            &[
                OptionValueForm::separate("-n"),
                OptionValueForm::separate("--lines"),
                OptionValueForm::separate("-c"),
                OptionValueForm::separate("--bytes"),
                OptionValueForm::equals("--lines"),
                OptionValueForm::equals("--bytes"),
                OptionValueForm::attached("-n"),
                OptionValueForm::attached("-c"),
            ],
            ValueSource::Values(&[
                "0", "1", "2", "10", "-1", "-2", "1b", "2b", "1k", "1K", "1kB", "1M", "-1k", "bad",
            ]),
        ))),
        HEAD_MODES,
        HEAD_STREAMS,
    ]),
    Alternative::weighted(4, &[HEAD_MODES, HEAD_STREAMS]),
]);

fn mutate_argv(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
    argv: &mut Vec<String>,
) {
    if argv.is_empty() || rng.random_bool(0.35) {
        mutation::regenerate_argv(util, option_pool, rng, max_args, fixture, argv);
        return;
    }
    mutation::mutate_existing_argv(
        rng,
        max_args,
        fixture,
        argv,
        support::existing_file_operands,
        random_replacement_value,
    );
}

fn random_replacement_value(argv: &[String], idx: usize, rng: &mut StdRng) -> String {
    let value = mutation::random_argument_value(rng);
    let replacing_stdin = argv.get(idx).is_some_and(|arg| arg == "-");
    if value == "-" && !replacing_stdin && argv.iter().any(|arg| arg == "-") {
        return mutation::random_non_stdin_argument_value(rng);
    }
    value
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::line_fixture();
    Some(match iteration {
        0 => support::case(vec![], fixture, b"0\n1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n"),
        1 => support::case(vec!["-n", "2", "a.txt"], fixture, b""),
        2 => support::case(vec!["-c", "5", "a.txt"], fixture, b""),
        3 => support::case(vec!["-q", "a.txt", "b.txt"], fixture, b""),
        4 => support::case(vec!["-v", "-n", "1", "a.txt", "-"], fixture, b"stdin\n"),
        5 => support::case(vec!["-n", "-2", "a.txt"], fixture, b""),
        6 => support::case(vec!["-z", "-n", "2"], fixture, b"a\0b\0c\0"),
        7 => support::case(vec!["-1", "a.txt"], fixture, b""),
        8 => support::case(vec!["-1c", "payload.bin"], fixture, b""),
        9 => support::case(vec!["-2b", "a.txt"], fixture, b""),
        10 => support::case(vec!["-n", "1k", "a.txt"], fixture, b""),
        11 => support::case(vec!["--bytes=1kB", "payload.bin"], fixture, b""),
        12 => support::case(vec!["-1q", "a.txt", "b.txt"], fixture, b""),
        13 => support::case(vec!["-1v", "a.txt", "-", "b.txt"], fixture, b"stdin\n"),
        _ => return None,
    })
}
