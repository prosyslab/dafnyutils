use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueContext, ValueSource,
};
use super::super::{mutation, support, PatternInputGenerator};
use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, GeneratedCase};
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

const ZERO_TERMINATED: Element = Element::optional(
    35,
    Atom::Option(OptionChoice::available(&["-z", "--zero-terminated"])),
);
const TOTAL: Element = Element::optional(35, Atom::Option(OptionChoice::available(&["--total"])));
const SUPPRESSIONS: Element = Element::repeated(
    0,
    3,
    Atom::Option(OptionChoice::available(&["-1", "-2", "-3"])),
);
const BUNDLED_SUPPRESSION: Element = Element::once(Atom::Value(ValueSource::Values(&[
    "-12", "-13", "-23", "-123",
])));
const DELIMITER: Element = Element::optional(
    45,
    Atom::OptionValue(OptionValue::new(
        &[
            OptionValueForm::equals("--output-delimiter"),
            OptionValueForm::separate("--output-delimiter"),
        ],
        ValueSource::Values(&[",", "", "++"]),
    )),
);
const SECOND_DELIMITER: Element = Element::optional(
    20,
    Atom::OptionValue(OptionValue::new(
        &[OptionValueForm::equals("--output-delimiter")],
        ValueSource::Values(&[",", "+"]),
    )),
);
const LEFT: Element = Element::once(Atom::Operand(OperandSource::Generated(comm_left)));
const RIGHT: Element = Element::once(Atom::Operand(OperandSource::Generated(comm_right)));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::weighted(
        13,
        &[
            ZERO_TERMINATED,
            TOTAL,
            SUPPRESSIONS,
            DELIMITER,
            SECOND_DELIMITER,
            LEFT,
            RIGHT,
        ],
    ),
    Alternative::requiring(
        7,
        &["-1", "-2", "-3"],
        &[
            ZERO_TERMINATED,
            TOTAL,
            BUNDLED_SUPPRESSION,
            DELIMITER,
            SECOND_DELIMITER,
            LEFT,
            RIGHT,
        ],
    ),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutation::regenerate_argv);

fn comm_left(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    if rng.random_bool(0.09) {
        return "-".to_string();
    }
    let zero_terminated = context
        .argv()
        .iter()
        .any(|arg| matches!(arg.as_str(), "-z" | "--zero-terminated"));
    let preferred = if zero_terminated {
        "left0.txt"
    } else {
        "left.txt"
    };
    pick_preferred_file(context, preferred, rng)
}

fn comm_right(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    if !context.argv().iter().any(|arg| arg == "-") && rng.random_bool(0.09) {
        return "-".to_string();
    }
    let zero_terminated = context
        .argv()
        .iter()
        .any(|arg| matches!(arg.as_str(), "-z" | "--zero-terminated"));
    let preferred = if zero_terminated {
        "right0.txt"
    } else {
        "right.txt"
    };
    pick_preferred_file(context, preferred, rng)
}

fn pick_preferred_file(context: &ValueContext<'_>, preferred: &str, rng: &mut StdRng) -> String {
    let files = support::existing_file_operands(context.fixture());
    if files.is_empty() || files.iter().any(|file| file == preferred) {
        preferred.to_string()
    } else {
        support::pick_string(&files, rng)
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = comm_fixture();
    Some(match iteration {
        0 => support::case(vec!["left.txt", "right.txt"], fixture, b""),
        1 => support::case(vec!["-1", "left.txt", "right.txt"], fixture, b""),
        2 => support::case(vec!["-2", "-3", "left.txt", "right.txt"], fixture, b""),
        3 => support::case(vec!["left.txt", "missing.txt"], fixture, b""),
        4 => support::case(
            vec!["--output-delimiter=,", "left.txt", "right.txt"],
            fixture,
            b"",
        ),
        5 => support::case(
            vec!["--output-delimiter=", "left.txt", "right.txt"],
            fixture,
            b"",
        ),
        6 => support::case(
            vec!["--total", "-123", "left.txt", "right.txt"],
            fixture,
            b"",
        ),
        7 => support::case(vec!["-z", "left0.txt", "right0.txt"], fixture, b""),
        8 => support::case(
            vec![
                "--total",
                "-z123",
                "--output-delimiter=,",
                "left0.txt",
                "right0.txt",
            ],
            fixture,
            b"",
        ),
        9 => support::case(
            vec!["-", "right.txt"],
            fixture,
            b"apple\nbanana\nbanana\norange\n",
        ),
        10 => support::case(
            vec![
                "--output-delimiter=,",
                "--output-delimiter=+",
                "left.txt",
                "right.txt",
            ],
            fixture,
            b"",
        ),
        _ => return None,
    })
}

fn comm_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("left.txt"),
                bytes: b"apple\nbanana\nbanana\norange\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("right.txt"),
                bytes: b"banana\ncarrot\norange\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("left0.txt"),
                bytes: b"apple\0banana\0banana\0orange\0".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("right0.txt"),
                bytes: b"banana\0carrot\0orange\0".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}
