use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, ValueContext, ValueSource,
};
use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::GeneratedCase;
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

const MORE_TARGETS: Element = Element::up_to_budget(
    0,
    Atom::Operand(OperandSource::Target {
        existing_percent: 100,
    }),
);

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::requiring(
        1,
        &["-c"],
        &[
            Element::once(Atom::Literal("-c")),
            Element::once(Atom::Operand(OperandSource::Missing)),
            MORE_TARGETS,
        ],
    ),
    Alternative::requiring(
        1,
        &["-r"],
        &[
            Element::once(Atom::Literal("-r")),
            Element::once(Atom::Operand(OperandSource::ExistingFile)),
            Element::once(Atom::Operand(OperandSource::Target {
                existing_percent: 65,
            })),
            MORE_TARGETS,
        ],
    ),
    Alternative::requiring(
        1,
        &["-d"],
        &[
            Element::once(Atom::Literal("-d")),
            Element::once(Atom::Value(ValueSource::Generated(random_date_value))),
            Element::once(Atom::Operand(OperandSource::Target {
                existing_percent: 65,
            })),
            MORE_TARGETS,
        ],
    ),
    Alternative::requiring(
        1,
        &["-t"],
        &[
            Element::once(Atom::Literal("-t")),
            Element::once(Atom::Value(ValueSource::Generated(random_touch_timestamp))),
            Element::once(Atom::Operand(OperandSource::Target {
                existing_percent: 65,
            })),
            MORE_TARGETS,
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::repeated(
                0,
                2,
                Atom::Option(OptionChoice::available(&["-a", "-m", "-c", "--no-create"])),
            ),
            Element::once(Atom::Operand(OperandSource::Target {
                existing_percent: 100,
            })),
            MORE_TARGETS,
        ],
    ),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

fn random_touch_timestamp(_context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    if rng.random_bool(0.2) {
        return "bad-timestamp".to_string();
    }
    format!(
        "{:04}{:02}{:02}{:02}{:02}.{:02}",
        rng.random_range(1971..=2035),
        rng.random_range(1..=12),
        rng.random_range(1..=28),
        rng.random_range(0..=23),
        rng.random_range(0..=59),
        rng.random_range(0..=59)
    )
}

fn random_date_value(_context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    random_date_string(rng)
}

pub(in crate::fuzz::input) fn random_date_string(rng: &mut StdRng) -> String {
    match rng.random_range(0..5) {
        0 => "1970-01-01 00:00:00 UTC".to_string(),
        1 => "2001-09-09 01:46:40 UTC".to_string(),
        2 => "next monday".to_string(),
        3 => "invalid-date".to_string(),
        _ => format!("2024-01-{:02} 12:34:56 UTC", rng.random_range(1..=28)),
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => GeneratedCase {
            argv: vec!["new.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        1 => GeneratedCase {
            argv: vec!["-c".to_string(), "missing.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        2 => GeneratedCase {
            argv: vec![
                "-r".to_string(),
                "a.txt".to_string(),
                "target.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        3 => support::case(
            vec!["-d", "1970-01-01 00:00:00 UTC", "target.txt"],
            fixture,
            b"",
        ),
        4 => support::case(vec!["-t", "200109090146.40", "target.txt"], fixture, b""),
        5 => support::case(vec!["--time=a", "created.txt"], fixture, b""),
        6 => support::case(vec!["--time", "-m", "created.txt"], fixture, b""),
        7 => support::case(vec!["-t", "not-a-timestamp", "created.txt"], fixture, b""),
        8 => support::case(vec!["-cm", "missing.txt"], fixture, b""),
        _ => return None,
    })
}
