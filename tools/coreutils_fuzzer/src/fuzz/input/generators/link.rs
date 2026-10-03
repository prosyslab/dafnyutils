use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, ValueContext,
};
use super::super::PatternInputGenerator;
use super::super::{support, system_state};
use crate::fuzz::{DirSpec, FileSpec, GeneratedCase, HardlinkSpec, UtilityProfile};
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

const HELP_OR_VERSION: Atom = Atom::Option(OptionChoice::available(&["--help", "--version"]));
const SOURCE: Atom = Atom::Operand(OperandSource::Generated(link_source));
const TARGET: Atom = Atom::Operand(OperandSource::Generated(link_target));
const EXTRA: Atom = Atom::Operand(OperandSource::Target {
    existing_percent: 50,
});

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::weighted(
        6,
        &[
            Element::repeated(0, 2, HELP_OR_VERSION),
            Element::once(SOURCE),
            Element::once(TARGET),
            Element::up_to_budget(0, EXTRA),
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::repeated(0, 2, HELP_OR_VERSION),
            Element::optional(70, SOURCE),
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::once(SOURCE),
            Element::repeated(1, 2, HELP_OR_VERSION),
            Element::optional(80, TARGET),
            Element::up_to_budget(0, EXTRA),
        ],
    ),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case).with_profile(UtilityProfile {
        requires_path_operand: true,
        prefers_existing_paths: true,
    });

fn link_source(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let files = support::existing_file_operands(context.fixture());
    support::pick_file_or_missing(&files, rng)
}

fn link_target(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let files = support::existing_file_operands(context.fixture());
    if !files.is_empty() && rng.random_bool(0.25) {
        return support::pick_string(&files, rng);
    }

    let name = format!("hard-link-{}", rng.random_range(0..10000));
    if rng.random_bool(0.15) {
        format!("missing-parent/{name}")
    } else {
        name
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let mut fixture = system_state::basic_fixture();
    let args = match iteration {
        0 => vec!["a.txt", "a-hard"],
        1 => vec![],
        2 => vec!["a.txt"],
        3 => vec!["a.txt", "a-hard", "extra"],
        4 => vec!["missing.txt", "a-hard"],
        5 => vec!["a.txt", "target.txt"],
        6 => vec!["", "a-hard"],
        7 => vec!["a.txt", ""],
        8 => vec!["a.txt", "missing-parent/a-hard"],
        9 => vec!["dir", "dir-hard"],
        10 => vec!["--help", "--version"],
        11 => vec!["--version", "--help"],
        12 => vec!["--help", "--bad"],
        13 => vec!["--bad", "--help"],
        14 => vec!["--help=value"],
        15 => vec!["-x"],
        16 => vec!["--thisoptiondoesnotexist"],
        17 => {
            fixture.files.push(FileSpec {
                relative_path: PathBuf::from("--help"),
                bytes: b"option-like source\n".to_vec(),
                mode: 0o644,
            });
            vec!["--", "--help", "--version"]
        }
        18 => vec!["a'b", "target name"],
        19 => {
            fixture.hardlinks.push(HardlinkSpec {
                relative_path: PathBuf::from("alias"),
                source_relative_path: PathBuf::from("a.txt"),
            });
            vec!["alias", "alias-hard"]
        }
        20 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("blocked"),
                mode: 0o555,
            });
            vec!["a.txt", "blocked/a-hard"]
        }
        _ => return None,
    };
    Some(support::case(args, fixture, b""))
}
