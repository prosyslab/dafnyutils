use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, ValueSource};
use super::super::{mutation, support, PatternInputGenerator};
use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, GeneratedCase};
use std::path::PathBuf;

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    Element::once(Atom::Operand(OperandSource::FileOrMissing {
        existing_percent: 85,
    })),
    Element::repeated(
        1,
        3,
        Atom::Value(ValueSource::Values(&["1", "2", "3", "4", "0"])),
    ),
])]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutation::regenerate_argv);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = csplit_fixture();
    Some(match iteration {
        0 => support::case(vec!["split.txt", "2"], fixture, b""),
        1 => support::case(vec!["-", "3"], fixture, b"red\nblue\ngreen\n"),
        2 => support::case(vec!["split.txt", "2", "4"], fixture, b""),
        3 => support::case(vec!["split.txt", "0"], fixture, b""),
        _ => return None,
    })
}

fn csplit_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("split.txt"),
                bytes: b"red\nblue\ngreen\nyellow\npurple\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha\nbeta\ngamma\ndelta\n".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}
