use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionValue, OptionValueForm,
    ValueContext, ValueSource,
};
use super::super::{fixtures, mutation, support, PatternInputGenerator};
use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, GeneratedCase, SymlinkSpec};
use rand::rngs::StdRng;
use rand::Rng;
use std::path::Path;
use std::path::PathBuf;

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutation::regenerate_argv);

const SOURCE: usize = 0;
const DIRECTORY: usize = 1;

const FILE_SOURCE: Element =
    Element::once(Atom::Operand(OperandSource::Generated(file_source))).captured(SOURCE);
const OTHER_EXISTING_FILE: Element =
    Element::once(Atom::Operand(OperandSource::Generated(other_existing_file)));
const MOVABLE_SOURCE: Element =
    Element::once(Atom::Operand(OperandSource::Generated(movable_source))).captured(SOURCE);
const RENAME_TARGET: Element =
    Element::once(Atom::Operand(OperandSource::Generated(rename_target)));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::requiring(
        1,
        &["-t"],
        &[
            Element::once(Atom::Literal("-t")),
            Element::once(Atom::Operand(OperandSource::Generated(any_directory)))
                .captured(DIRECTORY),
            Element::once(Atom::Operand(OperandSource::Generated(
                safe_source_for_directory,
            )))
            .captured(SOURCE),
            Element::optional(
                55,
                Atom::Operand(OperandSource::Generated(other_safe_source_for_directory)),
            ),
        ],
    ),
    Alternative::requiring(
        1,
        &["-n"],
        &[
            Element::once(Atom::Literal("-n")),
            Element::once(Atom::Operand(OperandSource::Generated(movable_source))).captured(SOURCE),
            Element::once(Atom::Operand(OperandSource::Generated(
                other_existing_movable,
            ))),
        ],
    ),
    Alternative::requiring(
        1,
        &["-v"],
        &[
            Element::once(Atom::Literal("-v")),
            MOVABLE_SOURCE,
            RENAME_TARGET,
        ],
    ),
    Alternative::requiring(
        1,
        &["-T"],
        &[
            Element::once(Atom::Literal("-T")),
            MOVABLE_SOURCE,
            RENAME_TARGET,
        ],
    ),
    Alternative::requiring(
        1,
        &["--debug", "-n"],
        &[
            Element::once(Atom::Literal("--debug")),
            Element::once(Atom::Literal("-n")),
            FILE_SOURCE,
            OTHER_EXISTING_FILE,
        ],
    ),
    Alternative::requiring(
        1,
        &["--strip-trailing-slashes"],
        &[
            Element::once(Atom::Literal("--strip-trailing-slashes")),
            Element::once(Atom::Operand(OperandSource::Generated(
                directory_with_slashes,
            )))
            .captured(SOURCE),
            Element::once(Atom::Operand(OperandSource::Generated(rename_target))),
        ],
    ),
    Alternative::requiring(
        1,
        &["--backup", "-v"],
        &[
            Element::once(Atom::Literal("--backup=numbered")),
            Element::once(Atom::Literal("-v")),
            FILE_SOURCE,
            OTHER_EXISTING_FILE,
        ],
    ),
    Alternative::requiring(
        1,
        &["-b", "-S"],
        &[
            Element::once(Atom::Literal("-b")),
            Element::once(Atom::Literal("-S")),
            Element::once(Atom::Literal(".bak")),
            FILE_SOURCE,
            OTHER_EXISTING_FILE,
        ],
    ),
    Alternative::requiring(
        1,
        &["--backup", "--suffix"],
        &[
            Element::once(Atom::Literal("--backup=existing")),
            Element::once(Atom::Literal("--suffix=.bak")),
            FILE_SOURCE,
            OTHER_EXISTING_FILE,
        ],
    ),
    Alternative::requiring(
        1,
        &["--update", "--debug"],
        &[
            Element::once(Atom::Literal("--debug")),
            Element::once(Atom::Literal("--update=none")),
            FILE_SOURCE,
            OTHER_EXISTING_FILE,
        ],
    ),
    Alternative::requiring(
        1,
        &["--update"],
        &[
            Element::once(Atom::Literal("--update=none-fail")),
            FILE_SOURCE,
            OTHER_EXISTING_FILE,
        ],
    ),
    Alternative::requiring(
        1,
        &["-u"],
        &[
            Element::once(Atom::Literal("-u")),
            FILE_SOURCE,
            OTHER_EXISTING_FILE,
        ],
    ),
    Alternative::requiring(
        1,
        &["--no-copy"],
        &[
            Element::once(Atom::Literal("--no-copy")),
            MOVABLE_SOURCE,
            RENAME_TARGET,
        ],
    ),
    Alternative::requiring(
        1,
        &["-f"],
        &[
            Element::once(Atom::Literal("-f")),
            FILE_SOURCE,
            OTHER_EXISTING_FILE,
        ],
    ),
    Alternative::requiring(
        1,
        &["--target-directory"],
        &[
            Element::once(Atom::OptionValue(OptionValue::new(
                &[OptionValueForm::equals("--target-directory")],
                ValueSource::Generated(any_directory),
            )))
            .captured(DIRECTORY),
            Element::once(Atom::Operand(OperandSource::Generated(
                safe_source_for_directory,
            ))),
        ],
    ),
    Alternative::new(&[
        Element::once(Atom::Operand(OperandSource::Generated(movable_source))).captured(SOURCE),
        Element::once(Atom::Operand(OperandSource::Generated(
            safe_directory_for_source,
        ))),
    ]),
    Alternative::new(&[MOVABLE_SOURCE, RENAME_TARGET]),
]);

fn movable_source(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    support::pick_string(&existing_movable_operands(context.fixture()), rng)
}

fn file_source(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let files = support::existing_file_operands(context.fixture());
    if files.is_empty() {
        movable_source(context, rng)
    } else {
        support::pick_string(&files, rng)
    }
}

fn other_existing_file(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    pick_other(
        support::existing_file_operands(context.fixture()),
        context.capture(SOURCE),
        rng,
    )
}

fn other_existing_movable(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    pick_other(
        existing_movable_operands(context.fixture()),
        context.capture(SOURCE),
        rng,
    )
}

fn pick_other(mut candidates: Vec<String>, excluded: Option<&str>, rng: &mut StdRng) -> String {
    if let Some(excluded) = excluded {
        candidates.retain(|candidate| candidate != excluded);
    }
    if candidates.is_empty() {
        excluded.unwrap_or(".").to_string()
    } else {
        support::pick_string(&candidates, rng)
    }
}

fn rename_target(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    random_rename_target(context.capture(SOURCE).unwrap_or("source"), rng)
}

fn any_directory(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    support::pick_string(&existing_dir_operands(context.fixture()), rng)
}

fn directory_with_slashes(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    format!("{}////", any_directory(context, rng))
}

fn safe_directory_for_source(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let directories = existing_dir_operands(context.fixture());
    let safe = safe_directory_operands_for_source(
        &directories,
        context.capture(SOURCE).unwrap_or("source"),
    );
    support::pick_string(if safe.is_empty() { &directories } else { &safe }, rng)
}

fn safe_source_for_directory(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let directory = context.capture(DIRECTORY).unwrap_or(".");
    let mut sources = existing_movable_operands(context.fixture());
    sources.retain(|source| target_in_directory(directory, source) != *source);
    if sources.is_empty() {
        movable_source(context, rng)
    } else {
        support::pick_string(&sources, rng)
    }
}

fn other_safe_source_for_directory(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let directory = context.capture(DIRECTORY).unwrap_or(".");
    let source = context.capture(SOURCE);
    let mut sources = existing_movable_operands(context.fixture());
    sources.retain(|candidate| {
        source != Some(candidate.as_str())
            && target_in_directory(directory, candidate) != *candidate
    });
    if sources.is_empty() {
        source.unwrap_or(".").to_string()
    } else {
        support::pick_string(&sources, rng)
    }
}

fn existing_movable_operands(fixture: &FixtureBlueprint) -> Vec<String> {
    let mut operands = support::existing_file_operands(fixture);
    operands.extend(
        fixture
            .symlinks
            .iter()
            .map(|symlink| symlink.relative_path.display().to_string()),
    );
    if operands.is_empty() {
        operands.push(".".to_string());
    }
    operands
}

fn existing_dir_operands(fixture: &FixtureBlueprint) -> Vec<String> {
    let mut operands: Vec<String> = fixture
        .directories
        .iter()
        .map(|dir| dir.relative_path.display().to_string())
        .collect();
    if operands.is_empty() {
        operands.push(".".to_string());
    }
    operands
}

fn safe_directory_operands_for_source(directories: &[String], source: &str) -> Vec<String> {
    directories
        .iter()
        .filter(|directory| target_in_directory(directory, source) != source)
        .cloned()
        .collect()
}

fn target_in_directory(directory: &str, source: &str) -> String {
    let leaf = Path::new(source)
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or(source);
    if directory == "." {
        leaf.to_string()
    } else {
        format!("{}/{}", directory.trim_end_matches('/'), leaf)
    }
}

fn random_rename_target(source: &str, rng: &mut StdRng) -> String {
    loop {
        let target = format!("renamed-{}.txt", rng.random_range(0..10000));
        if target != source {
            return target;
        }
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = fixtures::basic_fixture();
    Some(match iteration {
        0 => GeneratedCase {
            argv: vec!["a.txt".to_string(), "renamed.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        1 => GeneratedCase {
            argv: vec!["a.txt".to_string(), "dir".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        2 => GeneratedCase {
            argv: vec![
                "-t".to_string(),
                "dir".to_string(),
                "a.txt".to_string(),
                "b.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        3 => GeneratedCase {
            argv: vec![
                "-n".to_string(),
                "a.txt".to_string(),
                "target.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        4 => GeneratedCase {
            argv: vec!["a-link".to_string(), "moved-link".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        5 => GeneratedCase {
            argv: vec![
                "--debug".to_string(),
                "-n".to_string(),
                "a.txt".to_string(),
                "target.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        6 => GeneratedCase {
            argv: vec![
                "--backup=numbered".to_string(),
                "-v".to_string(),
                "a.txt".to_string(),
                "target.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        7 => GeneratedCase {
            argv: vec![
                "--backup=existing".to_string(),
                "--suffix=.bak".to_string(),
                "a.txt".to_string(),
                "target.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        8 => GeneratedCase {
            argv: vec![
                "--debug".to_string(),
                "--update=none".to_string(),
                "a.txt".to_string(),
                "target.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        9 => GeneratedCase {
            argv: vec![
                "--update=none-fail".to_string(),
                "a.txt".to_string(),
                "target.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        10 => GeneratedCase {
            argv: vec![
                "--strip-trailing-slashes".to_string(),
                "dir////".to_string(),
                "renamed-dir".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        11 => GeneratedCase {
            argv: vec![
                "-u".to_string(),
                "a.txt".to_string(),
                "target.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        12 => GeneratedCase {
            argv: vec![
                "--no-copy".to_string(),
                "a.txt".to_string(),
                "renamed-no-copy.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        13 => GeneratedCase {
            argv: vec![
                "-f".to_string(),
                "a.txt".to_string(),
                "target.txt".to_string(),
            ],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        14 => GeneratedCase {
            argv: vec!["--target-directory=dir".to_string(), "a.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        15 => GeneratedCase {
            argv: vec!["-t".to_string(), "a.txt".to_string(), "b.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        16 => GeneratedCase {
            argv: vec!["-T".to_string(), "a.txt".to_string(), "dir".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        17 => GeneratedCase {
            argv: vec![
                "-T".to_string(),
                "srcdir".to_string(),
                "empty-dest".to_string(),
            ],
            fixture: mv_directory_fixture(),
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        18 => GeneratedCase {
            argv: vec![
                "-T".to_string(),
                "srcdir".to_string(),
                "full-dest".to_string(),
            ],
            fixture: mv_directory_fixture(),
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        19 => GeneratedCase {
            argv: vec!["srcdir".to_string(), "srcdir/child".to_string()],
            fixture: mv_directory_fixture(),
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        20 => GeneratedCase {
            argv: vec!["loop-a/file".to_string(), "loop-out".to_string()],
            fixture: mv_symlink_loop_fixture(),
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        21 => GeneratedCase {
            argv: vec!["missing.txt".to_string(), "target.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        22 => GeneratedCase {
            argv: vec!["a.txt/missing".to_string(), "renamed.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        _ => return None,
    })
}

fn mv_directory_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![
            DirSpec {
                relative_path: PathBuf::from("srcdir"),
                mode: 0o755,
            },
            DirSpec {
                relative_path: PathBuf::from("srcdir/child"),
                mode: 0o755,
            },
            DirSpec {
                relative_path: PathBuf::from("empty-dest"),
                mode: 0o755,
            },
            DirSpec {
                relative_path: PathBuf::from("full-dest"),
                mode: 0o755,
            },
        ],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("srcdir/file.txt"),
                bytes: b"payload\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("full-dest/kept.txt"),
                bytes: b"kept\n".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}

fn mv_symlink_loop_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: Vec::new(),
        files: Vec::new(),
        symlinks: vec![
            SymlinkSpec {
                relative_path: PathBuf::from("loop-a"),
                target: PathBuf::from("loop-b"),
            },
            SymlinkSpec {
                relative_path: PathBuf::from("loop-b"),
                target: PathBuf::from("loop-a"),
            },
        ],
        hardlinks: Vec::new(),
    }
}
