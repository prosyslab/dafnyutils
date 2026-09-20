use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueContext, ValueSource,
};
use super::super::PatternInputGenerator;
use super::super::{fixtures, support};
use crate::fuzz::mutation::generate_missing_operands;
use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, GeneratedCase, SymlinkSpec};
use rand::prelude::SliceRandom;
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

const CHMOD_OPTIONS: Element = Element::repeated(
    0,
    4,
    Atom::Option(OptionChoice::available(&[
        "-c",
        "--changes",
        "--dereference",
        "-R",
        "--recursive",
        "-h",
        "--no-dereference",
        "--no-preserve-root",
        "--preserve-root",
        "--quiet",
        "-f",
        "--silent",
        "-v",
        "--verbose",
        "--help",
        "--version",
        "-H",
        "-L",
        "-P",
    ])),
);

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::requiring(
        3,
        &["--reference"],
        &[
            CHMOD_OPTIONS,
            Element::optional(
                25,
                Atom::Value(ValueSource::Generated(random_chmod_mode_value)),
            ),
            Element::once(Atom::OptionValue(OptionValue::new(
                &[
                    OptionValueForm::separate("--reference"),
                    OptionValueForm::equals("--reference"),
                ],
                ValueSource::Generated(random_target),
            ))),
            Element::repeated(
                0,
                4,
                Atom::Operand(OperandSource::Target {
                    existing_percent: 65,
                }),
            )
            .reusing(25),
        ],
    ),
    Alternative::weighted(
        17,
        &[
            CHMOD_OPTIONS,
            Element::optional(20, Atom::Literal("--")),
            Element::once(Atom::Value(ValueSource::Generated(random_chmod_mode_value))),
            Element::repeated(
                0,
                4,
                Atom::Operand(OperandSource::Target {
                    existing_percent: 65,
                }),
            )
            .reusing(25),
        ],
    ),
]);

fn random_target(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let existing = context.fixture().existing_operands();
    let missing = generate_missing_operands(rng);
    support::pick_target_operand(&existing, &missing, rng, false)
}

fn random_chmod_mode_value(_context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    random_chmod_mode(rng)
}

pub(in crate::fuzz::input) fn random_chmod_mode(rng: &mut StdRng) -> String {
    const REQUIRED: &[&str] = &["u+r-w", "+2000", "-7022", "00644", "007777"];
    const NUMERIC: &[&str] = &["0", "000", "600", "0644", "755", "0755", "2755", "7777"];
    const INVALID: &[&str] = &["08", "0999", "10000", "77777", "invalid-mode"];
    match rng.random_range(0..14) {
        0..=4 => REQUIRED[rng.random_range(0..REQUIRED.len())].to_string(),
        5..=7 => NUMERIC[rng.random_range(0..NUMERIC.len())].to_string(),
        8 => INVALID[rng.random_range(0..INVALID.len())].to_string(),
        _ => random_symbolic_chmod_mode(rng),
    }
}

fn random_symbolic_chmod_mode(rng: &mut StdRng) -> String {
    const WHO: &[&str] = &["", "u", "g", "o", "a", "ug", "uo", "go", "ugo"];
    const OPERATORS: &[char] = &['+', '-', '='];
    const PERMISSIONS: &[char] = &['r', 'w', 'x', 'X', 's', 't'];
    const COPIES: &[char] = &['u', 'g', 'o'];
    let clause_count = rng.random_range(1..=3);
    let mut clauses = Vec::with_capacity(clause_count);
    for _ in 0..clause_count {
        let who = WHO[rng.random_range(0..WHO.len())];
        let operator = OPERATORS[rng.random_range(0..OPERATORS.len())];
        let permissions = if rng.random_bool(0.25) {
            COPIES[rng.random_range(0..COPIES.len())].to_string()
        } else {
            let count = rng.random_range(0..=PERMISSIONS.len());
            let mut available = PERMISSIONS.to_vec();
            available.shuffle(rng);
            available.into_iter().take(count).collect()
        };
        clauses.push(format!("{who}{operator}{permissions}"));
    }
    clauses.join(",")
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = match iteration {
        40 => chmod_ordered_recovery_fixture(),
        41 => chmod_inaccessible_fixture(),
        8.. => chmod_domain_fixture(),
        _ => fixtures::basic_fixture(),
    };
    Some(match iteration {
        0 => GeneratedCase {
            argv: vec!["0644".to_string(), "a.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        1 => GeneratedCase {
            argv: vec!["u+x".to_string(), "a.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        2 => GeneratedCase {
            argv: vec!["invalid-mode".to_string(), "a.txt".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        },
        3 => support::case(vec![], fixture, b""),
        4 => support::case(vec!["-f", "0", "no-such"], fixture, b""),
        5 => support::case(vec!["--reference=a.txt", "755", "target.txt"], fixture, b""),
        6 => support::case(vec!["-v", "600", "missing"], fixture, b""),
        7 => support::case(vec!["-R", "0755", "dir"], fixture, b""),
        8 => support::case(vec!["-R", "-L", "u=rwX,g+s,o-t", "."], fixture, b""),
        9 => GeneratedCase {
            argv: vec!["u+x".to_string(), "../root-file".to_string()],
            fixture,
            stdin: Vec::new(),
            cwd: PathBuf::from("tree/child"),
        },
        10 => support::case(
            vec!["-cv", "g=u", "missing", "tree/root-file", "tree/root-file"],
            fixture,
            b"",
        ),
        11 => support::case(vec!["--help", "-Z"], fixture, b""),
        12 => support::case(vec!["--help", "--reference"], fixture, b""),
        13 => support::case(vec!["--version", "-Z"], fixture, b""),
        14 => support::case(vec!["-Z", "--help"], fixture, b""),
        15 => support::case(vec!["--he", "-Z"], fixture, b""),
        16 => support::case(vec!["--help=x"], fixture, b""),
        17 => support::case(vec!["--reference"], fixture, b""),
        18 => support::case(vec!["--re"], fixture, b""),
        19 => support::case(vec!["-vZ", "600", "a.txt"], fixture, b""),
        20 => support::case(vec!["--é"], fixture, b""),
        21 => support::case(vec!["-é"], fixture, b""),
        22 => support::case(vec!["--version", "--help"], fixture, b""),
        23 => support::case(vec!["--help", "--version"], fixture, b""),
        24 => support::case(vec!["u+r-w", "tree/root-file"], fixture, b""),
        25 => support::case(vec!["+2000", "tree"], fixture, b""),
        26 => support::case(vec!["-7022", "tree/root-file"], fixture, b""),
        27 => support::case(vec!["00644", "tree/root-file"], fixture, b""),
        28 => support::case(vec!["007777", "tree/root-file"], fixture, b""),
        29 => support::case(vec!["600", "quote'file"], fixture, b""),
        30 => support::case(vec!["600", "é"], fixture, b""),
        31 => support::case(vec!["600", "tab\tfile"], fixture, b""),
        32 => support::case(vec!["600", ""], fixture, b""),
        33 => support::case(vec!["600", "tree/"], fixture, b""),
        34 => support::case(
            vec!["--reference=tree/root-file", "tree/child/setuid"],
            fixture,
            b"",
        ),
        35 => support::case(vec!["--reference=missing", "tree/root-file"], fixture, b""),
        36 => support::case(
            vec!["-R", "--reference=tree/root-file", "tree"],
            fixture,
            b"",
        ),
        37 => support::case(
            vec!["-h", "--reference=tree/root-file", "file-link"],
            fixture,
            b"",
        ),
        38 => support::case(
            vec!["-v", "--reference=tree/root-file", "tree/child/setuid"],
            fixture,
            b"",
        ),
        39 => support::case(
            vec!["--version", "--reference=tree/root-file"],
            fixture,
            b"",
        ),
        40 => support::case(vec!["u+rwx", "d", "d/e"], fixture, b""),
        41 => support::case(vec!["600", "blocked/child", "tree/root-file"], fixture, b""),
        _ => return None,
    })
}

fn chmod_ordered_recovery_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![
            DirSpec {
                relative_path: PathBuf::from("d"),
                mode: 0,
            },
            DirSpec {
                relative_path: PathBuf::from("d/e"),
                mode: 0,
            },
        ],
        files: Vec::new(),
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}

fn chmod_inaccessible_fixture() -> FixtureBlueprint {
    let mut fixture = chmod_domain_fixture();
    fixture.directories.push(DirSpec {
        relative_path: PathBuf::from("blocked"),
        mode: 0,
    });
    fixture
}

fn chmod_domain_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![
            DirSpec {
                relative_path: PathBuf::from("tree"),
                mode: 0o1777,
            },
            DirSpec {
                relative_path: PathBuf::from("tree/child"),
                mode: 0o2755,
            },
        ],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("tree/root-file"),
                bytes: b"root\n".to_vec(),
                mode: 0o1644,
            },
            FileSpec {
                relative_path: PathBuf::from("tree/child/setuid"),
                bytes: b"child\n".to_vec(),
                mode: 0o4755,
            },
            FileSpec {
                relative_path: PathBuf::from("quote'file"),
                bytes: b"quote\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("é"),
                bytes: b"unicode\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("tab\tfile"),
                bytes: b"tab\n".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: vec![
            SymlinkSpec {
                relative_path: PathBuf::from("file-link"),
                target: PathBuf::from("tree/root-file"),
            },
            SymlinkSpec {
                relative_path: PathBuf::from("dir-link"),
                target: PathBuf::from("tree/child"),
            },
            SymlinkSpec {
                relative_path: PathBuf::from("dangling-link"),
                target: PathBuf::from("missing-target"),
            },
            SymlinkSpec {
                relative_path: PathBuf::from("cycle-a"),
                target: PathBuf::from("cycle-b"),
            },
            SymlinkSpec {
                relative_path: PathBuf::from("cycle-b"),
                target: PathBuf::from("cycle-a"),
            },
        ],
        hardlinks: Vec::new(),
    }
}
