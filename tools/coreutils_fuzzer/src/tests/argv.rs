use crate::fuzz::input::{generate_argv_for_test, mutate_argv, random_chmod_mode_for_test};
use crate::fuzz::mutation::generate_case;
use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint};
use rand::rngs::StdRng;
use rand::SeedableRng;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

fn chmod_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o2755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha\n".to_vec(),
                mode: 0o4755,
            },
            FileSpec {
                relative_path: PathBuf::from("b.txt"),
                bytes: b"beta\n".to_vec(),
                mode: 0o1644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}

fn chmod_option_pool() -> Vec<String> {
    [
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
        "--reference",
        "-f",
        "--silent",
        "-v",
        "--verbose",
        "--help",
        "--version",
        "-H",
        "-L",
        "-P",
    ]
    .into_iter()
    .map(str::to_string)
    .collect()
}

fn chmod_target_operands(argv: &[String]) -> &[String] {
    if let Some(reference) = argv.iter().position(|arg| arg.starts_with("--reference=")) {
        return &argv[reference + 1..];
    }
    if let Some(reference) = argv.iter().position(|arg| arg == "--reference") {
        return &argv[usize::min(reference + 2, argv.len())..];
    }
    const OPTIONS: &[&str] = &[
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
    ];
    let mut mode = 0;
    while mode < argv.len() && OPTIONS.contains(&argv[mode].as_str()) {
        mode += 1;
    }
    if argv.get(mode).is_some_and(|arg| arg == "--") {
        mode += 1;
    }
    &argv[usize::min(mode + 1, argv.len())..]
}

fn generated_chmod_modes() -> BTreeSet<String> {
    (0..4096)
        .map(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            random_chmod_mode_for_test(&mut rng)
        })
        .collect()
}

// Chmod random modes reach chained symbolic, signed numeric, and long valid octal forms.
#[test]
fn chmod_generation_reaches_extended_modes() {
    let modes = generated_chmod_modes();

    for expected in ["u+r-w", "+2000", "-7022", "00644", "007777"] {
        assert!(modes.contains(expected), "missing chmod mode {expected}");
    }
}

// Chmod generation reaches every schema option spelling plus the option terminator.
#[test]
fn chmod_generation_reaches_all_schema_options() {
    let pool = chmod_option_pool();
    let fixture = chmod_fixture();
    let mut seen = BTreeSet::new();

    for seed in 0..8192 {
        let mut rng = StdRng::seed_from_u64(seed);
        let argv = generate_argv_for_test("chmod", &pool, &mut rng, 12, &fixture);
        for arg in argv {
            if arg.starts_with("--reference=") {
                seen.insert("--reference".to_string());
            } else if arg == "--" || pool.contains(&arg) {
                seen.insert(arg);
            }
        }
    }

    let mut expected: BTreeSet<String> = pool.into_iter().collect();
    expected.insert("--".to_string());
    assert_eq!(seen, expected);
}

// Chmod generation reaches attached and separate reference argument spellings.
#[test]
fn chmod_generation_reaches_both_reference_forms() {
    let pool = chmod_option_pool();
    let fixture = chmod_fixture();
    let mut attached = false;
    let mut separate = false;

    for seed in 0..4096 {
        let mut rng = StdRng::seed_from_u64(seed);
        let argv = generate_argv_for_test("chmod", &pool, &mut rng, 12, &fixture);
        attached |= argv.iter().any(|arg| arg.starts_with("--reference="));
        separate |= argv.iter().any(|arg| arg == "--reference");
    }

    assert!(attached);
    assert!(separate);
}

// Chmod random references combine with recursive, no-follow, output, help/version, and conflicting modes.
#[test]
fn chmod_generation_combines_reference_with_other_domains() {
    let pool = chmod_option_pool();
    let fixture = chmod_fixture();
    let mut recursive = false;
    let mut no_follow = false;
    let mut output = false;
    let mut early_exit = false;
    let mut conflict = false;

    for seed in 0..32768 {
        let mut rng = StdRng::seed_from_u64(seed);
        let argv = generate_argv_for_test("chmod", &pool, &mut rng, 12, &fixture);
        let has_reference = argv
            .iter()
            .any(|arg| arg == "--reference" || arg.starts_with("--reference="));
        if !has_reference {
            continue;
        }
        recursive |= argv
            .iter()
            .any(|arg| matches!(arg.as_str(), "-R" | "--recursive"));
        no_follow |= argv
            .iter()
            .any(|arg| matches!(arg.as_str(), "-h" | "--no-dereference"));
        output |= argv
            .iter()
            .any(|arg| matches!(arg.as_str(), "-c" | "--changes" | "-v" | "--verbose"));
        early_exit |= argv
            .iter()
            .any(|arg| matches!(arg.as_str(), "--help" | "--version"));
        conflict |= argv.iter().any(|arg| {
            matches!(
                arg.as_str(),
                "u+r-w" | "+2000" | "-7022" | "00644" | "007777"
            )
        });
    }

    assert!(recursive && no_follow && output && early_exit && conflict);
}

// Chmod generation includes zero through four target operands after its mode source.
#[test]
fn chmod_generation_reaches_zero_through_four_operands() {
    let pool = chmod_option_pool();
    let fixture = chmod_fixture();
    let mut counts = BTreeSet::new();

    for seed in 0..4096 {
        let mut rng = StdRng::seed_from_u64(seed);
        let argv = generate_argv_for_test("chmod", &pool, &mut rng, 12, &fixture);
        counts.insert(chmod_target_operands(&argv).len());
    }

    assert_eq!(counts, BTreeSet::from([0, 1, 2, 3, 4]));
}

// Chmod generation can apply one mode to the same operand more than once.
#[test]
fn chmod_generation_reaches_duplicate_operands() {
    let pool = chmod_option_pool();
    let fixture = chmod_fixture();

    let saw_duplicate = (0..4096).any(|seed| {
        let mut rng = StdRng::seed_from_u64(seed);
        let argv = generate_argv_for_test("chmod", &pool, &mut rng, 12, &fixture);
        let operands = chmod_target_operands(&argv);
        operands
            .iter()
            .enumerate()
            .any(|(index, operand)| operands[..index].contains(operand))
    });

    assert!(saw_duplicate);
}

// Chmod generation combines existing targets with a missing-path failure.
#[test]
fn chmod_generation_reaches_missing_and_existing_operands() {
    let pool = chmod_option_pool();
    let fixture = chmod_fixture();
    let existing: BTreeSet<String> = fixture
        .directories
        .iter()
        .map(|entry| entry.relative_path.display().to_string())
        .chain(
            fixture
                .files
                .iter()
                .map(|entry| entry.relative_path.display().to_string()),
        )
        .collect();

    let saw_mixed = (0..4096).any(|seed| {
        let mut rng = StdRng::seed_from_u64(seed);
        let argv = generate_argv_for_test("chmod", &pool, &mut rng, 12, &fixture);
        let operands = chmod_target_operands(&argv);
        operands.iter().any(|operand| existing.contains(operand))
            && operands.iter().any(|operand| !existing.contains(operand))
    });

    assert!(saw_mixed);
}

// Numeric chmod generation reaches mode-zero, ordinary, special-bit, and maximum boundaries.
#[test]
fn chmod_mode_generation_reaches_numeric_boundaries() {
    let modes = generated_chmod_modes();

    for expected in ["0", "000", "755", "0755", "2755", "7777"] {
        assert!(modes.contains(expected), "missing numeric mode {expected}");
    }
}

// Invalid numeric-like chmod generation reaches bad digits and out-of-range values.
#[test]
fn chmod_mode_generation_reaches_invalid_numeric_like_inputs() {
    let modes = generated_chmod_modes();

    for expected in ["08", "0999", "10000", "77777"] {
        assert!(modes.contains(expected), "missing invalid mode {expected}");
    }
}

// Symbolic chmod generation reaches omitted, individual, and all-class who prefixes.
#[test]
fn chmod_mode_generation_reaches_every_who_class() {
    let modes = generated_chmod_modes();
    let who: BTreeSet<&str> = modes
        .iter()
        .filter_map(|mode| {
            let clause = mode.split(',').next()?;
            let operator = clause.find(['+', '-', '='])?;
            Some(&clause[..operator])
        })
        .collect();

    for expected in ["", "u", "g", "o", "a"] {
        assert!(who.contains(expected), "missing who class {expected:?}");
    }
}

// Symbolic chmod generation reaches add, remove, and replacement operations.
#[test]
fn chmod_mode_generation_reaches_every_operator() {
    let modes = generated_chmod_modes();

    for operator in ['+', '-', '='] {
        assert!(
            modes.iter().any(|mode| mode.contains(operator)),
            "missing operator {operator}"
        );
    }
}

// Symbolic chmod generation reaches every ordinary and conditional permission letter.
#[test]
fn chmod_mode_generation_reaches_every_permission_letter() {
    let modes = generated_chmod_modes();

    for permission in ['r', 'w', 'x', 'X', 's', 't'] {
        assert!(
            modes.iter().any(|mode| mode.contains(permission)),
            "missing permission {permission}"
        );
    }
}

// Symbolic chmod generation reaches copies from each existing permission class.
#[test]
fn chmod_mode_generation_reaches_every_copy_source() {
    let modes = generated_chmod_modes();

    for copy in ['u', 'g', 'o'] {
        assert!(
            modes.iter().any(|mode| {
                mode.split(',').any(|clause| {
                    clause
                        .find(['+', '-', '='])
                        .is_some_and(|operator| clause[operator + 1..] == copy.to_string())
                })
            }),
            "missing copy source {copy}"
        );
    }
}

// Symbolic chmod generation reaches left-to-right multi-clause expressions.
#[test]
fn chmod_mode_generation_reaches_sequential_clauses() {
    assert!(generated_chmod_modes()
        .iter()
        .any(|mode| mode.matches(',').count() >= 1));
}

// Comm generation uses the sorted left/right fixtures required by the utility.
#[test]
fn comm_generation_uses_sorted_fixture_inputs() {
    let mut rng = StdRng::seed_from_u64(17);

    let case = generate_case("comm", &["-1".to_string()], &mut rng, 8, 8);

    assert!(case.argv.iter().any(|arg| arg == "left.txt"));
    assert!(case.argv.iter().any(|arg| arg == "right.txt"));
    assert!(case
        .fixture
        .files
        .iter()
        .any(|file| file.relative_path.as_path() == Path::new("left.txt")
            && file.bytes == b"apple\nbanana\nbanana\norange\n"));
}

// Comm generation reaches delimiter, total, NUL-record, stdin, and conflict shapes.
#[test]
fn comm_generation_exercises_delimiter_total_zero_and_stdin_modes() {
    let pool = vec![
        "-1".to_string(),
        "-2".to_string(),
        "-3".to_string(),
        "-z".to_string(),
        "--zero-terminated".to_string(),
        "--total".to_string(),
        "--output-delimiter".to_string(),
    ];
    let mut saw_delimiter = false;
    let mut saw_total = false;
    let mut saw_zero = false;
    let mut saw_stdin = false;
    let mut saw_delimiter_conflict = false;

    for seed in 0..128 {
        let mut rng = StdRng::seed_from_u64(seed);
        let case = generate_case("comm", &pool, &mut rng, 8, 8);
        saw_delimiter |= case
            .argv
            .iter()
            .any(|arg| arg == "--output-delimiter" || arg.starts_with("--output-delimiter="));
        saw_total |= case.argv.iter().any(|arg| arg == "--total");
        saw_zero |= case
            .argv
            .iter()
            .any(|arg| arg == "-z" || arg == "--zero-terminated" || arg.starts_with("-z"));
        saw_stdin |= case.argv.iter().filter(|arg| arg.as_str() == "-").count() == 1
            && !case.stdin.is_empty();
        saw_delimiter_conflict |= case.argv.iter().any(|arg| arg == "--output-delimiter=,")
            && case.argv.iter().any(|arg| arg == "--output-delimiter=+");
    }

    assert!(saw_delimiter);
    assert!(saw_total);
    assert!(saw_zero);
    assert!(saw_stdin);
    assert!(saw_delimiter_conflict);
}

// Comm generation preserves GNU's bundled column-suppression spellings as pattern alternatives.
#[test]
fn comm_generation_reaches_bundled_suppression_options() {
    let pool = vec!["-1".to_string(), "-2".to_string(), "-3".to_string()];

    let reached = (0..256).any(|seed| {
        let mut rng = StdRng::seed_from_u64(seed);
        let case = generate_case("comm", &pool, &mut rng, 8, 8);
        case.argv
            .iter()
            .any(|arg| matches!(arg.as_str(), "-12" | "-13" | "-23" | "-123"))
    });

    assert!(reached);
}

// Cut generation always couples its selected field/byte mode with a value.
#[test]
fn cut_generation_includes_selection_option_and_value() {
    let mut rng = StdRng::seed_from_u64(23);
    let pool = vec![
        "-b".to_string(),
        "-c".to_string(),
        "-z".to_string(),
        "--zero-terminated".to_string(),
        "-n".to_string(),
        "--complement".to_string(),
        "--output-delimiter".to_string(),
    ];

    let case = generate_case("cut", &pool, &mut rng, 8, 8);

    let selector_index = case
        .argv
        .iter()
        .position(|arg| arg == "-b" || arg == "-c")
        .expect("cut generator should choose a selector option");
    assert!(case.argv.get(selector_index + 1).is_some());
}

// Cut argv generation should include every delimiter-expansion option across seeded cases.
#[test]
fn cut_generation_exercises_delimiter_expansion_options() {
    let pool = vec![
        "-b".to_string(),
        "-c".to_string(),
        "-z".to_string(),
        "--zero-terminated".to_string(),
        "-n".to_string(),
        "--complement".to_string(),
        "--output-delimiter".to_string(),
    ];

    let mut saw_zero_terminated = false;
    let mut saw_no_split = false;
    let mut saw_output_delimiter = false;
    let mut saw_complement = false;

    for seed in 0..128 {
        let mut rng = StdRng::seed_from_u64(seed);
        let case = generate_case("cut", &pool, &mut rng, 10, 8);
        saw_zero_terminated |= case
            .argv
            .iter()
            .any(|arg| arg == "-z" || arg == "--zero-terminated");
        saw_no_split |= case.argv.iter().any(|arg| arg == "-n");
        saw_output_delimiter |= case.argv.iter().any(|arg| arg == "--output-delimiter");
        saw_complement |= case.argv.iter().any(|arg| arg == "--complement");
    }

    assert!(saw_zero_terminated);
    assert!(saw_no_split);
    assert!(saw_output_delimiter);
    assert!(saw_complement);
}

// Symbolic ln generation keeps the option plus source and destination shape.
#[test]
fn ln_generation_stays_on_symbolic_two_operand_shape() {
    let mut rng = StdRng::seed_from_u64(29);
    let pool = vec!["-s".to_string(), "--symbolic".to_string()];

    let case = generate_case("ln", &pool, &mut rng, 8, 8);

    assert!(case.argv[0] == "-s" || case.argv[0] == "--symbolic");
    assert_eq!(case.argv.len(), 3);
}

// Mv argv generation should exercise no-copy as a rename-only option.
#[test]
fn mv_generation_exercises_no_copy_option() {
    let pool = vec!["--no-copy".to_string()];
    let fixture = mv_fixture();

    let saw_no_copy = (0..256).any(|seed| {
        let mut rng = StdRng::seed_from_u64(seed);
        let argv = generate_argv_for_test("mv", &pool, &mut rng, 8, &fixture);
        argv.iter().any(|arg| arg == "--no-copy")
    });

    assert!(saw_no_copy);
}

// Mv argv generation should exercise force overwrites of existing files.
#[test]
fn mv_generation_exercises_force_option() {
    let pool = vec!["-f".to_string()];
    let fixture = mv_fixture();

    let saw_force = (0..256).any(|seed| {
        let mut rng = StdRng::seed_from_u64(seed);
        let argv = generate_argv_for_test("mv", &pool, &mut rng, 8, &fixture);
        argv.iter().any(|arg| arg == "-f")
    });

    assert!(saw_force);
}

// Mv argv generation should exercise long target-directory syntax.
#[test]
fn mv_generation_exercises_long_target_directory_option() {
    let pool = vec!["--target-directory".to_string()];
    let fixture = mv_fixture();

    let saw_target_directory = (0..256).any(|seed| {
        let mut rng = StdRng::seed_from_u64(seed);
        let argv = generate_argv_for_test("mv", &pool, &mut rng, 8, &fixture);
        argv.iter()
            .any(|arg| arg.starts_with("--target-directory="))
    });

    assert!(saw_target_directory);
}

// Fold generation restricts inputs to the supported byte-column text slice.
#[test]
fn fold_generation_stays_inside_byte_column_text_slice() {
    for seed in 0..32 {
        let mut rng = StdRng::seed_from_u64(seed);
        let case = generate_case("fold", &[], &mut rng, 8, 8);

        // Fold random cases stay out of GNU control-character display-width behavior.
        assert!(
            case.fixture
                .files
                .iter()
                .all(|file| is_byte_column_text(&file.bytes)),
            "seed {seed} generated a non-text fold fixture"
        );
        assert!(
            case.stdin.is_empty() || is_byte_column_text(&case.stdin),
            "seed {seed} generated non-text fold stdin"
        );
    }
}

// Head random generation reaches legacy counts, suffixes, headers, and stdin operands.
#[test]
fn head_generation_exercises_legacy_counts_suffixes_and_headers() {
    let pool = vec![
        "-n".to_string(),
        "--lines".to_string(),
        "-c".to_string(),
        "--bytes".to_string(),
        "-q".to_string(),
        "--quiet".to_string(),
        "--silent".to_string(),
        "-v".to_string(),
        "--verbose".to_string(),
        "-z".to_string(),
        "--zero-terminated".to_string(),
    ];
    let mut saw_legacy = false;
    let mut saw_multiplier = false;
    let mut saw_header = false;
    let mut saw_stdin = false;

    for seed in 0..128 {
        let mut rng = StdRng::seed_from_u64(seed);
        let case = generate_case("head", &pool, &mut rng, 8, 8);

        saw_legacy |= case
            .argv
            .iter()
            .any(|arg| matches!(arg.as_str(), "-1" | "-08" | "-1c" | "-2b" | "-1k"));
        saw_multiplier |= case
            .argv
            .iter()
            .any(|arg| arg.contains("1k") || arg.contains("1K") || arg.contains("2b"));
        saw_header |= case.argv.iter().any(|arg| {
            matches!(
                arg.as_str(),
                "-q" | "--quiet" | "--silent" | "-v" | "--verbose" | "-1q" | "-1v"
            )
        });
        saw_stdin |= case.argv.iter().any(|arg| arg == "-");
        assert!(
            case.argv.iter().filter(|arg| arg.as_str() == "-").count() <= 1,
            "seed {seed} generated repeated stdin operands: {:?}",
            case.argv
        );
    }

    assert!(saw_legacy);
    assert!(saw_multiplier);
    assert!(saw_header);
    assert!(saw_stdin);
}

// Head corpus mutation stays inside finite stream operands.
#[test]
fn head_mutation_does_not_introduce_directory_operands() {
    let fixture = FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![FileSpec {
            relative_path: PathBuf::from("a.txt"),
            bytes: b"alpha\n".to_vec(),
            mode: 0o644,
        }],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    };

    for seed in 0..4096 {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut argv = vec!["a.txt".to_string()];

        mutate_argv("head", &[], &mut rng, 4, &fixture, &mut argv);

        assert!(
            !argv.iter().any(|arg| arg == "dir"),
            "seed {seed} introduced a directory operand: {argv:?}"
        );
    }
}

// Head corpus mutation avoids repeated stdin operands that depend on descriptor position.
#[test]
fn head_mutation_does_not_duplicate_stdin_operands() {
    let fixture = FixtureBlueprint {
        directories: Vec::new(),
        files: vec![FileSpec {
            relative_path: PathBuf::from("a.txt"),
            bytes: b"alpha\n".to_vec(),
            mode: 0o644,
        }],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    };

    for seed in 0..4096 {
        let mut rng = StdRng::seed_from_u64(seed);
        let mut argv = vec!["-".to_string(), "a.txt".to_string()];

        mutate_argv("head", &[], &mut rng, 4, &fixture, &mut argv);

        assert!(
            argv.iter().filter(|arg| arg.as_str() == "-").count() <= 1,
            "seed {seed} duplicated stdin operands: {argv:?}"
        );
    }
}

// Expand generation reaches tab configuration, initial-only mode, and stream operands.
#[test]
fn expand_generation_exercises_tabs_initial_and_stream_operands() {
    let pool = vec![
        "-i".to_string(),
        "--initial".to_string(),
        "-t".to_string(),
        "--tabs".to_string(),
    ];
    let mut saw_initial = false;
    let mut saw_tabs = false;
    let mut saw_stream_operand = false;

    for seed in 0..64 {
        let mut rng = StdRng::seed_from_u64(seed);
        let case = generate_case("expand", &pool, &mut rng, 8, 8);
        saw_initial |= case
            .argv
            .iter()
            .any(|arg| arg == "-i" || arg == "--initial");
        saw_tabs |= case.argv.iter().any(|arg| {
            arg == "-t" || arg == "--tabs" || arg.starts_with("-t") || arg.starts_with("--tabs=")
        });
        saw_stream_operand |= case
            .argv
            .iter()
            .any(|arg| arg == "-" || arg.ends_with(".txt"));
    }

    assert!(saw_initial);
    assert!(saw_tabs);
    assert!(saw_stream_operand);
}

// Printenv random cases avoid whole-environment output that differs between native and dotnet runners.
#[test]
fn printenv_generation_uses_explicit_variable_operands() {
    let pool = vec![
        "-0".to_string(),
        "--null".to_string(),
        "--help".to_string(),
        "--version".to_string(),
    ];

    for seed in 0..128 {
        let mut rng = StdRng::seed_from_u64(seed);
        let case = generate_case("printenv", &pool, &mut rng, 8, 8);

        assert!(
            printenv_has_stable_shape(&case.argv),
            "seed {seed} generated unstable printenv argv: {:?}",
            case.argv
        );
    }
}

fn printenv_has_stable_shape(argv: &[String]) -> bool {
    let mut after_options = false;
    for arg in argv {
        if matches!(arg.as_str(), "--help" | "--version") {
            return true;
        }
        if after_options {
            return true;
        }
        match arg.as_str() {
            "-0" | "--null" => {}
            "--" => after_options = true,
            _ => return true,
        }
    }
    false
}

fn is_byte_column_text(bytes: &[u8]) -> bool {
    bytes
        .iter()
        .all(|byte| matches!(*byte, b'\n' | b' '..=b'~'))
}

fn mv_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("b.txt"),
                bytes: b"beta\n".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}
