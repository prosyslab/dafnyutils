use crate::fuzz::input::scenario_case;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

// The recursive chmod seed carries nested nodes with regular and special permission bits.
#[test]
fn chmod_recursive_scenario_covers_nested_special_mode_fixture() {
    let scenario = scenario_case("chmod", 8).expect("chmod recursive domain scenario");

    assert!(scenario
        .fixture
        .directories
        .iter()
        .any(|dir| dir.relative_path.as_path() == Path::new("tree/child") && dir.mode == 0o2755));
    assert!(scenario.fixture.files.iter().any(|file| {
        file.relative_path.as_path() == Path::new("tree/child/setuid") && file.mode == 0o4755
    }));
}

// The recursive chmod seed can address the fixture root explicitly.
#[test]
fn chmod_recursive_scenario_covers_root_relative_operand() {
    let scenario = scenario_case("chmod", 8).expect("chmod recursive domain scenario");

    assert_eq!(scenario.argv.last().map(String::as_str), Some("."));
}

// The recursive chmod seed includes links to a file, directory, and missing target.
#[test]
fn chmod_recursive_scenario_covers_symlink_target_classes() {
    let scenario = scenario_case("chmod", 8).expect("chmod recursive domain scenario");
    let targets: BTreeSet<PathBuf> = scenario
        .fixture
        .symlinks
        .iter()
        .map(|link| link.target.clone())
        .collect();

    assert!(targets.contains(&PathBuf::from("tree/root-file")));
    assert!(targets.contains(&PathBuf::from("tree/child")));
    assert!(targets.contains(&PathBuf::from("missing-target")));
}

// The recursive chmod seed includes a two-link resolution cycle.
#[test]
fn chmod_recursive_scenario_covers_symlink_cycle() {
    let scenario = scenario_case("chmod", 8).expect("chmod recursive domain scenario");

    assert!(scenario.fixture.symlinks.iter().any(|link| {
        link.relative_path.as_path() == Path::new("cycle-a")
            && link.target.as_path() == Path::new("cycle-b")
    }));
    assert!(scenario.fixture.symlinks.iter().any(|link| {
        link.relative_path.as_path() == Path::new("cycle-b")
            && link.target.as_path() == Path::new("cycle-a")
    }));
}

// A non-root cwd seed addresses a valid target through a parent-relative operand.
#[test]
fn chmod_scenario_covers_cwd_relative_operand() {
    let scenario = scenario_case("chmod", 9).expect("chmod cwd-relative scenario");

    assert_eq!(scenario.cwd, PathBuf::from("tree/child"));
    assert_eq!(
        scenario.argv.last().map(String::as_str),
        Some("../root-file")
    );
}

// A verbose changes seed combines a missing path, valid path, and duplicate operand in order.
#[test]
fn chmod_scenario_covers_output_failure_and_duplicate_batch() {
    let scenario = scenario_case("chmod", 10).expect("chmod output failure scenario");

    assert_eq!(
        scenario.argv,
        ["-cv", "g=u", "missing", "tree/root-file", "tree/root-file"]
    );
}

// Each approved chmod parser boundary has its own deterministic argv scenario.
#[test]
fn chmod_scenarios_cover_parser_boundaries() {
    let expected = [
        vec!["--help", "-Z"],
        vec!["--help", "--reference"],
        vec!["--version", "-Z"],
        vec!["-Z", "--help"],
        vec!["--he", "-Z"],
        vec!["--help=x"],
        vec!["--reference"],
        vec!["--re"],
        vec!["-vZ", "600", "a.txt"],
        vec!["--é"],
        vec!["-é"],
        vec!["--version", "--help"],
        vec!["--help", "--version"],
    ];

    for (offset, argv) in expected.into_iter().enumerate() {
        assert_eq!(
            scenario_case("chmod", 11 + offset)
                .expect("chmod parser boundary scenario")
                .argv,
            argv
        );
    }
}

// Chmod deterministic modes include chained symbolic, signed numeric, and long valid octal forms.
#[test]
fn chmod_scenarios_cover_extended_modes() {
    let modes: BTreeSet<String> = (24..=28)
        .map(|iteration| {
            scenario_case("chmod", iteration)
                .expect("chmod extended mode scenario")
                .argv[0]
                .clone()
        })
        .collect();

    assert_eq!(
        modes,
        BTreeSet::from([
            "+2000".to_string(),
            "-7022".to_string(),
            "00644".to_string(),
            "007777".to_string(),
            "u+r-w".to_string(),
        ])
    );
}

// Chmod deterministic operands preserve Unicode, quoting, tabs, empty names, and trailing slashes.
#[test]
fn chmod_scenarios_cover_boundary_operands() {
    let operands: Vec<String> = (29..=33)
        .map(|iteration| {
            scenario_case("chmod", iteration)
                .expect("chmod operand boundary scenario")
                .argv
                .last()
                .expect("chmod operand")
                .clone()
        })
        .collect();

    assert_eq!(operands, ["quote'file", "é", "tab\tfile", "", "tree/"]);
}

// Chmod deterministic references reach success, failure, recursion, no-follow, output, help, and version branches.
#[test]
fn chmod_scenarios_cover_reference_combinations() {
    let argv: Vec<Vec<String>> = (34..=39)
        .map(|iteration| {
            scenario_case("chmod", iteration)
                .expect("chmod reference combination scenario")
                .argv
        })
        .collect();

    assert!(argv
        .iter()
        .any(|args| args == &["--reference=tree/root-file", "tree/child/setuid"]));
    assert!(argv
        .iter()
        .any(|args| args == &["--reference=missing", "tree/root-file"]));
    assert!(argv.iter().any(|args| args.contains(&"-R".to_string())));
    assert!(argv.iter().any(|args| args.contains(&"-h".to_string())));
    assert!(argv.iter().any(|args| args.contains(&"-v".to_string())));
    assert!(argv
        .iter()
        .any(|args| args.contains(&"--version".to_string())));
}

// Source: coreutils/tests/chmod/inaccessible.sh; changing the parent first restores access to its child operand.
#[test]
fn chmod_scenario_covers_ordered_inaccessible_recovery() {
    let scenario = scenario_case("chmod", 40).expect("chmod inaccessible scenario");

    assert_eq!(scenario.argv, ["u+rwx", "d", "d/e"]);
    assert!(scenario
        .fixture
        .directories
        .iter()
        .any(|dir| dir.relative_path.as_path() == Path::new("d") && dir.mode == 0));
    assert!(scenario
        .fixture
        .directories
        .iter()
        .any(|dir| dir.relative_path.as_path() == Path::new("d/e") && dir.mode == 0));
}

// A modeled inaccessible lookup remains separate from the ordered recovery seed and keeps a valid later operand.
#[test]
fn chmod_scenario_covers_modeled_inaccessible_continuation() {
    let scenario = scenario_case("chmod", 41).expect("chmod inaccessible continuation scenario");

    assert_eq!(scenario.argv, ["600", "blocked/child", "tree/root-file"]);
    assert!(scenario
        .fixture
        .directories
        .iter()
        .any(|dir| dir.relative_path.as_path() == Path::new("blocked") && dir.mode == 0));
}

// New-utility scenario registration preserves representative seeded argument shapes.
#[test]
fn new_utility_scenarios_cover_seeded_shapes() {
    // Base64 decode with garbage-tolerant input is registered.
    let base64 = scenario_case("base64", 2).expect("base64 scenario");
    assert_eq!(
        base64.argv,
        vec!["--decode".to_string(), "--ignore-garbage".to_string()]
    );
    assert_eq!(base64.stdin, b"Y W!F\tu\n");

    let comm = scenario_case("comm", 1).expect("comm scenario");
    assert_eq!(
        comm.argv,
        vec![
            "-1".to_string(),
            "left.txt".to_string(),
            "right.txt".to_string()
        ]
    );

    // Comm zero-terminated total mode is registered with NUL-delimited fixture files.
    let comm_zero_total = scenario_case("comm", 8).expect("comm zero total scenario");
    assert_eq!(
        comm_zero_total.argv,
        vec![
            "--total".to_string(),
            "-z123".to_string(),
            "--output-delimiter=,".to_string(),
            "left0.txt".to_string(),
            "right0.txt".to_string()
        ]
    );

    // Comm stdin mode is registered with sorted stdin content.
    let comm_stdin = scenario_case("comm", 9).expect("comm stdin scenario");
    assert_eq!(
        comm_stdin.argv,
        vec!["-".to_string(), "right.txt".to_string()]
    );
    assert_eq!(comm_stdin.stdin, b"apple\nbanana\nbanana\norange\n");

    // Comm duplicate delimiter conflict is registered as an invalid option combination.
    let comm_delim_conflict = scenario_case("comm", 10).expect("comm delimiter scenario");
    assert_eq!(comm_delim_conflict.argv[0], "--output-delimiter=,");
    assert_eq!(comm_delim_conflict.argv[1], "--output-delimiter=+");

    let csplit = scenario_case("csplit", 1).expect("csplit scenario");
    assert_eq!(csplit.argv, vec!["-".to_string(), "3".to_string()]);
    assert!(!csplit.stdin.is_empty());

    let cut = scenario_case("cut", 2).expect("cut scenario");
    assert_eq!(cut.argv[0], "-b");
    assert!(cut.argv.iter().any(|arg| arg == "-"));

    // Complement mode on byte ranges is registered.
    let cut_complement = scenario_case("cut", 4).expect("cut complement scenario");
    assert_eq!(
        cut_complement.argv,
        vec![
            "--complement".to_string(),
            "-b".to_string(),
            "2-3".to_string()
        ]
    );
    assert_eq!(cut_complement.stdin, b"abcd\nxy\n");

    // Cut zero-terminated mode is registered with NUL-delimited stdin.
    let cut_zero = scenario_case("cut", 5).expect("cut zero-terminated scenario");
    assert_eq!(
        cut_zero.argv,
        vec!["-z".to_string(), "-c".to_string(), "1".to_string()]
    );
    assert_eq!(cut_zero.stdin, b"ab\0cd");

    // Cut output delimiter mode is registered with adjacent byte ranges.
    let cut_output_delimiter = scenario_case("cut", 6).expect("cut output delimiter scenario");
    assert_eq!(
        cut_output_delimiter.argv,
        vec![
            "-b".to_string(),
            "1-2,3-4".to_string(),
            "--output-delimiter=:".to_string()
        ]
    );

    // Cut no-split compatibility mode is registered as a no-op byte-mode case.
    let cut_no_split = scenario_case("cut", 9).expect("cut no-split scenario");
    assert_eq!(
        cut_no_split.argv,
        vec!["-n".to_string(), "-b".to_string(), "1,3".to_string()]
    );

    // Fold spaces mode is registered with the fixed wrapped stdin.
    let fold = scenario_case("fold", 2).expect("fold scenario");
    assert_eq!(
        fold.argv,
        vec!["-s".to_string(), "-w".to_string(), "8".to_string()]
    );
    assert_eq!(fold.stdin, b"aa bb ccdd\n");

    // Expand initial-only mode is registered with a leading tab input.
    let expand = scenario_case("expand", 0).expect("expand scenario");
    assert_eq!(expand.argv, vec!["--tabs=3".to_string(), "-i".to_string()]);
    assert_eq!(expand.stdin, b" \ta\tb\n");

    let ln = scenario_case("ln", 0).expect("ln scenario");
    assert_eq!(
        ln.argv,
        vec!["-s".to_string(), "a.txt".to_string(), "a.sym".to_string()]
    );

    // Head zero-terminated mode is registered.
    let head = scenario_case("head", 6).expect("head zero-terminated scenario");
    assert_eq!(
        head.argv,
        vec!["-z".to_string(), "-n".to_string(), "2".to_string()]
    );
    assert_eq!(head.stdin, b"a\0b\0c\0");

    // Head legacy byte-count syntax is registered.
    let head_legacy = scenario_case("head", 8).expect("head legacy byte scenario");
    assert_eq!(
        head_legacy.argv,
        vec!["-1c".to_string(), "payload.bin".to_string()]
    );

    // Head multiplier suffix syntax is registered.
    let head_multiplier = scenario_case("head", 11).expect("head multiplier scenario");
    assert_eq!(
        head_multiplier.argv,
        vec!["--bytes=1kB".to_string(), "payload.bin".to_string()]
    );

    // Head legacy verbose mode covers file and stdin header interactions.
    let head_headers = scenario_case("head", 13).expect("head legacy header scenario");
    assert_eq!(
        head_headers.argv,
        vec![
            "-1v".to_string(),
            "a.txt".to_string(),
            "-".to_string(),
            "b.txt".to_string()
        ]
    );
    assert_eq!(head_headers.stdin, b"stdin\n");

    // Tac literal-separator mode is registered.
    let tac = scenario_case("tac", 5).expect("tac separator scenario");
    assert_eq!(
        tac.argv,
        vec!["-b".to_string(), "-s".to_string(), "--".to_string()]
    );
    assert_eq!(tac.stdin, b"a---b");

    // Tail zero-terminated mode is registered.
    let tail = scenario_case("tail", 0).expect("tail zero-terminated scenario");
    assert_eq!(
        tail.argv,
        vec!["-z".to_string(), "-n".to_string(), "2".to_string()]
    );
    assert_eq!(tail.stdin, b"a\0b\0c\0");

    // Paste zero-terminated mode is registered with stdin and empty records.
    let paste = scenario_case("paste", 5).expect("paste zero-terminated scenario");
    assert_eq!(
        paste.argv,
        vec!["-z".to_string(), "-s".to_string(), "-".to_string()]
    );
    assert_eq!(paste.stdin, b"a\0\0b");

    let paste_delim = scenario_case("paste", 6).expect("paste zero custom delimiter scenario");
    assert_eq!(
        paste_delim.argv,
        vec![
            "--zero-terminated".to_string(),
            "-d".to_string(),
            "|:".to_string(),
            "-".to_string(),
            "empty.txt".to_string()
        ]
    );
    assert_eq!(paste_delim.stdin, b"x\0\0y");

    // Tail legacy byte mode is registered.
    let tail_legacy = scenario_case("tail", 1).expect("tail legacy byte scenario");
    assert_eq!(tail_legacy.argv, vec!["+2c".to_string()]);
    assert_eq!(tail_legacy.stdin, b"abcd");

    assert!(scenario_case("uniq", 6).is_none());
}

// P0 utilities without prior seed coverage now register at least one deterministic scenario.
#[test]
fn p0_utility_scenarios_are_registered() {
    for util in [
        "basename", "dirname", "echo", "expr", "factor", "false", "logname", "printenv", "printf",
        "pwd", "seq", "tee", "tr", "true",
    ] {
        assert!(
            scenario_case(util, 0).is_some(),
            "{util} should have a P0 seed scenario"
        );
    }
}

// P0 scenarios keep utility-specific option and edge-case shapes in the seed queue.
#[test]
fn p0_utility_scenarios_cover_specialized_shapes() {
    let basename = scenario_case("basename", 3).expect("basename multi scenario");
    assert_eq!(
        basename.argv,
        vec![
            "-a".to_string(),
            "-s".to_string(),
            ".txt".to_string(),
            "-z".to_string(),
            "dir/file.txt".to_string(),
            "other.txt".to_string()
        ]
    );

    let printenv = scenario_case("printenv", 3).expect("printenv null scenario");
    assert_eq!(
        printenv.argv,
        vec!["-0".to_string(), "LC_ALL".to_string(), "LANG".to_string()]
    );

    let tee = scenario_case("tee", 2).expect("tee append scenario");
    assert_eq!(tee.argv, vec!["-a".to_string(), "target.txt".to_string()]);
    assert_eq!(tee.stdin, b"line 2\n");

    let tr = scenario_case("tr", 3).expect("tr delete squeeze scenario");
    assert_eq!(
        tr.argv,
        vec![
            "-d".to_string(),
            "-s".to_string(),
            "a".to_string(),
            "b".to_string()
        ]
    );
}

// P1 utilities register supplemental seeds beyond their original narrow coverage.
#[test]
fn p1_utility_scenarios_cover_supplemental_shapes() {
    let base64_wrap = scenario_case("base64", 3).expect("base64 wrap scenario");
    assert_eq!(base64_wrap.argv, vec!["--wrap=4".to_string()]);

    let fold_invalid = scenario_case("fold", 3).expect("fold invalid width scenario");
    assert_eq!(
        fold_invalid.argv,
        vec!["--width".to_string(), "-b".to_string()]
    );

    let touch_time = scenario_case("touch", 5).expect("touch time scenario");
    assert_eq!(
        touch_time.argv,
        vec!["--time=a".to_string(), "created.txt".to_string()]
    );

    let chmod_reference = scenario_case("chmod", 5).expect("chmod reference scenario");
    assert_eq!(
        chmod_reference.argv,
        vec![
            "--reference=a.txt".to_string(),
            "755".to_string(),
            "target.txt".to_string()
        ]
    );

    let wc_repeated_stdin = scenario_case("wc", 7).expect("wc repeated stdin scenario");
    assert_eq!(
        wc_repeated_stdin.argv,
        vec!["-".to_string(), "-".to_string()]
    );
}

// Mv no-copy seed keeps the same-filesystem rename-only option deterministic.
#[test]
fn mv_no_copy_scenario_is_registered() {
    let scenario = scenario_case("mv", 12).expect("mv no-copy scenario");

    assert_eq!(
        scenario.argv,
        vec![
            "--no-copy".to_string(),
            "a.txt".to_string(),
            "renamed-no-copy.txt".to_string()
        ]
    );
}

// Mv target-directory error seed exercises a file used where a directory is required.
#[test]
fn mv_not_directory_target_scenario_is_registered() {
    let scenario = scenario_case("mv", 15).expect("mv not-directory scenario");

    assert_eq!(
        scenario.argv,
        vec!["-t".to_string(), "a.txt".to_string(), "b.txt".to_string()]
    );
}

// Mv empty-directory replacement seed covers rename over an empty destination directory.
#[test]
fn mv_empty_directory_replacement_scenario_is_registered() {
    let scenario = scenario_case("mv", 17).expect("mv empty-directory replacement scenario");

    assert_eq!(
        scenario.argv,
        vec![
            "-T".to_string(),
            "srcdir".to_string(),
            "empty-dest".to_string()
        ]
    );
    assert!(scenario
        .fixture
        .directories
        .iter()
        .any(|dir| dir.relative_path.as_path() == PathBuf::from("empty-dest").as_path()));
}

// Mv self-child seed exercises the guard against moving a directory below itself.
#[test]
fn mv_self_child_directory_scenario_is_registered() {
    let scenario = scenario_case("mv", 19).expect("mv self-child scenario");

    assert_eq!(
        scenario.argv,
        vec!["srcdir".to_string(), "srcdir/child".to_string()]
    );
}

// Mv symlink-loop seed keeps ELOOP-style source diagnostics in the campaign.
#[test]
fn mv_symlink_loop_scenario_is_registered() {
    let scenario = scenario_case("mv", 20).expect("mv symlink-loop scenario");

    assert_eq!(
        scenario.argv,
        vec!["loop-a/file".to_string(), "loop-out".to_string()]
    );
    assert!(scenario
        .fixture
        .symlinks
        .iter()
        .any(|link| link.relative_path.as_path() == PathBuf::from("loop-a").as_path()));
}
