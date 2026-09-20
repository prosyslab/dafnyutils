use super::*;

#[test]
fn cli_parse_fuzz_required_and_defaults() {
    let cli = Cli::try_parse_from(["coreutils_fuzzer", "fuzz", "--util", "touch"]).expect("parse");
    let CliCommand::Fuzz(args) = cli.command else {
        panic!("expected fuzz command");
    };
    assert_eq!(args.common.util, "touch");
    assert_eq!(args.common.ref_bin, None);
    assert_eq!(args.common.ref_kind, ExecKind::Native);
    assert_eq!(args.dut_bin, None);
    assert_eq!(args.dut_kind, ExecKind::DotnetDll);
    assert_eq!(args.common.opts, None);
    assert_eq!(args.common.iterations, 100);
    assert_eq!(args.common.max_args, 8);
    assert_eq!(args.common.max_fs_entries, 12);
    assert_eq!(args.common.seed, None);
    assert_eq!(args.common.workdir_mode, WorkdirMode::PerIteration);
    assert_eq!(args.shrink_attempts, 250);
    assert_eq!(args.process_timeout_seconds, 10);
    assert!(!args.ignore_stderr);
}

#[test]
fn work_root_is_unique_to_fuzzer_process() {
    let work_root = work_root_for_util("touch");
    let file_name = work_root
        .file_name()
        .and_then(OsStr::to_str)
        .expect("work root has UTF-8 file name");

    assert_eq!(work_root.parent(), Some(Path::new("/tmp")));
    assert!(file_name.starts_with("touch-"));
    assert_eq!(file_name.len(), "touch-".len() + 16);
}

#[test]
fn cli_parse_fuzz_options_and_workdir_mode() {
    let cli = Cli::try_parse_from([
        "coreutils_fuzzer",
        "fuzz",
        "--util",
        "chmod",
        "--opts",
        "-R,-f -v",
        "--ref-bin",
        "_build/coreutils/src/chmod",
        "--ref-kind",
        "native",
        "--dut-bin",
        "_build/bench/chmod_bench.dll",
        "--dut-kind",
        "dotnet-dll",
        "--iterations",
        "25",
        "--seed",
        "42",
        "--max-args",
        "6",
        "--max-fs-entries",
        "9",
        "--workdir-mode",
        "shared",
        "--shrink-attempts",
        "17",
        "--process-timeout-seconds",
        "3",
        "--ignore-stderr",
    ])
    .expect("parse");
    let CliCommand::Fuzz(args) = cli.command else {
        panic!("expected fuzz command");
    };
    assert_eq!(args.common.util, "chmod");
    assert_eq!(
        args.common.ref_bin,
        Some(PathBuf::from("_build/coreutils/src/chmod"))
    );
    assert_eq!(args.common.ref_kind, ExecKind::Native);
    assert_eq!(
        args.dut_bin,
        Some(PathBuf::from("_build/bench/chmod_bench.dll"))
    );
    assert_eq!(args.dut_kind, ExecKind::DotnetDll);
    assert_eq!(args.common.opts.as_deref(), Some("-R,-f -v"));
    assert_eq!(args.common.iterations, 25);
    assert_eq!(args.common.seed, Some(42));
    assert_eq!(args.common.max_args, 6);
    assert_eq!(args.common.max_fs_entries, 9);
    assert_eq!(args.common.workdir_mode, WorkdirMode::Shared);
    assert_eq!(args.shrink_attempts, 17);
    assert_eq!(args.process_timeout_seconds, 3);
    assert!(args.ignore_stderr);
}

#[test]
fn fuzz_requires_dut_target() {
    let temp = tempfile::tempdir().expect("tempdir");
    let ref_bin = temp.path().join("ref.dll");
    let missing_dut = temp.path().join("missing.dll");
    fs::write(&ref_bin, b"dll").expect("write ref");

    let cli = Cli::try_parse_from([
        "coreutils_fuzzer",
        "fuzz",
        "--util",
        "touch",
        "--ref-kind",
        "dotnet-dll",
        "--ref-bin",
        ref_bin.to_str().expect("utf8 path"),
        "--dut-kind",
        "dotnet-dll",
        "--dut-bin",
        missing_dut.to_str().expect("utf8 path"),
    ])
    .expect("parse");
    let CliCommand::Fuzz(args) = cli.command else {
        panic!("expected fuzz command");
    };

    let err = resolve_fuzz_paths(&args).expect_err("missing dut should fail");
    assert!(err.contains("missing DUT binary override"));
}

#[test]
fn option_pool_parses_mixed_separators() {
    let pool = parse_option_pool(Some("-a,-m  -c, --date"));
    assert_eq!(pool, vec!["-a", "-m", "-c", "--date"]);
}

#[test]
fn generation_is_deterministic_for_same_seed() {
    let pool = vec!["-a".to_string(), "-m".to_string(), "-c".to_string()];
    let mut rng_a = StdRng::seed_from_u64(7);
    let mut rng_b = StdRng::seed_from_u64(7);
    let case_a = generate_case("touch", &pool, &mut rng_a, 7, 10);
    let case_b = generate_case("touch", &pool, &mut rng_b, 7, 10);
    assert_eq!(case_a, case_b);
}

// 최소 인자 예산에서도 touch 생성기는 선택지보다 필수 경로 자리를 먼저 예약한다.
#[test]
fn touch_generator_reserves_path_operand_at_minimum_budget() {
    let pool = vec!["-a".to_string(), "-m".to_string(), "-c".to_string()];
    let mut rng = StdRng::seed_from_u64(11);
    let case = generate_case("touch", &pool, &mut rng, 1, 8);
    assert!(case.argv.iter().any(|arg| !arg.starts_with('-')));
}

#[test]
fn generated_touch_fixture_paths_never_start_with_dash() {
    let pool: Vec<String> = Vec::new();
    for seed in 0..128 {
        let mut rng = StdRng::seed_from_u64(seed);
        let case = generate_case("touch", &pool, &mut rng, 6, 10);
        assert!(case.argv.iter().all(|arg| !arg.starts_with('-')));
    }
}

#[test]
fn compare_detects_match() {
    let a = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: b"ok".to_vec(),
        stderr: Vec::new(),
    };
    let b = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: b"ok".to_vec(),
        stderr: Vec::new(),
    };
    let argv: Vec<String> = Vec::new();
    assert_eq!(
        compare_results(
            "cat",
            &argv,
            &a,
            &b,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false
        ),
        CompareResult::Match
    );
}

#[test]
fn compare_detects_mismatch_fields() {
    let a = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: b"left".to_vec(),
        stderr: b"a".to_vec(),
    };
    let b = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: b"right".to_vec(),
        stderr: b"a".to_vec(),
    };
    assert_eq!(
        compare_results(
            "touch",
            &Vec::new(),
            &a,
            &b,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false
        ),
        CompareResult::Mismatch {
            process_outcome_diff: Some((observed_process_outcome(0), observed_process_outcome(1),)),
            stdout_diff: true,
            stderr_diff: false,
            fs_diff: Vec::new(),
        }
    );
}

#[test]
fn compare_help_output_uses_presence_only() {
    let a = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: b"long help".to_vec(),
        stderr: Vec::new(),
    };
    let b = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: b"short help".to_vec(),
        stderr: Vec::new(),
    };
    assert_eq!(
        compare_results(
            "touch",
            &["--help".to_string()],
            &a,
            &b,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false
        ),
        CompareResult::Match
    );
}

#[test]
fn compare_version_output_requires_matching_channels() {
    let a = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: b"touch (GNU coreutils) 9.4".to_vec(),
        stderr: Vec::new(),
    };
    let b = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: b"touch (Dafny port)".to_vec(),
        stderr: b"minor stderr banner".to_vec(),
    };
    assert_eq!(
        compare_results(
            "touch",
            &["foo".to_string(), "--version".to_string()],
            &a,
            &b,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false,
        ),
        CompareResult::Mismatch {
            process_outcome_diff: None,
            stdout_diff: false,
            stderr_diff: true,
            fs_diff: Vec::new(),
        }
    );
}

#[test]
fn compare_help_exit_mismatch_is_reported() {
    let a = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: b"help".to_vec(),
        stderr: Vec::new(),
    };
    let b = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: b"help".to_vec(),
        stderr: Vec::new(),
    };
    assert_eq!(
        compare_results(
            "touch",
            &["--help".to_string()],
            &a,
            &b,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false
        ),
        CompareResult::Mismatch {
            process_outcome_diff: Some((observed_process_outcome(1), observed_process_outcome(0),)),
            stdout_diff: false,
            stderr_diff: false,
            fs_diff: Vec::new(),
        }
    );
}

#[test]
fn compare_error_detection_reports_missing_stderr_text() {
    let reference = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: Vec::new(),
        stderr: b"/tmp/build/coreutils/src/basename: option '--suffix' requires an argument\nTry '/tmp/build/coreutils/src/basename --help' for more information.\n".to_vec(),
    };
    let dut = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: Vec::new(),
        stderr: Vec::new(),
    };

    assert_eq!(
        compare_results(
            "basename",
            &["input.txt".to_string()],
            &reference,
            &dut,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false,
        ),
        CompareResult::Mismatch {
            process_outcome_diff: None,
            stdout_diff: false,
            stderr_diff: true,
            fs_diff: Vec::new(),
        }
    );
}

// Different diagnostic prefixes and help hints are observable stderr bytes.
#[test]
fn compare_error_detection_reports_prefix_and_hint_differences() {
    let reference = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: Vec::new(),
        stderr: b"/tmp/build/coreutils/src/cat: invalid option -- 'z'\nTry '/tmp/build/coreutils/src/cat --help' for more information.\n".to_vec(),
    };
    let dut = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: Vec::new(),
        stderr: b"cat: invalid option -- 'z'\nTry 'cat --help' for more information.\n".to_vec(),
    };

    assert_eq!(
        compare_results(
            "cat",
            &["-l".to_string()],
            &reference,
            &dut,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false
        ),
        CompareResult::Mismatch {
            process_outcome_diff: None,
            stdout_diff: false,
            stderr_diff: true,
            fs_diff: Vec::new(),
        }
    );
}

#[test]
fn compare_error_detection_reports_meaningful_stderr_difference() {
    let reference = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: Vec::new(),
        stderr: b"/tmp/build/coreutils/src/cat: invalid option -- 'z'\n".to_vec(),
    };
    let dut = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: Vec::new(),
        stderr: b"cat: invalid option -- 'b'\n".to_vec(),
    };

    assert_eq!(
        compare_results(
            "cat",
            &["-l".to_string()],
            &reference,
            &dut,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false
        ),
        CompareResult::Mismatch {
            process_outcome_diff: None,
            stdout_diff: false,
            stderr_diff: true,
            fs_diff: Vec::new(),
        }
    );
}

#[test]
fn compare_can_ignore_stderr_differences() {
    let reference = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: Vec::new(),
        stderr: b"cat: 'a=rw': No such file or directory\n".to_vec(),
    };
    let dut = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: Vec::new(),
        stderr: b"cat: a=rw: No such file or directory\n".to_vec(),
    };

    assert_eq!(
        compare_results(
            "cat",
            &["a=rw".to_string()],
            &reference,
            &dut,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            true,
        ),
        CompareResult::Match
    );
}

#[test]
fn compare_ignoring_stderr_still_checks_exit_stdout_and_filesystem() {
    let reference = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: b"left".to_vec(),
        stderr: b"touch: left\n".to_vec(),
    };
    let dut = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: b"right".to_vec(),
        stderr: b"touch: right\n".to_vec(),
    };
    let mut ref_fs = FsSnapshot::new();
    ref_fs.insert(
        "a.txt".to_string(),
        fs_file_with_identity(b"left", "0644", 1),
    );
    let mut dut_fs = FsSnapshot::new();
    dut_fs.insert(
        "a.txt".to_string(),
        fs_file_with_identity(b"right", "0644", 2),
    );

    assert_eq!(
        compare_results(
            "touch",
            &["a.txt".to_string()],
            &reference,
            &dut,
            &ref_fs,
            &dut_fs,
            true,
        ),
        CompareResult::Mismatch {
            process_outcome_diff: Some((observed_process_outcome(1), observed_process_outcome(0),)),
            stdout_diff: true,
            stderr_diff: false,
            fs_diff: vec!["fs changed paths: a.txt".to_string()],
        }
    );
}

#[test]
fn compare_error_detection_still_checks_exit_and_filesystem() {
    let reference = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: Vec::new(),
        stderr:
            b"touch: invalid argument '-m' for '--time'\nTry 'touch --help' for more information.\n"
                .to_vec(),
    };
    let dut = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: Vec::new(),
        stderr: Vec::new(),
    };
    let mut ref_fs = FsSnapshot::new();
    ref_fs.insert(
        "a.txt".to_string(),
        FsNodeSnapshot {
            raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
            kind: "file".to_string(),
            mode_octal: "0644".to_string(),
            times: FsTimes::default(),
            uid: None,
            gid: None,
            logical_size: None,
            allocated_512_blocks: None,
            preferred_io_block_bytes: None,
            target: String::new(),
            data: b"left".to_vec(),
            host_key: Some(HostInodeKeySnapshot {
                device: 1,
                inode: 1,
            }),
            link_count: None,
        },
    );
    let mut dut_fs = FsSnapshot::new();
    dut_fs.insert(
        "a.txt".to_string(),
        FsNodeSnapshot {
            raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
            kind: "file".to_string(),
            mode_octal: "0644".to_string(),
            times: FsTimes::default(),
            uid: None,
            gid: None,
            logical_size: None,
            allocated_512_blocks: None,
            preferred_io_block_bytes: None,
            target: String::new(),
            data: b"right".to_vec(),
            host_key: Some(HostInodeKeySnapshot {
                device: 2,
                inode: 2,
            }),
            link_count: None,
        },
    );
    assert_eq!(
        compare_results(
            "touch",
            &["-m".to_string()],
            &reference,
            &dut,
            &ref_fs,
            &dut_fs,
            false
        ),
        CompareResult::Mismatch {
            process_outcome_diff: Some((observed_process_outcome(1), observed_process_outcome(0),)),
            stdout_diff: false,
            stderr_diff: true,
            fs_diff: vec!["fs changed paths: a.txt".to_string()],
        }
    );
}

#[test]
fn compare_error_detection_requires_nonzero_exit() {
    let reference = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: Vec::new(),
        stderr: b"touch: invalid argument '-m' for '--time'\nValid arguments are:\n  - 'atime', 'access', 'use'\n  - 'mtime', 'modify'\nTry 'touch --help' for more information.\n".to_vec(),
    };
    let dut = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: Vec::new(),
        stderr: Vec::new(),
    };

    assert_eq!(
        compare_results(
            "touch",
            &["--time".to_string(), "-m".to_string(), "file".to_string()],
            &reference,
            &dut,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false,
        ),
        CompareResult::Mismatch {
            process_outcome_diff: Some((observed_process_outcome(1), observed_process_outcome(0),)),
            stdout_diff: false,
            stderr_diff: true,
            fs_diff: Vec::new(),
        }
    );
}

// Touch relies on its typed public snapshot proof rather than raw per-execution traces.
#[test]
fn time_coverage_does_not_require_touch_raw_trace() {
    let run = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: Vec::new(),
        stderr: Vec::new(),
    };
    let mut ref_fs = FsSnapshot::new();
    ref_fs.insert(
        "a.txt".to_string(),
        fs_file_with_identity(b"same", "0644", 1),
    );
    let mut dut_file = fs_file_with_identity(b"same", "0644", 2);
    dut_file.times.mtime_sec = 10;
    let mut dut_fs = FsSnapshot::new();
    dut_fs.insert("a.txt".to_string(), dut_file);

    assert_eq!(
        compare_results("touch", &[], &run, &run, &ref_fs, &dut_fs, false),
        CompareResult::Match
    );
    let comparison = crate::fuzz::time_coverage::EvaluatedComparison::without_time_observations(
        compare_results("touch", &[], &run, &run, &ref_fs, &dut_fs, false),
        crate::utils::capabilities::require_fuzz_capability("touch")
            .unwrap()
            .time_coverage,
    );
    assert_eq!(
        comparison.verdict(),
        crate::fuzz::time_coverage::CaseVerdict::Match
    );
}

#[test]
fn extract_used_options_is_unique_and_sorted() {
    let pool = BTreeSet::from(["-a".to_string(), "-m".to_string(), "-c".to_string()]);
    let argv = vec![
        "-m".to_string(),
        "input0.txt".to_string(),
        "-a".to_string(),
        "-m".to_string(),
        "--other".to_string(),
    ];
    let used = extract_used_options(&argv, &pool);
    assert_eq!(used, vec!["-a".to_string(), "-m".to_string()]);
}

#[test]
fn extract_used_options_matches_long_options_with_attached_values() {
    let pool = BTreeSet::from([
        "--backup".to_string(),
        "--suffix".to_string(),
        "--update".to_string(),
    ]);
    let argv = vec![
        "--backup=numbered".to_string(),
        "--suffix=.bak".to_string(),
        "--update=none".to_string(),
        "a.txt".to_string(),
    ];

    let used = extract_used_options(&argv, &pool);

    assert_eq!(
        used,
        vec![
            "--backup".to_string(),
            "--suffix".to_string(),
            "--update".to_string()
        ]
    );
}

#[test]
fn option_coverage_tracks_single_and_pair_hits() {
    let pool = vec!["-a".to_string(), "-m".to_string(), "-c".to_string()];
    let mut cov = OptionCoverage::new(&pool);
    cov.observe_case(&["-a".to_string(), "-m".to_string(), "input0.txt".to_string()]);
    cov.observe_case(&["-c".to_string(), "dir0".to_string()]);

    assert_eq!(
        cov.render_report(),
        "Option coverage: singles 3/3 (100.0%), pairs 1/3 (33.3%)"
    );
}

fn fs_file(data: &[u8], mode: &str) -> FsNodeSnapshot {
    FsNodeSnapshot {
        raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
        kind: "file".to_string(),
        mode_octal: mode.to_string(),
        times: FsTimes::default(),
        uid: None,
        gid: None,
        logical_size: None,
        allocated_512_blocks: None,
        preferred_io_block_bytes: None,
        target: String::new(),
        data: data.to_vec(),
        host_key: None,
        link_count: None,
    }
}

fn fs_file_with_identity(data: &[u8], mode: &str, inode: u64) -> FsNodeSnapshot {
    let mut node = fs_file(data, mode);
    node.host_key = Some(HostInodeKeySnapshot { device: 1, inode });
    node
}

fn fs_dir() -> FsNodeSnapshot {
    FsNodeSnapshot {
        raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
        kind: "dir".to_string(),
        mode_octal: "0755".to_string(),
        times: FsTimes::default(),
        uid: None,
        gid: None,
        logical_size: None,
        allocated_512_blocks: None,
        preferred_io_block_bytes: None,
        target: String::new(),
        data: Vec::new(),
        host_key: None,
        link_count: None,
    }
}

fn fs_metadata_node() -> FsNodeSnapshot {
    FsNodeSnapshot {
        raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
        kind: "file".to_string(),
        mode_octal: "0644".to_string(),
        times: FsTimes::default(),
        uid: Some(1000),
        gid: Some(1000),
        logical_size: Some(7),
        allocated_512_blocks: Some(8),
        preferred_io_block_bytes: Some(4096),
        target: String::new(),
        data: b"payload".to_vec(),
        host_key: Some(HostInodeKeySnapshot {
            device: 1,
            inode: 1,
        }),
        link_count: Some(1),
    }
}

fn compare_single_fs_nodes(reference: FsNodeSnapshot, dut: FsNodeSnapshot) -> CompareResult {
    let result = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: Vec::new(),
        stderr: Vec::new(),
    };
    compare_results(
        "cat",
        &[],
        &result,
        &result,
        &BTreeMap::from([("file".to_string(), reference)]),
        &BTreeMap::from([("file".to_string(), dut)]),
        false,
    )
}

// Distinct Unix owners on otherwise identical files are a filesystem mismatch.
#[test]
fn compare_detects_inode_ownership_difference() {
    let reference = fs_metadata_node();
    let mut dut = reference.clone();
    dut.uid = Some(2000);
    dut.gid = Some(3000);

    assert!(matches!(
        compare_single_fs_nodes(reference, dut),
        CompareResult::Mismatch { .. }
    ));
}

// Distinct logical sizes on otherwise identical observations are a filesystem mismatch.
#[test]
fn compare_detects_inode_logical_size_difference() {
    let reference = fs_metadata_node();
    let mut dut = reference.clone();
    dut.logical_size = Some(4096);

    assert!(matches!(
        compare_single_fs_nodes(reference, dut),
        CompareResult::Mismatch { .. }
    ));
}

// Distinct allocated block counts on otherwise identical files are a filesystem mismatch.
#[test]
fn compare_detects_inode_allocated_blocks_difference() {
    let reference = fs_metadata_node();
    let mut dut = reference.clone();
    dut.allocated_512_blocks = Some(16);

    assert!(matches!(
        compare_single_fs_nodes(reference, dut),
        CompareResult::Mismatch { .. }
    ));
}

// Distinct preferred IO block sizes on otherwise identical files are a filesystem mismatch.
#[test]
fn compare_detects_inode_preferred_io_block_size_difference() {
    let reference = fs_metadata_node();
    let mut dut = reference.clone();
    dut.preferred_io_block_bytes = Some(8192);

    assert!(matches!(
        compare_single_fs_nodes(reference, dut),
        CompareResult::Mismatch { .. }
    ));
}

#[test]
fn semantic_coverage_tracks_behavior_buckets() {
    let case = GeneratedCase {
        argv: vec!["a.txt".to_string(), "missing.txt".to_string()],
        fixture: FixtureBlueprint {
            directories: Vec::new(),
            files: vec![FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha".to_vec(),
                mode: 0o644,
            }],
            symlinks: Vec::new(),
            hardlinks: Vec::new(),
        },
        stdin: Vec::new(),
        cwd: PathBuf::from("."),
    };
    let result = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(1),
        stdout: b"alpha".to_vec(),
        stderr: b"cat: missing.txt: No such file or directory\n".to_vec(),
    };
    let mut fs = FsSnapshot::new();
    fs.insert(".".to_string(), fs_dir());
    fs.insert("a.txt".to_string(), fs_file(b"alpha", "0644"));

    let buckets = classify_case("cat", &case, &result, &fs, &fs);

    assert!(buckets.contains("operand:existing-file"));
    assert!(buckets.contains("operand:missing-path"));
    assert!(buckets.contains("exit:error"));
    assert!(buckets.contains("stream:stdout-nonempty"));
    assert!(buckets.contains("stream:stderr-nonempty"));
    assert!(buckets.contains("fs:unchanged"));
}

#[test]
fn semantic_operand_classification_skips_mv_suffix_values() {
    let case = GeneratedCase {
        argv: vec![
            "-b".to_string(),
            "-S".to_string(),
            ".bak".to_string(),
            "a.txt".to_string(),
            "target.txt".to_string(),
        ],
        fixture: FixtureBlueprint {
            directories: Vec::new(),
            files: vec![
                FileSpec {
                    relative_path: PathBuf::from("a.txt"),
                    bytes: b"alpha".to_vec(),
                    mode: 0o644,
                },
                FileSpec {
                    relative_path: PathBuf::from("target.txt"),
                    bytes: b"target".to_vec(),
                    mode: 0o644,
                },
            ],
            symlinks: Vec::new(),
            hardlinks: Vec::new(),
        },
        stdin: Vec::new(),
        cwd: PathBuf::from("."),
    };
    let result = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: Vec::new(),
        stderr: Vec::new(),
    };
    let mut fs = FsSnapshot::new();
    fs.insert(".".to_string(), fs_dir());
    fs.insert("a.txt".to_string(), fs_file(b"alpha", "0644"));
    fs.insert("target.txt".to_string(), fs_file(b"target", "0644"));

    let buckets = classify_case("mv", &case, &result, &fs, &fs);

    assert!(buckets.contains("operand:existing-file"));
    assert!(!buckets.contains("operand:missing-path"));
}

#[test]
fn semantic_coverage_reports_new_bucket_discovery() {
    let case = GeneratedCase {
        argv: vec!["-".to_string()],
        fixture: FixtureBlueprint {
            directories: Vec::new(),
            files: Vec::new(),
            symlinks: Vec::new(),
            hardlinks: Vec::new(),
        },
        stdin: b"stdin".to_vec(),
        cwd: PathBuf::from("."),
    };
    let result = RunResult {
        termination: crate::fuzz::process_outcome::Termination::test_exit(0),
        stdout: b"stdin".to_vec(),
        stderr: Vec::new(),
    };
    let fs = FsSnapshot::new();
    let mut coverage = SemanticCoverage::default();

    assert!(coverage.observe_case("cat", &case, &result, &fs, &fs));
    assert!(!coverage.observe_case("cat", &case, &result, &fs, &fs));
    assert!(coverage.render_report().contains("buckets"));
}

#[test]
fn interesting_corpus_keeps_only_interesting_cases_and_caps_size() {
    let case = GeneratedCase {
        argv: vec!["a.txt".to_string()],
        fixture: FixtureBlueprint {
            directories: Vec::new(),
            files: Vec::new(),
            symlinks: Vec::new(),
            hardlinks: Vec::new(),
        },
        stdin: Vec::new(),
        cwd: PathBuf::from("."),
    };
    let mut corpus = InterestingCorpus::new(2);
    corpus.maybe_add(&case, false);
    let mut rng = StdRng::seed_from_u64(1);
    assert!(corpus.choose(&mut rng).is_none());
    corpus.maybe_add(&case, true);
    corpus.maybe_add(&case, true);
    corpus.maybe_add(&case, true);
    assert!(corpus.choose(&mut rng).is_some());
}

#[test]
fn scenario_cases_cover_seeded_utility_behaviors() {
    let cat = scenario_case("cat", 2).expect("cat scenario");
    assert_eq!(cat.argv, vec!["-".to_string(), "a.txt".to_string()]);
    assert!(!cat.stdin.is_empty());

    let touch = scenario_case("touch", 2).expect("touch scenario");
    assert_eq!(
        touch.argv,
        vec![
            "-r".to_string(),
            "a.txt".to_string(),
            "target.txt".to_string()
        ]
    );

    let mv = scenario_case("mv", 6).expect("mv scenario");
    assert_eq!(
        mv.argv,
        vec![
            "--backup=numbered".to_string(),
            "-v".to_string(),
            "a.txt".to_string(),
            "target.txt".to_string()
        ]
    );

    assert!(scenario_case("unknown", 0).is_none());
}

// Differential targets share the locale, time zone, terminal, and file-name quoting assumptions.
#[test]
fn deterministic_env_forces_modeled_process_context() {
    let mut cmd = Command::new("sh");
    super::apply_deterministic_env(&mut cmd);

    let environment: BTreeMap<String, String> = cmd
        .get_envs()
        .filter_map(|(key, value)| {
            value.map(|value| {
                (
                    key.to_string_lossy().to_string(),
                    value.to_string_lossy().to_string(),
                )
            })
        })
        .collect();

    assert_eq!(environment.get("LC_ALL").map(String::as_str), Some("C"));
    assert_eq!(environment.get("LANG").map(String::as_str), Some("C"));
    assert_eq!(environment.get("TZ").map(String::as_str), Some("UTC0"));
    assert_eq!(environment.get("TERM").map(String::as_str), Some("dumb"));
    assert_eq!(
        environment.get("QUOTING_STYLE").map(String::as_str),
        Some("literal")
    );
}

// Ambient settings, including secrets and utility-specific knobs, are not inherited.
#[test]
fn deterministic_env_removes_inherited_utility_settings() {
    let mut cmd = Command::new("sh");
    super::apply_deterministic_env(&mut cmd);

    let inherited: BTreeSet<String> = cmd
        .get_envs()
        .filter_map(|(key, value)| value.map(|_| key.to_string_lossy().to_string()))
        .collect();

    assert_eq!(
        inherited,
        BTreeSet::from([
            "LANG".to_string(),
            "LC_ALL".to_string(),
            "PATH".to_string(),
            "QUOTING_STYLE".to_string(),
            "TERM".to_string(),
            "TZ".to_string(),
        ])
    );
}

#[test]
#[cfg(unix)]
fn run_variant_captures_stdout_and_stderr() {
    let temp = tempfile::tempdir().expect("tempdir");
    let script = temp.path().join("emit.sh");
    fs::write(
        &script,
        "#!/usr/bin/env sh\nprintf 'out:%s\\n' \"$1\"\nprintf 'err:%s\\n' \"$1\" >&2\nexit 7\n",
    )
    .expect("write script");

    let paths = ResolvedPaths {
        reference: ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "reference",
        },
        dut: ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "dut",
        },
    };
    let argv = vec![
        script.to_str().expect("UTF-8 temp path").to_string(),
        "token".to_string(),
    ];

    let result = run_variant(
        VariantKind::Ref,
        &paths,
        &argv,
        &[],
        Path::new("."),
        temp.path(),
        0o022,
        None,
        Duration::from_secs(1),
    )
    .expect("run variant");

    assert_eq!(result.termination.exit_code(), Some(7));
    assert_eq!(result.stdout, b"out:token\n".to_vec());
    assert_eq!(result.stderr, b"err:token\n".to_vec());
}

#[test]
#[cfg(unix)]
fn run_variant_treats_broken_stdin_pipe_as_process_output() {
    let temp = tempfile::tempdir().expect("tempdir");
    let script = temp.path().join("close-stdin.sh");
    fs::write(
        &script,
        "#!/usr/bin/env sh\nexec 0<&-\nprintf 'closed\\n'\nsleep 0.1\n",
    )
    .expect("write script");

    let paths = ResolvedPaths {
        reference: ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "reference",
        },
        dut: ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "dut",
        },
    };
    let argv = vec![script.to_str().expect("UTF-8 temp path").to_string()];

    let stdin = vec![b'x'; 1024 * 1024];
    let result = run_variant(
        VariantKind::Ref,
        &paths,
        &argv,
        &stdin,
        Path::new("."),
        temp.path(),
        0o022,
        None,
        Duration::from_secs(1),
    )
    .expect("broken stdin pipe should not hide process output");

    assert_eq!(result.termination.exit_code(), Some(0));
    assert_eq!(result.stdout, b"closed\n".to_vec());
}

#[test]
#[cfg(unix)]
fn evaluate_case_suppresses_stdin_when_argv_does_not_consume_it() {
    let temp = tempfile::tempdir().expect("tempdir");
    let script = temp.path().join("count-stdin.sh");
    fs::write(
        &script,
        "#!/usr/bin/env sh\nbytes=$(cat | wc -c | tr -d '[:space:]')\nprintf '%s\\n' \"$bytes\"\n",
    )
    .expect("write script");

    let cli = Cli::try_parse_from([
        "coreutils_fuzzer",
        "fuzz",
        "--util",
        "cat",
        "--process-timeout-seconds",
        "1",
    ])
    .expect("parse");
    let CliCommand::Fuzz(args) = cli.command else {
        panic!("expected fuzz command");
    };
    let paths = ResolvedPaths {
        reference: ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "reference",
        },
        dut: ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "dut",
        },
    };
    let case = GeneratedCase {
        argv: vec![
            script.to_str().expect("UTF-8 temp path").to_string(),
            "input.txt".to_string(),
        ],
        fixture: FixtureBlueprint {
            directories: Vec::new(),
            files: vec![FileSpec {
                relative_path: PathBuf::from("input.txt"),
                bytes: b"file\n".to_vec(),
                mode: 0o644,
            }],
            symlinks: Vec::new(),
            hardlinks: Vec::new(),
        },
        stdin: b"provided stdin\n".to_vec(),
        cwd: PathBuf::from("."),
    };

    let evaluation = evaluate_case(&args, &paths, temp.path(), None, 0, &case).expect("evaluate");

    assert_eq!(evaluation.reference.stdout, b"0\n".to_vec());
    assert_eq!(evaluation.dut.stdout, b"0\n".to_vec());
    assert_eq!(evaluation.comparison.observable, CompareResult::Match);
    assert_eq!(
        evaluation.comparison.verdict(),
        crate::fuzz::time_coverage::CaseVerdict::Match
    );
}

#[test]
#[cfg(unix)]
fn run_variant_times_out_hung_process() {
    let temp = tempfile::tempdir().expect("tempdir");
    let script = temp.path().join("hang.sh");
    fs::write(&script, "#!/usr/bin/env sh\nexec sleep 5\n").expect("write script");

    let paths = ResolvedPaths {
        reference: ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "reference",
        },
        dut: ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "dut",
        },
    };
    let argv = vec![script.to_str().expect("UTF-8 temp path").to_string()];

    let err = run_variant(
        VariantKind::Ref,
        &paths,
        &argv,
        &[],
        Path::new("."),
        temp.path(),
        0o022,
        None,
        Duration::from_millis(50),
    )
    .expect_err("hung variant should time out");

    assert!(err.contains("reference variant"));
    assert!(err.contains("timed out"));
}

#[test]
fn render_text_diff_marks_line_replacement() {
    let diff = render_text_diff("stdout", b"line1\nline2\n", b"line1\nlineX\n");
    assert!(diff.contains("--- ref/stdout (12 bytes)"));
    assert!(diff.contains("+++ dut/stdout (12 bytes)"));
    assert!(diff.contains(" line1"));
    assert!(diff.contains("-line2"));
    assert!(diff.contains("+lineX"));
}

#[test]
fn render_text_diff_handles_empty_vs_non_empty() {
    let diff = render_text_diff("stderr", b"", b"oops");
    assert!(diff.contains("--- ref/stderr (0 bytes)"));
    assert!(diff.contains("+++ dut/stderr (4 bytes)"));
    assert!(diff.contains("-<empty>"));
    assert!(diff.contains("+oops"));
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EntrySnapshot {
    is_dir: bool,
    is_symlink: bool,
    link_target: Option<PathBuf>,
    mode: u32,
    atime_sec: i64,
    atime_nsec: i64,
    mtime_sec: i64,
    mtime_nsec: i64,
    bytes: Vec<u8>,
}

#[cfg(unix)]
fn snapshot_tree(root: &Path) -> std::collections::BTreeMap<PathBuf, EntrySnapshot> {
    fn walk(
        root: &Path,
        current: &Path,
        out: &mut std::collections::BTreeMap<PathBuf, EntrySnapshot>,
    ) {
        let initial_metadata = fs::symlink_metadata(current).expect("metadata");
        let rel = current.strip_prefix(root).expect("relative").to_path_buf();
        let file_type = initial_metadata.file_type();
        let is_dir = file_type.is_dir();
        let is_symlink = file_type.is_symlink();
        let link_target = if is_symlink {
            Some(fs::read_link(current).expect("read symlink target"))
        } else {
            None
        };
        let bytes = if is_dir || is_symlink {
            Vec::new()
        } else {
            fs::read(current).expect("read file")
        };
        if is_dir {
            let mut children: Vec<PathBuf> = fs::read_dir(current)
                .expect("read dir")
                .map(|entry| entry.expect("dir entry").path())
                .collect();
            children.sort();
            for child in children {
                walk(root, &child, out);
            }
        }
        restore_path_times(current, times_from_metadata(&initial_metadata), is_symlink)
            .expect("restore observer-updated timestamps");
        let metadata = fs::symlink_metadata(current).expect("metadata after observation");
        out.insert(
            rel,
            EntrySnapshot {
                is_dir,
                is_symlink,
                link_target,
                mode: metadata.permissions().mode(),
                atime_sec: metadata.atime(),
                atime_nsec: metadata.atime_nsec(),
                mtime_sec: metadata.mtime(),
                mtime_nsec: metadata.mtime_nsec(),
                bytes,
            },
        );
    }

    let mut result = std::collections::BTreeMap::new();
    walk(root, root, &mut result);
    result
}

// Twin differential fixtures must begin with identical contents, modes, and observable times.
#[test]
#[cfg(unix)]
fn prepare_iteration_dirs_starts_from_identical_snapshots() {
    let temp = tempfile::tempdir().expect("tempdir");
    let fixture = FixtureBlueprint {
        directories: vec![
            DirSpec {
                relative_path: PathBuf::from("alpha"),
                mode: 0o755,
            },
            DirSpec {
                relative_path: PathBuf::from("alpha/nested"),
                mode: 0o700,
            },
        ],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("alpha/nested/a.txt"),
                bytes: b"hello".to_vec(),
                mode: 0o640,
            },
            FileSpec {
                relative_path: PathBuf::from("b.bin"),
                bytes: vec![0, 1, 2, 3, 4],
                mode: 0o444,
            },
        ],
        symlinks: vec![SymlinkSpec {
            relative_path: PathBuf::from("alpha/link-to-root"),
            target: PathBuf::from("../b.bin"),
        }],
        hardlinks: Vec::new(),
    };

    let (ref_dir, dut_dir) =
        prepare_iteration_dirs(temp.path(), None, 0, &fixture, false).expect("prepare dirs");
    let ref_snapshot = snapshot_tree(&ref_dir);
    let dut_snapshot = snapshot_tree(&dut_dir);
    assert_eq!(ref_snapshot, dut_snapshot);
}

#[test]
#[cfg(unix)]
fn ref_side_effect_does_not_change_dut_state() {
    let temp = tempfile::tempdir().expect("tempdir");
    let fixture = FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("x"),
            mode: 0o755,
        }],
        files: vec![FileSpec {
            relative_path: PathBuf::from("x/file.txt"),
            bytes: b"seed".to_vec(),
            mode: 0o600,
        }],
        symlinks: vec![],
        hardlinks: Vec::new(),
    };

    let (ref_dir, dut_dir) =
        prepare_iteration_dirs(temp.path(), None, 1, &fixture, false).expect("prepare dirs");
    let before_dut = snapshot_tree(&dut_dir);

    fs::write(ref_dir.join("x/file.txt"), b"mutated").expect("mutate ref");
    fs::create_dir_all(ref_dir.join("newdir")).expect("new dir");
    fs::write(ref_dir.join("newdir/new.txt"), b"new").expect("new file");

    let after_dut = snapshot_tree(&dut_dir);
    assert_eq!(before_dut, after_dut);
}

#[test]
#[cfg(unix)]
fn reset_dir_recovers_from_permission_denied_tree() {
    use std::os::unix::fs::PermissionsExt;

    let temp = tempfile::tempdir().expect("tempdir");
    let target = temp.path().join("locked");
    fs::create_dir_all(target.join("nested")).expect("create nested");
    fs::write(target.join("nested/file.txt"), b"x").expect("write file");

    fs::set_permissions(
        target.join("nested/file.txt"),
        fs::Permissions::from_mode(0o000),
    )
    .expect("chmod file");
    fs::set_permissions(target.join("nested"), fs::Permissions::from_mode(0o000))
        .expect("chmod nested dir");
    fs::set_permissions(&target, fs::Permissions::from_mode(0o000)).expect("chmod target dir");

    reset_dir(&target).expect("reset dir should recover from permissions");

    let entries: Vec<_> = fs::read_dir(&target)
        .expect("read reset target")
        .collect::<Result<Vec<_>, _>>()
        .expect("collect entries");
    assert!(entries.is_empty());
}

// Character devices are rejected instead of being coerced to empty regular files.
#[test]
#[cfg(unix)]
fn snapshot_fs_rejects_character_device() {
    let error =
        snapshot_fs(Path::new("/dev/null")).expect_err("character-device observation must fail");

    assert!(error.contains("unsupported filesystem node"));
    assert!(error.contains("/dev/null"));
}

// Repeated reads preserve the modeled tree after excluding observer-induced ctime advancement.
#[test]
#[cfg(unix)]
fn snapshot_fs_is_stable_after_its_own_reads() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path().join("fixture");
    fs::create_dir_all(root.join("nested")).expect("create nested directory");
    fs::write(root.join("nested/file.txt"), b"payload").expect("write file");
    std::os::unix::fs::symlink("nested/file.txt", root.join("link")).expect("create symlink");

    let mut first = snapshot_fs(&root).expect("first snapshot");
    let mut second = snapshot_fs(&root).expect("second snapshot");

    for node in first.values_mut().chain(second.values_mut()) {
        node.times.ctime_sec = 0;
        node.times.ctime_nsec = 0;
    }

    assert_eq!(first, second);
}

#[test]
#[cfg(unix)]
fn materialize_fixture_applies_modes_and_symlink_targets() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path().join("fixture");
    fs::create_dir_all(&root).expect("create root");

    let fixture = FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("secure"),
            mode: 0o700,
        }],
        files: vec![FileSpec {
            relative_path: PathBuf::from("secure/target.txt"),
            bytes: b"payload".to_vec(),
            mode: 0o400,
        }],
        symlinks: vec![SymlinkSpec {
            relative_path: PathBuf::from("secure/link.txt"),
            target: PathBuf::from("target.txt"),
        }],
        hardlinks: Vec::new(),
    };

    materialize_fixture(&root, &fixture).expect("materialize fixture");

    let dir_meta = fs::symlink_metadata(root.join("secure")).expect("secure metadata");
    assert_eq!(dir_meta.permissions().mode() & 0o7777, 0o700);

    let file_meta = fs::symlink_metadata(root.join("secure/target.txt")).expect("file metadata");
    assert_eq!(file_meta.permissions().mode() & 0o7777, 0o400);

    let symlink_path = root.join("secure/link.txt");
    let symlink_meta = fs::symlink_metadata(&symlink_path).expect("symlink metadata");
    assert!(symlink_meta.file_type().is_symlink());
    assert_eq!(
        fs::read_link(symlink_path).expect("read link"),
        PathBuf::from("target.txt")
    );
}

// Materialization must make the alias name refer to the exact regular-file inode.
#[test]
#[cfg(unix)]
fn materialize_fixture_creates_regular_file_hardlink() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path().join("fixture");
    let fixture = FixtureBlueprint {
        directories: Vec::new(),
        files: vec![FileSpec {
            relative_path: PathBuf::from("source"),
            bytes: b"payload".to_vec(),
            mode: 0o644,
        }],
        symlinks: Vec::new(),
        hardlinks: vec![HardlinkSpec {
            relative_path: PathBuf::from("alias"),
            source_relative_path: PathBuf::from("source"),
        }],
    };

    materialize_fixture(&root, &fixture).expect("materialize fixture");

    let source = fs::symlink_metadata(root.join("source")).expect("source metadata");
    let alias = fs::symlink_metadata(root.join("alias")).expect("alias metadata");
    assert_eq!((source.dev(), source.ino()), (alias.dev(), alias.ino()));
}

// A hard-link destination below a fixture symlink must not create an alias outside the root.
#[test]
#[cfg(unix)]
fn materialize_fixture_rejects_hardlink_destination_below_symlink() {
    let temp = tempfile::tempdir().expect("tempdir");
    let outside = temp.path().join("outside");
    fs::create_dir(&outside).expect("create outside directory");
    let root = temp.path().join("fixture");
    let fixture = FixtureBlueprint {
        directories: Vec::new(),
        files: vec![FileSpec {
            relative_path: PathBuf::from("source"),
            bytes: b"payload".to_vec(),
            mode: 0o644,
        }],
        symlinks: vec![SymlinkSpec {
            relative_path: PathBuf::from("escape"),
            target: outside.clone(),
        }],
        hardlinks: vec![HardlinkSpec {
            relative_path: PathBuf::from("escape/alias"),
            source_relative_path: PathBuf::from("source"),
        }],
    };

    assert!(materialize_fixture(&root, &fixture).is_err());
    assert!(!outside.join("alias").exists());
}

// A non-normalized symlink path must be rejected before fixture materialization.
#[test]
#[cfg(unix)]
fn materialize_fixture_rejects_non_normalized_symlink_path() {
    let temp = tempfile::tempdir().expect("tempdir");
    let fixture = FixtureBlueprint {
        directories: Vec::new(),
        files: Vec::new(),
        symlinks: vec![SymlinkSpec {
            relative_path: PathBuf::from("nested/../escape"),
            target: PathBuf::from("target"),
        }],
        hardlinks: Vec::new(),
    };

    assert!(materialize_fixture(temp.path(), &fixture).is_err());
}

// A hard-link alias of a symlink must not become an ancestor that escapes the fixture root.
#[test]
#[cfg(unix)]
fn materialize_fixture_rejects_hardlink_alias_below_symlink() {
    let temp = tempfile::tempdir().expect("tempdir");
    let outside = temp.path().join("outside");
    fs::create_dir(&outside).expect("create outside directory");
    let root = temp.path().join("fixture");
    let fixture = FixtureBlueprint {
        directories: Vec::new(),
        files: Vec::new(),
        symlinks: vec![SymlinkSpec {
            relative_path: PathBuf::from("link"),
            target: outside.clone(),
        }],
        hardlinks: vec![
            HardlinkSpec {
                relative_path: PathBuf::from("alias"),
                source_relative_path: PathBuf::from("link"),
            },
            HardlinkSpec {
                relative_path: PathBuf::from("alias/escaped"),
                source_relative_path: PathBuf::from("link"),
            },
        ],
    };

    assert!(materialize_fixture(&root, &fixture).is_err());
    assert!(!outside.join("escaped").exists());
}

// A declared symlink may itself remain the source of a hard link.
#[test]
#[cfg(unix)]
fn materialize_fixture_allows_symlink_hardlink_source() {
    let temp = tempfile::tempdir().expect("tempdir");
    let root = temp.path().join("fixture");
    let fixture = FixtureBlueprint {
        directories: Vec::new(),
        files: Vec::new(),
        symlinks: vec![SymlinkSpec {
            relative_path: PathBuf::from("link"),
            target: PathBuf::from("missing-target"),
        }],
        hardlinks: vec![HardlinkSpec {
            relative_path: PathBuf::from("alias"),
            source_relative_path: PathBuf::from("link"),
        }],
    };

    materialize_fixture(&root, &fixture).expect("materialize fixture");

    let source = fs::symlink_metadata(root.join("link")).expect("source metadata");
    let alias = fs::symlink_metadata(root.join("alias")).expect("alias metadata");
    assert!(alias.file_type().is_symlink());
    assert_eq!((source.dev(), source.ino()), (alias.dev(), alias.ino()));
}

// Staging must retain an alias partition in both independently cloned trees.
#[test]
#[cfg(unix)]
fn clone_fixture_tree_preserves_hardlinks() {
    let temp = tempfile::tempdir().expect("tempdir");
    let fixture = FixtureBlueprint {
        directories: Vec::new(),
        files: vec![FileSpec {
            relative_path: PathBuf::from("source"),
            bytes: b"payload".to_vec(),
            mode: 0o644,
        }],
        symlinks: Vec::new(),
        hardlinks: vec![HardlinkSpec {
            relative_path: PathBuf::from("alias"),
            source_relative_path: PathBuf::from("source"),
        }],
    };

    let (reference, dut) =
        stage_iteration_dirs(temp.path(), None, 0, &fixture, false).expect("stage fixture trees");

    for root in [&reference, &dut] {
        let source = fs::symlink_metadata(root.join("source")).expect("source metadata");
        let alias = fs::symlink_metadata(root.join("alias")).expect("alias metadata");
        assert_eq!((source.dev(), source.ino()), (alias.dev(), alias.ino()));
    }
}

// Equal bytes with different alias partitions must be reported as a filesystem mismatch.
#[test]
fn compare_detects_hardlink_partition_difference() {
    let node = |host_key| FsNodeSnapshot {
        raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
        kind: "file".to_string(),
        mode_octal: "644".to_string(),
        times: FsTimes::default(),
        uid: None,
        gid: None,
        logical_size: None,
        allocated_512_blocks: None,
        preferred_io_block_bytes: None,
        target: String::new(),
        data: b"payload".to_vec(),
        host_key,
        link_count: Some(2),
    };
    let reference = BTreeMap::from([
        (
            "source".to_string(),
            node(Some(HostInodeKeySnapshot {
                device: 1,
                inode: 1,
            })),
        ),
        (
            "alias".to_string(),
            node(Some(HostInodeKeySnapshot {
                device: 1,
                inode: 1,
            })),
        ),
    ]);
    let dut = BTreeMap::from([
        (
            "source".to_string(),
            node(Some(HostInodeKeySnapshot {
                device: 2,
                inode: 7,
            })),
        ),
        (
            "alias".to_string(),
            node(Some(HostInodeKeySnapshot {
                device: 2,
                inode: 8,
            })),
        ),
    ]);
    let result = compare_results_with_roots(
        "cat",
        &[],
        &RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: Vec::new(),
            stderr: Vec::new(),
        },
        &RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: Vec::new(),
            stderr: Vec::new(),
        },
        &IdentityTransitionEvidence::new(),
        &reference,
        &IdentityTransitionEvidence::new(),
        &dut,
        false,
        None,
        None,
        None,
    )
    .unwrap();
    assert!(matches!(result, CompareResult::Mismatch { fs_diff, .. } if !fs_diff.is_empty()));
}

// A regular-file snapshot preserves the complete Unix inode metadata used by stat and ls.
#[test]
#[cfg(unix)]
fn snapshot_fs_records_regular_file_identity() {
    let temp = tempfile::tempdir().expect("tempdir");
    let path = temp.path().join("file");
    fs::write(&path, b"payload").expect("write file");
    let metadata = fs::symlink_metadata(&path).expect("file metadata");

    let snapshot = snapshot_fs(temp.path()).expect("snapshot filesystem");
    let node = snapshot.get("file").expect("file snapshot");

    assert_eq!(
        node.host_key,
        Some(HostInodeKeySnapshot {
            device: metadata.dev(),
            inode: metadata.ino(),
        })
    );
    assert_eq!(node.link_count, Some(metadata.nlink()));
    assert_eq!(node.uid, Some(metadata.uid()));
    assert_eq!(node.gid, Some(metadata.gid()));
    assert_eq!(node.logical_size, Some(metadata.size()));
    assert_eq!(node.allocated_512_blocks, Some(metadata.blocks()));
    assert_eq!(node.preferred_io_block_bytes, Some(metadata.blksize()));
}

// A directory snapshot retains its concrete Unix link count instead of a namespace-derived value.
#[test]
#[cfg(unix)]
fn snapshot_fs_records_directory_identity() {
    let temp = tempfile::tempdir().expect("tempdir");
    let path = temp.path().join("directory");
    fs::create_dir(&path).expect("create directory");
    let metadata = fs::symlink_metadata(&path).expect("directory metadata");

    let snapshot = snapshot_fs(temp.path()).expect("snapshot filesystem");
    let node = snapshot.get("directory").expect("directory snapshot");

    assert_eq!(
        node.host_key,
        Some(HostInodeKeySnapshot {
            device: metadata.dev(),
            inode: metadata.ino()
        })
    );
    assert_eq!(node.link_count, Some(metadata.nlink()));
}

// Reducing a source either keeps it or removes every hard link that depends on it.
#[test]
fn fixture_reduction_preserves_hardlink_source() {
    let case = GeneratedCase {
        argv: vec!["cat".to_string()],
        fixture: FixtureBlueprint {
            directories: Vec::new(),
            files: vec![
                FileSpec {
                    relative_path: PathBuf::from("other"),
                    bytes: b"other".to_vec(),
                    mode: 0o644,
                },
                FileSpec {
                    relative_path: PathBuf::from("source"),
                    bytes: b"payload".to_vec(),
                    mode: 0o644,
                },
            ],
            symlinks: Vec::new(),
            hardlinks: vec![HardlinkSpec {
                relative_path: PathBuf::from("alias"),
                source_relative_path: PathBuf::from("source"),
            }],
        },
        stdin: Vec::new(),
        cwd: PathBuf::from("."),
    };

    for candidate in reduce_fixture(&case) {
        let files: BTreeSet<_> = candidate
            .fixture
            .files
            .iter()
            .map(|file| &file.relative_path)
            .collect();
        assert!(candidate.fixture.hardlinks.iter().all(|link| {
            files.contains(&link.source_relative_path)
                || !case
                    .fixture
                    .hardlinks
                    .iter()
                    .any(|original| original.relative_path == link.relative_path)
        }));
    }
}
