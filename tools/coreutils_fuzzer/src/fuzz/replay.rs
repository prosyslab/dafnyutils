use super::comparison::compare::{mismatch_signature, report_mismatch};
use super::comparison::evaluation::CaseVerdict;
use super::container::CommandCaseExecutor;
use super::repro::{decode_manifest, ReproManifest};
use super::runtime::resolve_fuzz_paths;
use super::shrink::evaluate_case_with_executor;
use super::system_state_concretizer::validate_fixture;
use crate::utils::capabilities::require_fuzz_capability;
use crate::utils::cli::{CampaignArgs, FuzzArgs, ReplayArgs};
use crate::utils::execution_context::{canonical_process_environment, selected_process_umask};
use crate::{fuzzer_outcome_marker, REPLAY_NOT_REPRODUCED, SEMANTIC_MISMATCH};
use std::fs;
use std::path::{Component, Path};

pub(crate) fn run_replay(args: ReplayArgs) -> Result<(), String> {
    let manifest_path = args.repro.join("manifest.json");
    let bytes = fs::read(&manifest_path).map_err(|error| {
        format!(
            "failed to read replay manifest `{}`: {error}",
            manifest_path.display()
        )
    })?;
    let manifest = decode_manifest(&bytes).map_err(|error| {
        format!(
            "failed to decode replay manifest `{}`: {error}",
            manifest_path.display()
        )
    })?;
    require_fuzz_capability(&manifest.util)?;
    validate_replay_case(&manifest.case)?;
    validate_replay_context(&manifest)?;
    validate_saved_verdict(&manifest)?;

    let mut fuzz_args = FuzzArgs {
        common: CampaignArgs {
            util: manifest.util.clone(),
            ref_bin: Some(args.ref_bin.unwrap_or(manifest.reference.path.clone())),
            ref_kind: args.ref_kind.unwrap_or(manifest.reference.kind),
            opts: None,
            iterations: 1,
            seed: Some(manifest.seed),
            max_args: manifest.case.argv.len(),
            max_fs_entries: fixture_entry_count(&manifest.case.fixture),
            workdir_mode: manifest.workdir_mode,
            case_set: None,
            metrics_out: None,
            work_root: args.work_root.clone(),
            container_image: args
                .container_image
                .clone()
                .unwrap_or_else(|| manifest.execution_context.container_image_id.clone()),
            target_uid: manifest.execution_context.target_uid,
            target_gid: manifest.execution_context.target_gid,
        },
        dut_bin: Some(args.dut_bin.unwrap_or(manifest.dut.path.clone())),
        dut_kind: args.dut_kind.unwrap_or(manifest.dut.kind),
        shrink_attempts: 0,
        process_timeout_seconds: args
            .process_timeout_seconds
            .unwrap_or(manifest.process_timeout_seconds),
        ignore_stderr: manifest.comparison.ignore_stderr,

        process_umask: Some(manifest.execution_context.umask),
        replay_fixture_times: Some(
            manifest
                .comparison
                .expected_replay_verdict
                .fixture_time_inputs()?,
        ),
        container_image_id: None,
        compose_provenance: Some(Box::new(super::container::compose_provenance()?)),
    };
    let paths = resolve_fuzz_paths(&fuzz_args)?;
    let mut executor = CommandCaseExecutor::create(&fuzz_args, &paths)?;
    fuzz_args.container_image_id = Some(executor.image_id().unwrap_or("local-test").to_string());
    fuzz_args.common.work_root = Some(executor.work_root_base().to_path_buf());
    let evaluation = evaluate_case_with_executor(
        &fuzz_args,
        &mut executor,
        manifest.seed,
        manifest.iteration,
        manifest.iteration,
        &manifest.case,
    )?;

    let actual_verdict = evaluation.replay_verdict.clone();
    let scope = format!(
        "replay schema={} original_work_root_base={} container_image_id={}",
        manifest.schema_version,
        manifest
            .execution_context
            .work_root_base
            .as_ref()
            .and_then(Option::as_deref)
            .map_or_else(
                || "unobserved".to_string(),
                |path| path.display().to_string()
            ),
        executor.image_id().unwrap_or("local-test"),
    );
    let actual_comparison = evaluation.comparison.clone();
    match actual_comparison.verdict() {
        CaseVerdict::Match => Err(format!(
            "{}\nreplay did not reproduce the saved {:?} mismatch for util={} seed={} iteration={}\n{scope}",
            fuzzer_outcome_marker(REPLAY_NOT_REPRODUCED),
            manifest.comparison.expected_mismatch_signature,
            manifest.util,
            manifest.seed,
            manifest.iteration
        )),
        CaseVerdict::Mismatch => {
            let compare = actual_verdict.comparison.clone();
            let actual_signature = mismatch_signature(
                &compare,
                &actual_verdict.reference_identity,
                &actual_verdict.dut_identity,
            );
            let mismatch_kind = actual_signature
                .map(|signature| format!("{signature:?}"))
                .unwrap_or_else(|| "Observable".to_string());
            if actual_signature != manifest.comparison.expected_mismatch_signature
                || !actual_comparison.reproduces(&manifest.comparison.evaluated)
                || !actual_verdict.reproduces(&manifest.comparison.expected_replay_verdict)?
            {
                return Err(format!(
                    "{}\nreplay produced a different verdict ({}), expected {:?}, for util={} seed={} iteration={}\n{scope}",
                    fuzzer_outcome_marker(REPLAY_NOT_REPRODUCED),
                    mismatch_kind,
                    manifest.comparison.expected_mismatch_signature,
                    manifest.util,
                    manifest.seed,
                    manifest.iteration
                ));
            }
            if actual_signature.is_some() {
                report_mismatch(
                    manifest.seed,
                    manifest.iteration,
                    &manifest.util,
                    &evaluation.case.argv,
                    &evaluation.reference,
                    &evaluation.dut,
                    &compare,
                );
            } else {
                eprintln!("{}", fuzzer_outcome_marker(SEMANTIC_MISMATCH));
                eprintln!("Observable mismatch detected");
            }
            Err(format!(
                "{}\nreplay reproduced {} mismatch for util={} seed={} iteration={}\n{scope}",
                fuzzer_outcome_marker(SEMANTIC_MISMATCH),
                mismatch_kind,
                manifest.util,
                manifest.seed,
                manifest.iteration
            ))
        }
    }
}

fn validate_saved_verdict(manifest: &ReproManifest) -> Result<(), String> {
    let verdict = &manifest.comparison.expected_replay_verdict;
    let evaluated = &manifest.comparison.evaluated;
    verdict.validate_time_evidence()?;
    if evaluated.execution != verdict.execution {
        return Err("saved evaluation execution evidence disagrees with replay".into());
    }
    if evaluated.observable != verdict.comparison {
        return Err("replay manifest observable comparison disagrees with saved verdict".into());
    }
    if evaluated.verdict() == CaseVerdict::Match {
        return Err("replay manifest expected verdict is not a mismatch".to_string());
    }
    let derived = mismatch_signature(
        &verdict.comparison,
        &verdict.reference_identity,
        &verdict.dut_identity,
    );
    if derived != manifest.comparison.expected_mismatch_signature {
        return Err(format!(
            "replay manifest mismatch signature {:?} disagrees with saved verdict {:?}",
            manifest.comparison.expected_mismatch_signature, derived
        ));
    }
    Ok(())
}

fn validate_replay_context(manifest: &ReproManifest) -> Result<(), String> {
    if manifest.execution_context.environment != canonical_process_environment() {
        return Err(
            "replay manifest environment does not match the controlled execution context"
                .to_string(),
        );
    }
    crate::utils::execution_context::validate_process_umask(manifest.execution_context.umask)?;
    let expected_umask = selected_process_umask(manifest.seed, manifest.iteration);
    if manifest.execution_context.umask != expected_umask {
        return Err(format!(
            "replay manifest umask {:?} does not match expected {:?}",
            manifest.execution_context.umask, expected_umask
        ));
    }
    Ok(())
}

fn fixture_entry_count(fixture: &super::FixtureBlueprint) -> usize {
    fixture.directories.len()
        + fixture.files.len()
        + fixture.symlinks.len()
        + fixture.hardlinks.len()
}

fn validate_replay_case(case: &super::GeneratedCase) -> Result<(), String> {
    validate_fixture(&case.fixture)?;
    if case.cwd == Path::new(".") {
        return Ok(());
    }
    if case.cwd.as_os_str().is_empty()
        || case.cwd.is_absolute()
        || case.cwd.components().any(|component| {
            matches!(
                component,
                Component::CurDir
                    | Component::ParentDir
                    | Component::RootDir
                    | Component::Prefix(_)
            )
        })
    {
        return Err(format!(
            "replay case cwd must be `.` or a normalized relative path: `{}`",
            case.cwd.display()
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::run_replay;
    use crate::fuzz::comparison::compare::stream_evidence;
    use crate::fuzz::repro::{save_repro_at, ReproManifest, REPRO_SCHEMA_VERSION};
    use crate::fuzz::shrink::{evaluate_case_with_seed, shrink_mismatch};
    use crate::fuzz::{
        DirSpec, FileSpec, FixtureBlueprint, GeneratedCase, HardlinkSpec, ResolvedPaths,
        ResolvedTarget, SymlinkSpec,
    };
    use crate::utils::cli::{Cli, CliCommand, ExecKind};
    use crate::{FUZZER_OUTCOME_MARKER_PREFIX, REPLAY_NOT_REPRODUCED, SEMANTIC_MISMATCH};
    use clap::Parser;
    use std::collections::BTreeMap;
    use std::fs;
    use std::path::PathBuf;

    fn native_paths() -> ResolvedPaths {
        ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: PathBuf::from("/bin/cat"),
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: PathBuf::from("/bin/false"),
                label: "dut",
            },
        }
    }

    fn parse_replay(bundle: &std::path::Path) -> crate::utils::cli::ReplayArgs {
        let replay = Cli::try_parse_from([
            "coreutils_fuzzer",
            "replay",
            "--repro",
            bundle.to_str().unwrap(),
        ])
        .unwrap();
        let CliCommand::Replay(replay_args) = replay.command else {
            unreachable!()
        };
        replay_args
    }

    fn save_case_bundle(
        root: &std::path::Path,
        args: &crate::utils::cli::FuzzArgs,
        paths: &ResolvedPaths,
        case: &GeneratedCase,
    ) -> PathBuf {
        let evaluation = evaluate_case_with_seed(args, paths, root, None, 17, 9, case).unwrap();
        save_repro_at(
            root,
            args,
            17,
            9,
            paths,
            &evaluation.case,
            &evaluation.reference,
            &evaluation.dut,
            &evaluation.comparison,
            evaluation.mismatch_signature.as_ref(),
            &evaluation.replay_verdict,
            &evaluation.pre_fs,
            &evaluation.dut_pre_fs,
            &evaluation.reference_fs,
            &evaluation.dut_fs,
            &evaluation.reference_identity,
            &evaluation.dut_identity,
        )
        .unwrap()
    }

    fn bundle_files(path: &std::path::Path) -> BTreeMap<String, Vec<u8>> {
        fs::read_dir(path)
            .unwrap()
            .map(|entry| {
                let entry = entry.unwrap();
                (
                    entry.file_name().to_string_lossy().into_owned(),
                    fs::read(entry.path()).unwrap(),
                )
            })
            .collect()
    }

    fn mismatch_args(reference: PathBuf, dut: PathBuf) -> crate::utils::cli::FuzzArgs {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "cat",
            "--ref-bin",
            reference.to_str().unwrap(),
            "--dut-bin",
            dut.to_str().unwrap(),
            "--ref-kind",
            "native",
            "--dut-kind",
            "native",
            "--iterations",
            "1",
            "--seed",
            "17",
            "--shrink-attempts",
            "1",
        ])
        .unwrap();
        let CliCommand::Fuzz(mut args) = cli.command else {
            unreachable!()
        };
        args.common.work_root = Some(PathBuf::from("/tmp"));
        args
    }

    // A saved controlled mismatch replays the exact case with the same semantic verdict.
    #[test]
    fn saved_mismatch_replays_with_same_signature() {
        let root = tempfile::tempdir().unwrap();
        let args = mismatch_args(PathBuf::from("/bin/cat"), PathBuf::from("/bin/false"));
        let paths = native_paths();
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: b"saved stdin\n".to_vec(),
            cwd: PathBuf::from("."),
        };
        let original =
            evaluate_case_with_seed(&args, &paths, root.path(), None, 17, 9, &case).unwrap();
        let evaluation =
            shrink_mismatch(&args, &paths, root.path(), None, 17, 9, original, 1).unwrap();
        assert_ne!(evaluation.case.stdin, case.stdin);
        assert!(!evaluation.case.stdin.is_empty());
        let bundle = save_repro_at(
            root.path(),
            &args,
            17,
            9,
            &paths,
            &evaluation.case,
            &evaluation.reference,
            &evaluation.dut,
            &evaluation.comparison,
            evaluation.mismatch_signature.as_ref(),
            &evaluation.replay_verdict,
            &evaluation.pre_fs,
            &evaluation.dut_pre_fs,
            &evaluation.reference_fs,
            &evaluation.dut_fs,
            &evaluation.reference_identity,
            &evaluation.dut_identity,
        )
        .unwrap();
        let error = run_replay(parse_replay(&bundle)).unwrap_err();
        let manifest: ReproManifest =
            serde_json::from_slice(&fs::read(bundle.join("manifest.json")).unwrap()).unwrap();

        assert!(
            error.contains(&format!(
                "{FUZZER_OUTCOME_MARKER_PREFIX}{SEMANTIC_MISMATCH}"
            )),
            "{error}"
        );
        assert!(error.contains("replay reproduced ProcessOutcome mismatch"));
        assert_eq!(manifest.schema_version, REPRO_SCHEMA_VERSION);
        assert_eq!(manifest.comparison.evaluated, evaluation.comparison);
        assert_eq!(manifest.case, evaluation.case);
        assert_eq!(
            fs::read(bundle.join("stdin.bin")).unwrap(),
            evaluation.case.stdin
        );
        let saved_result: serde_json::Value =
            serde_json::from_slice(&fs::read(bundle.join("reference_result.json")).unwrap())
                .unwrap();
        assert_eq!(saved_result["termination"]["kind"], "exit");
        assert_eq!(saved_result["termination"]["raw_status"], 0);
        assert!(saved_result.get("exit_code").is_none());
        assert_eq!(
            saved_result["stdout"],
            serde_json::to_value(stream_evidence(&evaluation.reference.stdout)).unwrap()
        );
        assert!(fs::read_to_string(bundle.join("reproduce.sh"))
            .unwrap()
            .contains("run.py replay"));
    }

    // Saved placement is provenance and cannot make replay access or adopt a host path.
    #[test]
    fn replay_does_not_adopt_saved_work_root() {
        let root = tempfile::tempdir().unwrap();
        let args = mismatch_args(PathBuf::from("/bin/cat"), PathBuf::from("/bin/false"));
        let paths = native_paths();
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: b"saved placement\n".to_vec(),
            cwd: PathBuf::from("."),
        };
        let bundle = save_case_bundle(root.path(), &args, &paths, &case);
        let manifest_path = bundle.join("manifest.json");
        let mut manifest: serde_json::Value =
            serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
        manifest["execution_context"]["work_root_base"] =
            "/definitely-not-present/untrusted-replay-root".into();
        fs::write(
            &manifest_path,
            serde_json::to_vec_pretty(&manifest).unwrap(),
        )
        .unwrap();

        let error = run_replay(parse_replay(&bundle)).unwrap_err();

        assert!(
            error.contains("FUZZER_OUTCOME=semantic_mismatch"),
            "{error}"
        );
        assert!(
            error.contains("original_work_root_base=/definitely-not-present/untrusted-replay-root")
        );
    }

    // Saving the same mismatch twice keeps the first versioned bundle byte-for-byte intact.
    #[test]
    fn duplicate_mismatch_save_preserves_original_bundle() {
        let root = tempfile::tempdir().unwrap();
        let args = mismatch_args(PathBuf::from("/bin/cat"), PathBuf::from("/bin/false"));
        let paths = native_paths();
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: b"preserve me\n".to_vec(),
            cwd: PathBuf::from("."),
        };

        let first = save_case_bundle(root.path(), &args, &paths, &case);
        let first_snapshot = bundle_files(&first);
        let second = save_case_bundle(root.path(), &args, &paths, &case);

        assert_ne!(first, second);
        assert!(first.ends_with("cat-seed17-iter9"));
        assert!(second.ends_with("cat-seed17-iter9-run2"));
        assert_eq!(bundle_files(&first), first_snapshot);
    }

    // Fixing the DUT to match the reference remains a replay-not-reproduced failure.
    #[test]
    fn replay_rejects_fixed_match() {
        let root = tempfile::tempdir().unwrap();
        let args = mismatch_args(PathBuf::from("/bin/cat"), PathBuf::from("/bin/false"));
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: b"fixed input\n".to_vec(),
            cwd: PathBuf::from("."),
        };
        let bundle = save_case_bundle(root.path(), &args, &native_paths(), &case);
        let replay = Cli::try_parse_from([
            "coreutils_fuzzer",
            "replay",
            "--repro",
            bundle.to_str().unwrap(),
            "--dut-bin",
            "/bin/cat",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Replay(replay_args) = replay.command else {
            unreachable!()
        };

        let error = run_replay(replay_args).unwrap_err();

        assert!(error.contains(&format!(
            "{FUZZER_OUTCOME_MARKER_PREFIX}{REPLAY_NOT_REPRODUCED}"
        )));
        assert!(error.contains("replay did not reproduce"));
    }

    // A different process outcome pair is rejected within the same mismatch category.
    #[cfg(unix)]
    #[test]
    fn replay_rejects_changed_same_category_mismatch() {
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let args = mismatch_args(PathBuf::from("/bin/cat"), PathBuf::from("/bin/false"));
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: b"saved stdin\n".to_vec(),
            cwd: PathBuf::from("."),
        };
        let bundle = save_case_bundle(root.path(), &args, &native_paths(), &case);
        let changed_dut = root.path().join("exit-two.sh");
        fs::write(&changed_dut, b"#!/bin/sh\nexit 2\n").unwrap();
        fs::set_permissions(&changed_dut, fs::Permissions::from_mode(0o755)).unwrap();
        let replay = Cli::try_parse_from([
            "coreutils_fuzzer",
            "replay",
            "--repro",
            bundle.to_str().unwrap(),
            "--dut-bin",
            changed_dut.to_str().unwrap(),
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Replay(replay_args) = replay.command else {
            unreachable!()
        };

        let error = run_replay(replay_args).unwrap_err();

        assert!(error.contains(&format!(
            "{FUZZER_OUTCOME_MARKER_PREFIX}{REPLAY_NOT_REPRODUCED}"
        )));
        assert!(error.contains("different verdict (ProcessOutcome)"));
    }

    // Changed version bytes cannot reproduce a saved stdout mismatch with the same category.
    #[cfg(unix)]
    #[test]
    fn replay_rejects_changed_version_bytes_with_same_stdout_signature() {
        use crate::fuzz::comparison::compare::{MismatchSignature, ReplayStreamEvidence};
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let reference = root.path().join("reference.sh");
        let dut = root.path().join("dut.sh");
        fs::write(
            &reference,
            b"#!/bin/sh\nprintf 'cat (GNU coreutils) 9.4\\n'\n",
        )
        .unwrap();
        fs::write(&dut, b"#!/bin/sh\nprintf 'cat (GNU coreutils) 9.3\\n'\n").unwrap();
        fs::set_permissions(&reference, fs::Permissions::from_mode(0o755)).unwrap();
        fs::set_permissions(&dut, fs::Permissions::from_mode(0o755)).unwrap();
        let args = mismatch_args(reference.clone(), dut.clone());
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: reference,
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: dut.clone(),
                label: "dut",
            },
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["--version".to_string()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let bundle = save_case_bundle(root.path(), &args, &paths, &case);
        let manifest: ReproManifest =
            serde_json::from_slice(&fs::read(bundle.join("manifest.json")).unwrap()).unwrap();
        assert_eq!(
            manifest.comparison.expected_mismatch_signature,
            Some(MismatchSignature::Stdout)
        );
        assert_eq!(
            manifest.comparison.expected_replay_verdict.dut_stdout,
            ReplayStreamEvidence::RawBytes(b"cat (GNU coreutils) 9.3\n".to_vec())
        );
        fs::write(&dut, b"#!/bin/sh\nprintf 'cat (GNU coreutils) 9.2\\n'\n").unwrap();

        let error = run_replay(parse_replay(&bundle)).unwrap_err();

        assert!(
            error.contains(&format!(
                "{FUZZER_OUTCOME_MARKER_PREFIX}{REPLAY_NOT_REPRODUCED}"
            )),
            "{error}"
        );
        assert!(error.contains("different verdict (Stdout)"), "{error}");
    }

    // A different same-path filesystem mutation cannot satisfy the saved coarse fs category.
    #[cfg(unix)]
    #[test]
    fn replay_rejects_changed_content_with_same_filesystem_signature() {
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let write_b = root.path().join("write-b.sh");
        let write_c = root.path().join("write-c.sh");
        fs::write(&write_b, b"#!/bin/sh\nprintf B > data\n").unwrap();
        fs::write(&write_c, b"#!/bin/sh\nprintf C > data\n").unwrap();
        fs::set_permissions(&write_b, fs::Permissions::from_mode(0o755)).unwrap();
        fs::set_permissions(&write_c, fs::Permissions::from_mode(0o755)).unwrap();
        let args = mismatch_args(PathBuf::from("/bin/true"), write_b.clone());
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: PathBuf::from("/bin/true"),
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: write_b,
                label: "dut",
            },
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: vec![FileSpec {
                    relative_path: PathBuf::from("data"),
                    bytes: b"A".to_vec(),
                    mode: 0o644,
                }],
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let bundle = save_case_bundle(root.path(), &args, &paths, &case);
        let replay = Cli::try_parse_from([
            "coreutils_fuzzer",
            "replay",
            "--repro",
            bundle.to_str().unwrap(),
            "--dut-bin",
            write_c.to_str().unwrap(),
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Replay(replay_args) = replay.command else {
            unreachable!()
        };

        let error = run_replay(replay_args).unwrap_err();

        assert!(error.contains(&format!(
            "{FUZZER_OUTCOME_MARKER_PREFIX}{REPLAY_NOT_REPRODUCED}"
        )));
        assert!(error.contains("different verdict (Filesystem)"));
    }

    // Replay refuses a changed execution environment instead of silently using it.
    #[test]
    fn replay_rejects_noncanonical_environment() {
        let root = tempfile::tempdir().unwrap();
        let args = mismatch_args(PathBuf::from("/bin/cat"), PathBuf::from("/bin/false"));
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: b"saved stdin\n".to_vec(),
            cwd: PathBuf::from("."),
        };
        let bundle = save_case_bundle(root.path(), &args, &native_paths(), &case);
        let manifest_path = bundle.join("manifest.json");
        let mut manifest: ReproManifest =
            serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
        manifest
            .execution_context
            .environment
            .insert("SECRET_TOKEN".to_string(), "must-not-inherit".to_string());
        fs::write(
            &manifest_path,
            serde_json::to_vec_pretty(&manifest).unwrap(),
        )
        .unwrap();

        let error = run_replay(parse_replay(&bundle)).unwrap_err();

        assert!(error.contains("environment does not match"));
    }

    // A saved non-chmod mask outside its seed/iteration schedule is rejected before replay.
    #[test]
    fn replay_rejects_changed_non_chmod_schedule_umask() {
        let root = tempfile::tempdir().unwrap();
        let args = mismatch_args(PathBuf::from("/bin/cat"), PathBuf::from("/bin/false"));
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: b"saved stdin\n".to_vec(),
            cwd: ".".into(),
        };
        let bundle = save_case_bundle(root.path(), &args, &native_paths(), &case);
        let manifest_path = bundle.join("manifest.json");
        let mut manifest: ReproManifest =
            serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
        manifest.execution_context.umask = 0o077;
        fs::write(
            &manifest_path,
            serde_json::to_vec_pretty(&manifest).unwrap(),
        )
        .unwrap();

        let error = run_replay(parse_replay(&bundle)).unwrap_err();

        assert!(error.contains("does not match expected"), "{error}");
    }

    // The redundant leading signature cannot disagree with the structured saved verdict.
    #[test]
    fn replay_rejects_inconsistent_saved_signature() {
        let root = tempfile::tempdir().unwrap();
        let args = mismatch_args(PathBuf::from("/bin/cat"), PathBuf::from("/bin/false"));
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: b"saved stdin\n".to_vec(),
            cwd: PathBuf::from("."),
        };
        let bundle = save_case_bundle(root.path(), &args, &native_paths(), &case);
        let manifest_path = bundle.join("manifest.json");
        let mut manifest: ReproManifest =
            serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
        manifest.comparison.expected_mismatch_signature =
            Some(crate::fuzz::comparison::compare::MismatchSignature::Stderr);
        fs::write(
            &manifest_path,
            serde_json::to_vec_pretty(&manifest).unwrap(),
        )
        .unwrap();

        let error = run_replay(parse_replay(&bundle)).unwrap_err();

        assert!(error.contains("disagrees with saved verdict"));
    }

    // Replay recreates a normal-target file with the saved seed/iteration schedule umask.
    #[cfg(unix)]
    #[test]
    fn replay_reuses_saved_scheduled_process_umask() {
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let creator = root.path().join("create.sh");
        fs::write(&creator, b"#!/bin/sh\nsleep 0.02\n: > created\nexit 1\n").unwrap();
        let reference_creator = root.path().join("reference-create.sh");
        fs::write(
            &reference_creator,
            b"#!/bin/sh\nsleep 0.02\n: > created\nexit 0\n",
        )
        .unwrap();
        fs::set_permissions(&reference_creator, fs::Permissions::from_mode(0o755)).unwrap();
        fs::set_permissions(&creator, fs::Permissions::from_mode(0o755)).unwrap();
        let args = mismatch_args(reference_creator.clone(), creator.clone());
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: reference_creator,
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: creator,
                label: "dut",
            },
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let bundle = save_case_bundle(root.path(), &args, &paths, &case);

        let error = run_replay(parse_replay(&bundle)).unwrap_err();

        assert!(
            error.contains(&format!(
                "{FUZZER_OUTCOME_MARKER_PREFIX}{SEMANTIC_MISMATCH}"
            )),
            "{error}"
        );
        let manifest: ReproManifest =
            serde_json::from_slice(&fs::read(bundle.join("manifest.json")).unwrap()).unwrap();
        assert_eq!(manifest.execution_context.umask, 0o005);
        let created = manifest
            .comparison
            .expected_replay_verdict
            .dut_post_fs
            .nodes
            .get("created")
            .unwrap();
        assert_eq!(created.mode_octal, "0662");
    }

    // Replay validates every fixture path before a malicious bundle can overwrite external data.
    #[test]
    fn replay_rejects_fixture_escape_before_writing() {
        let root = tempfile::tempdir().unwrap();
        let args = mismatch_args(PathBuf::from("/bin/cat"), PathBuf::from("/bin/false"));
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let bundle = save_case_bundle(root.path(), &args, &native_paths(), &case);
        let sentinel = root.path().join("external-sentinel");
        fs::write(&sentinel, b"unchanged").unwrap();
        let manifest_path = bundle.join("manifest.json");
        let mut manifest: ReproManifest =
            serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
        manifest.case.fixture.files.push(FileSpec {
            relative_path: sentinel.clone(),
            bytes: b"overwritten".to_vec(),
            mode: 0o644,
        });
        fs::write(
            &manifest_path,
            serde_json::to_vec_pretty(&manifest).unwrap(),
        )
        .unwrap();

        let error = run_replay(parse_replay(&bundle)).unwrap_err();

        assert!(error.contains("invalid fixture file path"));
        assert_eq!(fs::read(&sentinel).unwrap(), b"unchanged");
    }

    // Replay restores stdin, cwd, symlinks, and hardlinks from the saved case.
    #[cfg(unix)]
    #[test]
    fn replay_restores_complete_case_inputs() {
        let root = tempfile::tempdir().unwrap();
        use std::os::unix::fs::PermissionsExt;
        let reference = root.path().join("reference-cat");
        let dut = root.path().join("dut-cat");
        fs::write(&reference, b"#!/bin/sh\nsleep 0.02\n/bin/cat \"$@\"\n").unwrap();
        fs::write(&dut, b"#!/bin/sh\nsleep 0.02\n/bin/cat \"$@\"\nexit 1\n").unwrap();
        fs::set_permissions(&reference, fs::Permissions::from_mode(0o755)).unwrap();
        fs::set_permissions(&dut, fs::Permissions::from_mode(0o755)).unwrap();
        let args = mismatch_args(reference.clone(), dut.clone());
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: reference,
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: dut,
                label: "dut",
            },
        };
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["-".to_string(), "link".to_string(), "../alias".to_string()],
            fixture: FixtureBlueprint {
                directories: vec![DirSpec {
                    relative_path: PathBuf::from("work"),
                    mode: 0o755,
                }],
                files: vec![FileSpec {
                    relative_path: PathBuf::from("data"),
                    bytes: b"fixture data\n".to_vec(),
                    mode: 0o640,
                }],
                symlinks: vec![SymlinkSpec {
                    relative_path: PathBuf::from("work/link"),
                    target: PathBuf::from("../data"),
                }],
                hardlinks: vec![HardlinkSpec {
                    relative_path: PathBuf::from("alias"),
                    source_relative_path: PathBuf::from("data"),
                }],
            },
            stdin: b"saved stdin\n".to_vec(),
            cwd: PathBuf::from("work"),
        };
        let bundle = save_case_bundle(root.path(), &args, &paths, &case);

        let error = run_replay(parse_replay(&bundle)).unwrap_err();

        assert!(
            error.contains(&format!(
                "{FUZZER_OUTCOME_MARKER_PREFIX}{SEMANTIC_MISMATCH}"
            )),
            "{error}"
        );
        let manifest: ReproManifest =
            serde_json::from_slice(&fs::read(bundle.join("manifest.json")).unwrap()).unwrap();
        assert_eq!(manifest.case, case);
    }

    fn metadata_manifest_fixture() -> serde_json::Value {
        let root = tempfile::tempdir().unwrap();
        let args = mismatch_args(PathBuf::from("/bin/cat"), PathBuf::from("/bin/false"));
        let case = GeneratedCase {
            file_size_limit: None,
            argv: vec!["-".into()],
            stdin: vec![0, 128, 255],
            cwd: PathBuf::from("."),
            fixture: FixtureBlueprint {
                directories: vec![],
                files: vec![],
                symlinks: vec![],
                hardlinks: vec![],
            },
        };
        let bundle = save_case_bundle(root.path(), &args, &native_paths(), &case);
        serde_json::from_slice(&fs::read(bundle.join("manifest.json")).unwrap()).unwrap()
    }

    // Current typed process evidence rejects missing, ambiguous, inconsistent, and widened payloads.
    #[test]
    fn current_replay_rejects_malformed_process_outcomes() {
        let current = metadata_manifest_fixture();
        let verdict_path = ["comparison", "expected_replay_verdict"];

        let mut missing = current.clone();
        missing[verdict_path[0]][verdict_path[1]]
            .as_object_mut()
            .unwrap()
            .remove("reference_process_outcome");
        assert!(super::decode_manifest(&serde_json::to_vec(&missing).unwrap()).is_err());

        let mut ambiguous = current.clone();
        ambiguous[verdict_path[0]][verdict_path[1]]["reference_process_outcome"] = 141.into();
        let error = super::decode_manifest(&serde_json::to_vec(&ambiguous).unwrap()).unwrap_err();
        assert!(error.contains("invalid type: integer"), "{error}");

        let mut inconsistent = current.clone();
        inconsistent[verdict_path[0]][verdict_path[1]]["reference_process_outcome"] =
            serde_json::json!({"kind":"exit", "code":141, "raw_status":13});
        let error =
            super::decode_manifest(&serde_json::to_vec(&inconsistent).unwrap()).unwrap_err();
        assert!(
            error.contains("disagrees with raw Unix wait status"),
            "{error}"
        );

        let mut widened = current;
        widened[verdict_path[0]][verdict_path[1]]["reference_process_outcome"] = serde_json::json!({"kind":"signal", "signal":13, "core_dumped":false, "raw_status":13, "code":141});
        assert!(super::decode_manifest(&serde_json::to_vec(&widened).unwrap()).is_err());
    }

    // A saved current process mismatch must contain genuinely different outcomes.
    #[test]
    fn current_replay_rejects_equal_process_difference() {
        let mut current = metadata_manifest_fixture();
        let verdict = &mut current["comparison"]["expected_replay_verdict"];
        let outcome = verdict["reference_process_outcome"].clone();
        verdict["dut_process_outcome"] = outcome.clone();
        verdict["comparison"]["Mismatch"]["process_outcome_diff"] =
            serde_json::json!([outcome, outcome]);
        current["comparison"]["evaluated"]["observable"] =
            current["comparison"]["expected_replay_verdict"]["comparison"].clone();
        current["comparison"]["expected_mismatch_signature"] = "ProcessOutcome".into();
        let error = super::decode_manifest(&serde_json::to_vec(&current).unwrap()).unwrap_err();
        assert!(
            error.contains("difference contains equal outcomes"),
            "{error}"
        );
    }

    // Repeated top-level values must not replace the original current replay seed.
    #[test]
    fn current_replay_rejects_duplicate_seed() {
        let value = metadata_manifest_fixture();
        let encoded = serde_json::to_string(&value).unwrap();
        let needle = format!("\"seed\":{}", value["seed"]);
        assert!(encoded.contains(&needle));
        let duplicate = encoded.replacen(&needle, &format!("\"seed\":999,{needle}"), 1);
        let error = super::decode_manifest(duplicate.as_bytes()).unwrap_err();
        assert!(error.contains("duplicate field `seed`"), "{error}");
    }

    // A second code cannot erase a contradictory value inside a typed outcome.
    #[test]
    fn current_replay_rejects_duplicate_outcome_code() {
        let encoded = serde_json::to_string(&metadata_manifest_fixture()).unwrap();
        assert!(encoded.contains("\"code\":0"));
        let duplicate = encoded.replacen("\"code\":0", "\"code\":27,\"code\":0", 1);
        let error = super::decode_manifest(duplicate.as_bytes()).unwrap_err();
        assert!(error.contains("duplicate field `code`"), "{error}");
    }

    // Raw wait status is an observation and cannot be replaced by a later duplicate.
    #[test]
    fn current_replay_rejects_duplicate_raw_wait_status() {
        let encoded = serde_json::to_string(&metadata_manifest_fixture()).unwrap();
        assert!(encoded.contains("\"raw_status\":0"));
        let duplicate =
            encoded.replacen("\"raw_status\":0", "\"raw_status\":13,\"raw_status\":0", 1);
        let error = super::decode_manifest(duplicate.as_bytes()).unwrap_err();
        assert!(error.contains("duplicate field `raw_status`"), "{error}");
    }

    // Process format migration must not erase duplicate raw-stat metadata fields.
    #[test]
    fn current_replay_rejects_duplicate_raw_metadata_value() {
        let mut value = metadata_manifest_fixture();
        let node = value["comparison"]["expected_replay_verdict"]["reference_pre_fs"]["nodes"]
            .as_object_mut()
            .unwrap()
            .values_mut()
            .next()
            .unwrap();
        node["raw_stat_metadata"] =
            serde_json::json!({"Known": {"device_number": 0, "io_block_bytes": -1}});
        let encoded = serde_json::to_string(&value).unwrap();
        assert!(super::decode_manifest(encoded.as_bytes()).is_ok());
        let duplicate = encoded.replacen(
            "\"device_number\":0",
            "\"device_number\":7,\"device_number\":0",
            1,
        );
        let error = super::decode_manifest(duplicate.as_bytes()).unwrap_err();
        assert!(error.contains("duplicate field `device_number`"), "{error}");
    }

    // A current comparison cannot combine a typed difference with an ignored legacy difference.
    #[test]
    fn current_replay_rejects_mixed_comparison_fields() {
        let mut value = metadata_manifest_fixture();
        value["comparison"]["expected_replay_verdict"]["comparison"]["Mismatch"]["exit_diff"] =
            serde_json::json!([0, 141]);
        let error = super::decode_manifest(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(error.contains("unknown field `exit_diff`"), "{error}");
    }

    // Current process evidence cannot use a legacy mismatch category to claim the current format.
    #[test]
    fn current_replay_rejects_legacy_mismatch_category() {
        let mut value = metadata_manifest_fixture();
        value["comparison"]["expected_mismatch_signature"] = "ExitCode".into();
        let error = super::decode_manifest(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(error.contains("unknown variant `ExitCode`"), "{error}");
    }

    // The current schema requires placement provenance instead of treating absence as a default.
    #[test]
    fn current_schema_rejects_missing_work_root_base() {
        let mut value = metadata_manifest_fixture();
        value["execution_context"]
            .as_object_mut()
            .unwrap()
            .remove("work_root_base");
        let error = super::decode_manifest(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(error.contains("missing work-root base"), "{error}");
    }

    // The current schema rejects explicit null separately from an absent placement field.
    #[test]
    fn current_schema_rejects_null_work_root_base() {
        let mut value = metadata_manifest_fixture();
        value["execution_context"]["work_root_base"] = serde_json::Value::Null;
        let error = super::decode_manifest(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(error.contains("null work-root base"), "{error}");
    }

    // Duplicate placement fields are rejected directly from original manifest bytes.
    #[test]
    fn current_schema_rejects_duplicate_work_root_base() {
        let value = metadata_manifest_fixture();
        let encoded = String::from_utf8(serde_json::to_vec(&value).unwrap()).unwrap();
        let duplicated = encoded.replacen(
            "\"work_root_base\":\"/tmp\"",
            "\"work_root_base\":\"/tmp\",\"work_root_base\":\"/tmp\"",
            1,
        );
        assert_ne!(encoded, duplicated);
        let error = super::decode_manifest(duplicated.as_bytes()).unwrap_err();
        assert!(
            error.contains("duplicate field `work_root_base`"),
            "{error}"
        );
    }

    // The current schema requires the configured container image as replay provenance.
    #[test]
    fn current_schema_rejects_missing_container_image() {
        let mut value = metadata_manifest_fixture();
        value["execution_context"]
            .as_object_mut()
            .unwrap()
            .remove("container_image");
        let error = super::decode_manifest(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(error.contains("missing field `container_image`"), "{error}");
    }

    // The current schema requires the numeric target UID rather than adopting the replay host UID.
    #[test]
    fn current_schema_rejects_missing_target_uid() {
        let mut value = metadata_manifest_fixture();
        value["execution_context"]
            .as_object_mut()
            .unwrap()
            .remove("target_uid");
        let error = super::decode_manifest(&serde_json::to_vec(&value).unwrap()).unwrap_err();
        assert!(error.contains("missing field `target_uid`"), "{error}");
    }

    // Unknown versions are diagnosed before attempting the current version's required fields.
    #[test]
    fn replay_reports_unsupported_version_before_payload_shape() {
        for version in [1, 2, 3, 4, 5, 6, 7, 8, 999] {
            let bytes = format!(r#"{{"schema_version":{version}}}"#);
            let error = super::decode_manifest(bytes.as_bytes()).unwrap_err();
            assert!(
                error.contains(&format!("unsupported replay schema version {version}")),
                "{error}"
            );
            assert!(error.contains("--case-set"), "{error}");
        }
    }

    // A candidate that crashes with a long stderr leaves a bounded bundle that still replays.
    #[cfg(unix)]
    #[test]
    fn long_crash_output_is_saved_bounded_and_replays() {
        use crate::fuzz::comparison::compare::ReplayStreamEvidence;
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let dut = root.path().join("dut.sh");
        fs::write(
            &dut,
            b"#!/bin/sh\nyes '   at CatCore.ConcatPieces' | head -c 200000 >&2\nexit 3\n",
        )
        .unwrap();
        fs::set_permissions(&dut, fs::Permissions::from_mode(0o755)).unwrap();
        let args = mismatch_args(PathBuf::from("/bin/cat"), dut.clone());
        let mut paths = native_paths();
        paths.dut.path = dut;
        let case = GeneratedCase {
            file_size_limit: None,
            argv: Vec::new(),
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let bundle = save_case_bundle(root.path(), &args, &paths, &case);
        let manifest: ReproManifest =
            serde_json::from_slice(&fs::read(bundle.join("manifest.json")).unwrap()).unwrap();
        let ReplayStreamEvidence::Bounded(saved) =
            &manifest.comparison.expected_replay_verdict.dut_stderr
        else {
            panic!("long stderr must be bounded");
        };
        assert_eq!(saved.length, 200_000);
        assert!(fs::metadata(bundle.join("manifest.json")).unwrap().len() < 2 * 1024 * 1024);
        let result: serde_json::Value =
            serde_json::from_slice(&fs::read(bundle.join("dut_result.json")).unwrap()).unwrap();
        assert_eq!(result["stderr"]["bounded"]["length"], 200_000);
        let raw = fs::read(bundle.join("dut.stderr")).unwrap();
        let marker = b"\n[coreutils-fuzzer: 134464 of 200000 bytes omitted]\n";
        assert_eq!(raw.len(), 64 * 1024 + marker.len());
        assert_eq!(&raw[32 * 1024..32 * 1024 + marker.len()], marker);
        let error = run_replay(parse_replay(&bundle)).unwrap_err();
        assert!(
            error.contains(&format!(
                "{FUZZER_OUTCOME_MARKER_PREFIX}{SEMANTIC_MISMATCH}"
            )),
            "{error}"
        );
    }
}
