use super::compare::{
    compare_results_with_roots, fs_snapshots_match, mismatch_signature, replay_verdict_with_roots,
    MismatchSignature, ReplayVerdict,
};
use super::execution::{
    chmod_snapshot_post, chmod_snapshot_pre, prepare_controlled_chmod_variant, run_variant,
    snapshot_fs_post, snapshot_fs_pre, IdentityTransitionEvidence,
};
use super::fixture::{
    apply_fixture_modes, current_read_only_time_anchor, prepare_iteration_dirs,
    prepare_read_only_iteration_dirs_at, set_fixture_owner, stage_iteration_dirs,
};
use super::time_coverage::{CaseVerdict, EvaluatedComparison};
use super::{CompareResult, FsSnapshot, GeneratedCase, ResolvedPaths, RunResult, VariantKind};
use crate::utils::arg_semantics::should_consume_stdin_from_argv;
use crate::utils::capabilities::require_fuzz_capability;
use crate::utils::chmod_campaign::{
    canonical_environment_config, current_process_umask, selected_chmod_umask,
};
use crate::utils::cli::FuzzArgs;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::Duration;

#[derive(Debug, Clone)]
pub(crate) struct CaseEvaluation {
    pub(crate) case: GeneratedCase,
    pub(crate) reference: RunResult,
    pub(crate) dut: RunResult,
    pub(crate) comparison: EvaluatedComparison,
    pub(crate) mismatch_signature: Option<MismatchSignature>,
    pub(crate) replay_verdict: ReplayVerdict,
    pub(crate) pre_fs: FsSnapshot,
    pub(crate) dut_pre_fs: FsSnapshot,
    pub(crate) reference_fs: FsSnapshot,
    pub(crate) dut_fs: FsSnapshot,
    pub(crate) reference_identity: IdentityTransitionEvidence,
    pub(crate) dut_identity: IdentityTransitionEvidence,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RawCaseObservation {
    pub(crate) reference: RunResult,
    pub(crate) dut: RunResult,
    pub(crate) pre_fs: FsSnapshot,
    pub(crate) dut_pre_fs: FsSnapshot,
    pub(crate) reference_fs: FsSnapshot,
    pub(crate) dut_fs: FsSnapshot,
    pub(crate) reference_identity: IdentityTransitionEvidence,
    pub(crate) dut_identity: IdentityTransitionEvidence,
    pub(crate) reference_root: PathBuf,
    pub(crate) dut_root: PathBuf,
}

pub(crate) trait CaseExecutor {
    fn execute(
        &mut self,
        args: &FuzzArgs,
        seed: u64,
        child_iteration: usize,
        work_iteration: usize,
        case: &GeneratedCase,
    ) -> Result<RawCaseObservation, String>;
}

#[cfg(test)]
struct LocalCaseExecutor<'a> {
    paths: &'a ResolvedPaths,
    work_root: &'a Path,
    shared_root: Option<&'a Path>,
}

#[cfg(test)]
impl CaseExecutor for LocalCaseExecutor<'_> {
    fn execute(
        &mut self,
        args: &FuzzArgs,
        seed: u64,
        child_iteration: usize,
        work_iteration: usize,
        case: &GeneratedCase,
    ) -> Result<RawCaseObservation, String> {
        execute_case_in_work_dir(
            args,
            self.paths,
            self.work_root,
            self.shared_root,
            seed,
            child_iteration,
            work_iteration,
            case,
            None,
        )
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
struct ModeledReadTimeChanges {
    strict_changes: Vec<String>,
    symlink_atime_paths: BTreeSet<String>,
}

fn modeled_read_time_changes(pre: &FsSnapshot, post: &FsSnapshot) -> ModeledReadTimeChanges {
    let mut result = ModeledReadTimeChanges::default();
    for (path, before) in pre {
        let Some(after) = post.get(path) else {
            continue;
        };
        if before.kind == "inaccessible"
            || after.kind == "inaccessible"
            || before.host_key != after.host_key
        {
            continue;
        }
        let mut fields = Vec::new();
        if (before.times.atime_sec, before.times.atime_nsec)
            != (after.times.atime_sec, after.times.atime_nsec)
        {
            if before.kind == "symlink" && after.kind == "symlink" {
                result.symlink_atime_paths.insert(path.clone());
            } else {
                fields.push("atime");
            }
        }
        if (before.times.mtime_sec, before.times.mtime_nsec)
            != (after.times.mtime_sec, after.times.mtime_nsec)
        {
            fields.push("mtime");
        }
        if (before.times.ctime_sec, before.times.ctime_nsec)
            != (after.times.ctime_sec, after.times.ctime_nsec)
        {
            fields.push("ctime");
        }
        if !fields.is_empty() {
            result
                .strict_changes
                .push(format!("{path}: {}", fields.join(", ")));
        }
    }
    result
}

fn unexpected_dut_read_time_changes(
    reference: &ModeledReadTimeChanges,
    dut: &ModeledReadTimeChanges,
) -> Vec<String> {
    let mut changes = dut.strict_changes.clone();
    changes.extend(
        dut.symlink_atime_paths
            .difference(&reference.symlink_atime_paths)
            .map(|path| format!("{path}: atime")),
    );
    changes.sort();
    changes
}

pub(crate) fn read_only_timestamp_differences(
    util: &str,
    pre_fs: &FsSnapshot,
    ref_fs: &FsSnapshot,
    dut_pre_fs: &FsSnapshot,
    dut_fs: &FsSnapshot,
) -> Result<Vec<String>, String> {
    if matches!(util, "ls" | "stat") {
        let reference_changes = modeled_read_time_changes(pre_fs, ref_fs);
        if !reference_changes.strict_changes.is_empty() {
            return Err(format!(
                "reference {} changed modeled read-only timestamps: {}",
                util,
                reference_changes.strict_changes.join("; ")
            ));
        }
        let dut_changes = modeled_read_time_changes(dut_pre_fs, dut_fs);
        let dut_changes = unexpected_dut_read_time_changes(&reference_changes, &dut_changes)
            .into_iter()
            .map(|detail| format!("DUT changed read-only timestamps at {detail}"))
            .collect();
        return Ok(dut_changes);
    }
    Ok(Vec::new())
}

fn append_filesystem_differences(compare: &mut CompareResult, differences: Vec<String>) {
    if differences.is_empty() {
        return;
    }
    match compare {
        CompareResult::Match => {
            *compare = CompareResult::Mismatch {
                process_outcome_diff: None,
                stdout_diff: false,
                stderr_diff: false,
                fs_diff: differences,
            };
        }
        CompareResult::Mismatch { fs_diff, .. } => fs_diff.extend(differences),
    }
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn evaluate_case_with_seed(
    args: &FuzzArgs,
    paths: &ResolvedPaths,
    work_root: &Path,
    shared_root: Option<&Path>,
    seed: u64,
    iteration: usize,
    case: &GeneratedCase,
) -> Result<CaseEvaluation, String> {
    let mut executor = LocalCaseExecutor {
        paths,
        work_root,
        shared_root,
    };
    evaluate_case_with_executor(args, &mut executor, seed, iteration, iteration, case)
}

pub(crate) fn evaluate_case_with_executor(
    args: &FuzzArgs,
    executor: &mut dyn CaseExecutor,
    seed: u64,
    child_iteration: usize,
    work_iteration: usize,
    case: &GeneratedCase,
) -> Result<CaseEvaluation, String> {
    let observation = executor.execute(args, seed, child_iteration, work_iteration, case)?;
    finish_case_evaluation(args, case, observation)
}

#[cfg(test)]
pub(crate) fn evaluate_case(
    args: &FuzzArgs,
    paths: &ResolvedPaths,
    work_root: &Path,
    shared_root: Option<&Path>,
    iteration: usize,
    case: &GeneratedCase,
) -> Result<CaseEvaluation, String> {
    evaluate_case_with_seed(
        args,
        paths,
        work_root,
        shared_root,
        args.common.seed.unwrap_or_default(),
        iteration,
        case,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn execute_case_in_work_dir(
    args: &FuzzArgs,
    paths: &ResolvedPaths,
    work_root: &Path,
    shared_root: Option<&Path>,
    seed: u64,
    child_iteration: usize,
    work_iteration: usize,
    case: &GeneratedCase,
    target_identity: Option<(u32, u32)>,
) -> Result<RawCaseObservation, String> {
    let process_timeout = Duration::from_secs(args.process_timeout_seconds);
    let (
        ref_dir,
        dut_dir,
        pre_fs,
        dut_pre_fs,
        mut ref_observer,
        mut dut_observer,
        ref_result,
        dut_result,
    ) = if args.common.util == "chmod" {
        let (ref_dir, dut_dir) =
            stage_iteration_dirs(work_root, shared_root, work_iteration, &case.fixture, true)?;
        if let Some((uid, gid)) = target_identity {
            set_fixture_owner(&ref_dir, uid, gid)?;
            set_fixture_owner(&dut_dir, uid, gid)?;
        }
        let umask = selected_chmod_umask(seed, child_iteration);
        let environment = canonical_environment_config(umask)?;
        let reference = prepare_controlled_chmod_variant(
            VariantKind::Ref,
            paths,
            &case.argv,
            case.cwd.as_path(),
            ref_dir.as_path(),
            &environment,
            umask,
            target_identity,
        )?;
        let dut = prepare_controlled_chmod_variant(
            VariantKind::Dut,
            paths,
            &case.argv,
            case.cwd.as_path(),
            dut_dir.as_path(),
            &environment,
            umask,
            target_identity,
        )?;
        apply_fixture_modes(ref_dir.as_path(), &case.fixture)?;
        apply_fixture_modes(dut_dir.as_path(), &case.fixture)?;
        let (pre_fs, ref_observer) = chmod_snapshot_pre(ref_dir.as_path())?;
        let (dut_pre_fs, dut_observer) = chmod_snapshot_pre(dut_dir.as_path())?;
        if !fs_snapshots_match(&pre_fs, &dut_pre_fs, true)? {
            return Err(
                "reference and DUT fixtures differ after pre-state observation".to_string(),
            );
        }
        let ref_result = reference.go_and_collect(&case.stdin, process_timeout)?;
        let dut_result = dut.go_and_collect(&case.stdin, process_timeout)?;
        (
            ref_dir,
            dut_dir,
            pre_fs,
            dut_pre_fs,
            ref_observer,
            dut_observer,
            ref_result,
            dut_result,
        )
    } else {
        let (ref_dir, dut_dir) = if matches!(args.common.util.as_str(), "ls" | "stat") {
            let anchor = match args.read_only_time_anchor_seconds {
                Some(anchor) => anchor,
                None => current_read_only_time_anchor()?,
            };
            prepare_read_only_iteration_dirs_at(
                work_root,
                shared_root,
                work_iteration,
                &case.fixture,
                anchor,
            )?
        } else {
            prepare_iteration_dirs(work_root, shared_root, work_iteration, &case.fixture, false)?
        };
        if let Some((uid, gid)) = target_identity {
            set_fixture_owner(&ref_dir, uid, gid)?;
            set_fixture_owner(&dut_dir, uid, gid)?;
            apply_fixture_modes(&ref_dir, &case.fixture)?;
            apply_fixture_modes(&dut_dir, &case.fixture)?;
        }
        let (pre_fs, ref_observer) = snapshot_fs_pre(ref_dir.as_path())?;
        let (dut_pre_fs, dut_observer) = snapshot_fs_pre(dut_dir.as_path())?;
        if !fs_snapshots_match(&pre_fs, &dut_pre_fs, false)? {
            return Err("reference and DUT fixtures differ before execution".to_string());
        }
        let process_stdin = if should_consume_stdin_from_argv(&args.common.util, &case.argv) {
            case.stdin.as_slice()
        } else {
            &[]
        };
        let process_umask = match args.process_umask {
            Some(umask) => umask,
            None => current_process_umask()?,
        };
        let ref_result = run_variant(
            VariantKind::Ref,
            paths,
            &case.argv,
            process_stdin,
            case.cwd.as_path(),
            ref_dir.as_path(),
            process_umask,
            target_identity,
            process_timeout,
        )?;
        let dut_result = run_variant(
            VariantKind::Dut,
            paths,
            &case.argv,
            process_stdin,
            case.cwd.as_path(),
            dut_dir.as_path(),
            process_umask,
            target_identity,
            process_timeout,
        )?;
        (
            ref_dir,
            dut_dir,
            pre_fs,
            dut_pre_fs,
            ref_observer,
            dut_observer,
            ref_result,
            dut_result,
        )
    };

    let (ref_fs, reference_identity) = if args.common.util == "chmod" {
        chmod_snapshot_post(ref_dir.as_path(), &mut ref_observer)?
    } else {
        snapshot_fs_post(ref_dir.as_path(), &mut ref_observer)?
    };
    let (dut_fs, dut_identity) = if args.common.util == "chmod" {
        chmod_snapshot_post(dut_dir.as_path(), &mut dut_observer)?
    } else {
        snapshot_fs_post(dut_dir.as_path(), &mut dut_observer)?
    };
    Ok(RawCaseObservation {
        reference: ref_result,
        dut: dut_result,
        pre_fs,
        dut_pre_fs,
        reference_fs: ref_fs,
        dut_fs,
        reference_identity,
        dut_identity,
        reference_root: ref_dir,
        dut_root: dut_dir,
    })
}

fn finish_case_evaluation(
    args: &FuzzArgs,
    case: &GeneratedCase,
    observation: RawCaseObservation,
) -> Result<CaseEvaluation, String> {
    let RawCaseObservation {
        reference: ref_result,
        dut: dut_result,
        pre_fs,
        dut_pre_fs,
        reference_fs: ref_fs,
        dut_fs,
        reference_identity,
        dut_identity,
        reference_root: ref_dir,
        dut_root: dut_dir,
    } = observation;
    let mut compare = compare_results_with_roots(
        &args.common.util,
        &case.argv,
        &ref_result,
        &dut_result,
        &reference_identity,
        &ref_fs,
        &dut_identity,
        &dut_fs,
        args.ignore_stderr,
        Some(ref_dir.as_path()),
        Some(dut_dir.as_path()),
        Some(case.cwd.as_path()),
    )?;
    let time_differences =
        read_only_timestamp_differences(&args.common.util, &pre_fs, &ref_fs, &dut_pre_fs, &dut_fs)?;
    append_filesystem_differences(&mut compare, time_differences);
    let mismatch_signature = mismatch_signature(&compare, &reference_identity, &dut_identity);
    let replay_verdict = replay_verdict_with_roots(
        &args.common.util,
        &case.argv,
        &ref_result,
        &dut_result,
        &compare,
        &reference_identity,
        &dut_identity,
        &pre_fs,
        &dut_pre_fs,
        &ref_fs,
        &dut_fs,
        args.ignore_stderr,
        Some(ref_dir.as_path()),
        Some(dut_dir.as_path()),
        Some(case.cwd.as_path()),
    )?;

    Ok(CaseEvaluation {
        case: case.clone(),
        reference: ref_result,
        dut: dut_result,
        comparison: EvaluatedComparison::without_time_observations(
            compare,
            require_fuzz_capability(&args.common.util)?.time_coverage,
        ),
        mismatch_signature,
        replay_verdict,
        pre_fs,
        dut_pre_fs,
        reference_fs: ref_fs,
        dut_fs,
        reference_identity,
        dut_identity,
    })
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
fn evaluate_case_in_work_dir(
    args: &FuzzArgs,
    paths: &ResolvedPaths,
    work_root: &Path,
    shared_root: Option<&Path>,
    seed: u64,
    child_iteration: usize,
    work_iteration: usize,
    case: &GeneratedCase,
) -> Result<CaseEvaluation, String> {
    let observation = execute_case_in_work_dir(
        args,
        paths,
        work_root,
        shared_root,
        seed,
        child_iteration,
        work_iteration,
        case,
        None,
    )?;
    finish_case_evaluation(args, case, observation)
}

pub(crate) fn shrink_mismatch_with_executor(
    args: &FuzzArgs,
    executor: &mut dyn CaseExecutor,
    seed: u64,
    iteration: usize,
    original: CaseEvaluation,
    max_attempts: usize,
) -> Result<CaseEvaluation, String> {
    if max_attempts == 0 || original.comparison.verdict() != CaseVerdict::Mismatch {
        return Ok(original);
    }
    let Some(target_signature) = original.mismatch_signature else {
        return Ok(original);
    };

    let mut best = original;
    let mut attempts = 0usize;
    loop {
        let mut accepted = false;
        for candidate in reductions(&args.common.util, &best.case) {
            attempts += 1;
            if attempts > max_attempts {
                return Ok(best);
            }
            let work_iteration = iteration + 1_000_000 + attempts;
            let evaluation = evaluate_case_with_executor(
                args,
                executor,
                seed,
                iteration,
                work_iteration,
                &candidate,
            )?;
            if evaluation.comparison.verdict() == CaseVerdict::Mismatch
                && evaluation.mismatch_signature == Some(target_signature)
            {
                best = evaluation;
                accepted = true;
                break;
            }
        }
        if !accepted {
            break;
        }
    }
    Ok(best)
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn shrink_mismatch(
    args: &FuzzArgs,
    paths: &ResolvedPaths,
    work_root: &Path,
    shared_root: Option<&Path>,
    seed: u64,
    iteration: usize,
    original: CaseEvaluation,
    max_attempts: usize,
) -> Result<CaseEvaluation, String> {
    let mut executor = LocalCaseExecutor {
        paths,
        work_root,
        shared_root,
    };
    shrink_mismatch_with_executor(args, &mut executor, seed, iteration, original, max_attempts)
}

fn reductions(util: &str, case: &GeneratedCase) -> Vec<GeneratedCase> {
    let mut out = Vec::new();
    out.extend(reduce_argv(util, case));
    if util != "ls" || !super::input::ls_argv_requires_followed_entry_metadata(&case.argv) {
        out.extend(reduce_fixture(case));
    }
    out.extend(reduce_contents(case));
    out.extend(reduce_stdin(case));
    out.extend(reduce_cwd(case));
    out
}

fn reduce_argv(util: &str, case: &GeneratedCase) -> Vec<GeneratedCase> {
    if case.argv.len() <= 1 {
        return Vec::new();
    }
    let mut out = Vec::new();
    for idx in 0..case.argv.len() {
        let mut candidate = case.clone();
        candidate.argv.remove(idx);
        if candidate.argv != case.argv
            && (util != "ls" || super::input::ls_argv_respects_mode_dependencies(&candidate.argv))
        {
            out.push(candidate);
        }
    }
    out
}

pub(crate) fn reduce_fixture(case: &GeneratedCase) -> Vec<GeneratedCase> {
    let mut out = Vec::new();
    if !case.fixture.hardlinks.is_empty() {
        let mut candidate = case.clone();
        candidate.fixture.hardlinks.pop();
        out.push(candidate);
    }
    if !case.fixture.symlinks.is_empty() {
        let mut candidate = case.clone();
        let removed = candidate
            .fixture
            .symlinks
            .pop()
            .expect("symlink is present");
        candidate
            .fixture
            .hardlinks
            .retain(|link| link.source_relative_path != removed.relative_path);
        out.push(candidate);
    }
    if case.fixture.files.len() > 1 {
        let mut candidate = case.clone();
        let removed = candidate.fixture.files.pop().expect("file is present");
        candidate
            .fixture
            .hardlinks
            .retain(|link| link.source_relative_path != removed.relative_path);
        out.push(candidate);
    }
    if case.fixture.directories.len() > 1 {
        let mut candidate = case.clone();
        candidate.fixture.directories.pop();
        out.push(candidate);
    }
    out
}

fn reduce_contents(case: &GeneratedCase) -> Vec<GeneratedCase> {
    let mut out = Vec::new();
    for idx in 0..case.fixture.files.len() {
        let bytes = &case.fixture.files[idx].bytes;
        if bytes.is_empty() {
            continue;
        }
        let mut candidate = case.clone();
        candidate.fixture.files[idx].bytes.truncate(bytes.len() / 2);
        out.push(candidate);
    }
    out
}

fn reduce_stdin(case: &GeneratedCase) -> Vec<GeneratedCase> {
    if case.stdin.is_empty() {
        return Vec::new();
    }
    let mut candidate = case.clone();
    candidate.stdin.truncate(case.stdin.len() / 2);
    vec![candidate]
}

fn reduce_cwd(case: &GeneratedCase) -> Vec<GeneratedCase> {
    if case.cwd.as_os_str().is_empty() || case.cwd == Path::new(".") {
        return Vec::new();
    }
    let mut candidate = case.clone();
    candidate.cwd = ".".into();
    vec![candidate]
}

#[cfg(test)]
mod tests {
    use super::{
        append_filesystem_differences, evaluate_case_in_work_dir, fs_snapshots_match,
        modeled_read_time_changes, reduce_argv, reductions, shrink_mismatch,
        unexpected_dut_read_time_changes, CaseEvaluation, IdentityTransitionEvidence,
        MismatchSignature,
    };
    use crate::fuzz::execution::{
        chmod_snapshot_post, chmod_snapshot_pre, prepare_controlled_chmod_variant,
    };
    use crate::fuzz::fixture::{apply_fixture_modes, stage_iteration_dirs};
    use crate::fuzz::input::scenario_case;
    use crate::fuzz::{
        CompareResult, DirSpec, FileSpec, FixtureBlueprint, FsNodeSnapshot, FsSnapshot, FsTimes,
        GeneratedCase, HostInodeKeySnapshot, ResolvedPaths, ResolvedTarget, RunResult, SymlinkSpec,
        VariantKind,
    };
    use crate::utils::chmod_campaign::{canonical_environment_config, selected_chmod_umask};
    use crate::utils::cli::{Cli, CliCommand, ExecKind};
    use clap::Parser;
    use std::path::PathBuf;

    fn symlink_node(atime_sec: i64) -> FsNodeSnapshot {
        FsNodeSnapshot {
            raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
            kind: "symlink".to_string(),
            mode_octal: "0777".to_string(),
            times: FsTimes {
                atime_sec,
                atime_nsec: 0,
                mtime_sec: 20,
                mtime_nsec: 0,
                ctime_sec: 30,
                ctime_nsec: 0,
            },
            uid: None,
            gid: None,
            logical_size: None,
            allocated_512_blocks: None,
            preferred_io_block_bytes: None,
            target: "target".to_string(),
            data: Vec::new(),
            host_key: Some(HostInodeKeySnapshot {
                device: 1,
                inode: 3,
            }),
            link_count: Some(1),
        }
    }

    // A regular file changed by a read-only utility must report every modeled timestamp mutation.
    #[test]
    fn read_only_time_transition_detects_modeled_timestamp_mutation() {
        let before = FsNodeSnapshot {
            raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
            kind: "file".to_string(),
            mode_octal: "0644".to_string(),
            times: FsTimes {
                atime_sec: 10,
                atime_nsec: 0,
                mtime_sec: 20,
                mtime_nsec: 0,
                ctime_sec: 30,
                ctime_nsec: 0,
            },
            uid: None,
            gid: None,
            logical_size: None,
            allocated_512_blocks: None,
            preferred_io_block_bytes: None,
            target: String::new(),
            data: b"payload".to_vec(),
            host_key: Some(HostInodeKeySnapshot {
                device: 1,
                inode: 2,
            }),
            link_count: Some(1),
        };
        let mut after = before.clone();
        after.times.atime_sec = 99;
        after.times.mtime_sec = 21;
        after.times.ctime_sec = 31;
        let pre = FsSnapshot::from([("file".to_string(), before)]);
        let post = FsSnapshot::from([("file".to_string(), after)]);

        let changes = modeled_read_time_changes(&pre, &post);

        assert_eq!(changes.strict_changes, ["file: atime, mtime, ctime"]);
        assert!(changes.symlink_atime_paths.is_empty());
    }

    // A symbolic-link access-time change is separated while modification and change times remain strict.
    #[test]
    fn read_only_time_transition_partitions_symlink_atime() {
        let before = symlink_node(10);
        let mut after = before.clone();
        after.times.atime_sec = 99;
        after.times.mtime_sec = 21;
        after.times.ctime_sec = 31;
        let pre = FsSnapshot::from([("link".to_string(), before)]);
        let post = FsSnapshot::from([("link".to_string(), after)]);

        let changes = modeled_read_time_changes(&pre, &post);

        assert_eq!(changes.strict_changes, ["link: mtime, ctime"]);
        assert_eq!(changes.symlink_atime_paths.len(), 1);
        assert!(changes.symlink_atime_paths.contains("link"));
    }

    // 참조가 보존한 심볼릭 링크 접근 시각을 DUT만 바꾸면 파일 시스템 차이로 보고한다.
    #[test]
    fn dut_only_symlink_atime_change_becomes_filesystem_difference() {
        let before = symlink_node(10);
        let mut dut_after = before.clone();
        dut_after.times.atime_sec = 99;
        let pre = FsSnapshot::from([("link".to_string(), before.clone())]);
        let reference_post = FsSnapshot::from([("link".to_string(), before)]);
        let dut_post = FsSnapshot::from([("link".to_string(), dut_after)]);
        let reference_changes = modeled_read_time_changes(&pre, &reference_post);
        let dut_changes = modeled_read_time_changes(&pre, &dut_post);
        let differences = unexpected_dut_read_time_changes(&reference_changes, &dut_changes)
            .into_iter()
            .map(|detail| format!("DUT changed read-only timestamps at {detail}"))
            .collect();
        let mut compare = CompareResult::Match;

        append_filesystem_differences(&mut compare, differences);

        assert_eq!(
            compare,
            CompareResult::Mismatch {
                process_outcome_diff: None,
                stdout_diff: false,
                stderr_diff: false,
                fs_diff: vec!["DUT changed read-only timestamps at link: atime".to_string()],
            }
        );
    }

    // 같은 링크의 서로 다른 접근 시각은 원시 비교가 같아도 시간 검사를 완료하지 못한다.
    #[test]
    fn time_coverage_blocks_matching_symlink_atime_path_sets() {
        let before = symlink_node(10);
        let mut after = before.clone();
        after.times.atime_sec = 99;
        let pre = FsSnapshot::from([("link".to_string(), before)]);
        let post = FsSnapshot::from([("link".to_string(), after)]);
        let reference_changes = modeled_read_time_changes(&pre, &post);
        let mut dut_post = post.clone();
        dut_post.get_mut("link").unwrap().times.atime_sec = 123;
        let dut_changes = modeled_read_time_changes(&pre, &dut_post);
        let differences = unexpected_dut_read_time_changes(&reference_changes, &dut_changes)
            .into_iter()
            .map(|detail| format!("DUT changed read-only timestamps at {detail}"))
            .collect();
        let mut compare = CompareResult::Match;

        append_filesystem_differences(&mut compare, differences);

        assert_eq!(compare, CompareResult::Match);
        for util in ["ls", "stat"] {
            let comparison = super::EvaluatedComparison::without_time_observations(
                compare.clone(),
                crate::utils::capabilities::require_fuzz_capability(util)
                    .unwrap()
                    .time_coverage,
            );
            assert_eq!(comparison.verdict(), super::CaseVerdict::IncompleteCoverage);
        }
    }

    // ls 축소는 시각 선택자만 남겨 GNU의 암시 정렬 차이를 새 불일치로 만들지 않는다.
    #[test]
    fn ls_argv_shrink_preserves_time_selector_dependency() {
        let case = GeneratedCase {
            argv: vec!["-t".to_string(), "--time=status".to_string()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };

        let candidates = reduce_argv("ls", &case);

        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].argv, vec!["-t"]);
    }

    // Metadata-producing -L shrinking must not turn a valid implicit link into a dangling one.
    #[test]
    fn ls_followed_metadata_shrink_preserves_fixture_topology() {
        let case = GeneratedCase {
            argv: vec!["-L".to_string(), "-n".to_string()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: vec![FileSpec {
                    relative_path: PathBuf::from("target"),
                    bytes: b"payload".to_vec(),
                    mode: 0o644,
                }],
                symlinks: vec![SymlinkSpec {
                    relative_path: PathBuf::from("link"),
                    target: PathBuf::from("target"),
                }],
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };

        let candidates = reductions("ls", &case);

        assert!(candidates.iter().all(|candidate| {
            candidate.fixture.directories.len() == case.fixture.directories.len()
                && candidate.fixture.files.len() == case.fixture.files.len()
                && candidate.fixture.symlinks == case.fixture.symlinks
                && candidate.fixture.hardlinks == case.fixture.hardlinks
                && candidate.fixture.files[0].relative_path == case.fixture.files[0].relative_path
        }));
    }

    // A reduction evaluation failure must abort shrinking instead of being silently skipped.
    #[test]
    fn shrink_propagates_reduction_evaluation_error() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "true",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: PathBuf::from("/definitely/missing/reference"),
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: PathBuf::from("/bin/true"),
                label: "dut",
            },
        };
        let case = GeneratedCase {
            argv: vec!["first".to_string(), "second".to_string()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let identity = IdentityTransitionEvidence::new();
        let original = CaseEvaluation {
            case,
            reference: RunResult {
                termination: crate::fuzz::process_outcome::Termination::test_exit(0),
                stdout: Vec::new(),
                stderr: Vec::new(),
            },
            dut: RunResult {
                termination: crate::fuzz::process_outcome::Termination::test_exit(1),
                stdout: Vec::new(),
                stderr: Vec::new(),
            },
            comparison: super::EvaluatedComparison::without_time_observations(
                CompareResult::Mismatch {
                    process_outcome_diff: Some((
                        crate::fuzz::compare::ProcessOutcomeEvidence::Observed(
                            crate::fuzz::process_outcome::Termination::test_exit(0),
                        ),
                        crate::fuzz::compare::ProcessOutcomeEvidence::Observed(
                            crate::fuzz::process_outcome::Termination::test_exit(1),
                        ),
                    )),
                    stdout_diff: false,
                    stderr_diff: false,
                    fs_diff: Vec::new(),
                },
                crate::utils::capabilities::TimeCoverageRequirement::None,
            ),
            mismatch_signature: Some(MismatchSignature::ProcessOutcome),
            replay_verdict: crate::fuzz::compare::ReplayVerdict {
                comparison: CompareResult::Mismatch {
                    process_outcome_diff: Some((
                        crate::fuzz::compare::ProcessOutcomeEvidence::Observed(
                            crate::fuzz::process_outcome::Termination::test_exit(0),
                        ),
                        crate::fuzz::compare::ProcessOutcomeEvidence::Observed(
                            crate::fuzz::process_outcome::Termination::test_exit(1),
                        ),
                    )),
                    stdout_diff: false,
                    stderr_diff: false,
                    fs_diff: Vec::new(),
                },
                reference_process_outcome: crate::fuzz::compare::ProcessOutcomeEvidence::Observed(
                    crate::fuzz::process_outcome::Termination::test_exit(0),
                ),
                dut_process_outcome: crate::fuzz::compare::ProcessOutcomeEvidence::Observed(
                    crate::fuzz::process_outcome::Termination::test_exit(1),
                ),
                reference_stdout: crate::fuzz::compare::ReplayStreamEvidence::RawBytes(Vec::new()),
                dut_stdout: crate::fuzz::compare::ReplayStreamEvidence::RawBytes(Vec::new()),
                reference_stderr: crate::fuzz::compare::ReplayStreamEvidence::RawBytes(Vec::new()),
                dut_stderr: crate::fuzz::compare::ReplayStreamEvidence::RawBytes(Vec::new()),
                reference_identity: identity.clone(),
                dut_identity: identity.clone(),
                reference_pre_fs: crate::fuzz::compare::ReplayFsEvidence {
                    nodes: std::collections::BTreeMap::new(),
                    hardlink_aliases: std::collections::BTreeSet::new(),
                },
                dut_pre_fs: crate::fuzz::compare::ReplayFsEvidence {
                    nodes: std::collections::BTreeMap::new(),
                    hardlink_aliases: std::collections::BTreeSet::new(),
                },
                reference_post_fs: crate::fuzz::compare::ReplayFsEvidence {
                    nodes: std::collections::BTreeMap::new(),
                    hardlink_aliases: std::collections::BTreeSet::new(),
                },
                dut_post_fs: crate::fuzz::compare::ReplayFsEvidence {
                    nodes: std::collections::BTreeMap::new(),
                    hardlink_aliases: std::collections::BTreeSet::new(),
                },
            },
            pre_fs: FsSnapshot::new(),
            dut_pre_fs: FsSnapshot::new(),
            reference_fs: FsSnapshot::new(),
            dut_fs: FsSnapshot::new(),
            reference_identity: identity.clone(),
            dut_identity: identity,
        };
        let root = tempfile::tempdir().unwrap();

        let error =
            shrink_mismatch(&args, &paths, root.path(), None, 1, 0, original, 1).unwrap_err();

        assert!(error.contains("failed to run reference variant"), "{error}");
    }

    // Shrink work-directory numbering must not change the original seed/iteration umask schedule.
    #[cfg(unix)]
    #[test]
    fn chmod_shrink_preserves_original_child_configuration() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let case = GeneratedCase {
            argv: vec!["-c".to_string(), "umask".to_string()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let root = tempfile::tempdir().unwrap();

        let evaluation =
            evaluate_case_in_work_dir(&args, &paths, root.path(), None, 4, 3, 1_000_017, &case)
                .unwrap();

        assert_eq!(evaluation.reference.stdout, b"0022\n");
        assert_eq!(evaluation.reference, evaluation.dut);
    }

    // Pre-state observation must not give otherwise identical chmod roles different atimes.
    #[cfg(unix)]
    #[test]
    fn chmod_roles_start_from_identical_observed_filesystems() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/true"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let case = scenario_case("chmod", 0).unwrap();
        let root = tempfile::tempdir().unwrap();

        let evaluation =
            evaluate_case_in_work_dir(&args, &paths, root.path(), None, 1, 0, 0, &case).unwrap();

        assert!(fs_snapshots_match(&evaluation.pre_fs, &evaluation.reference_fs, true).unwrap());
        assert!(fs_snapshots_match(&evaluation.reference_fs, &evaluation.dut_fs, true).unwrap());
        assert_eq!(
            evaluation.comparison.observable,
            crate::fuzz::CompareResult::Match
        );
        assert_eq!(
            evaluation.comparison.verdict(),
            crate::fuzz::time_coverage::CaseVerdict::Match
        );
    }

    // A declared mode-zero cwd must not prevent either chmod role from launching there.
    #[cfg(unix)]
    #[test]
    fn chmod_roles_launch_from_declared_unsearchable_cwd() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/chmod"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let case = GeneratedCase {
            argv: vec!["--version".to_string()],
            fixture: FixtureBlueprint {
                directories: vec![DirSpec {
                    relative_path: PathBuf::from("d"),
                    mode: 0o000,
                }],
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("d"),
        };
        let root = tempfile::tempdir().unwrap();
        let (ref_dir, dut_dir) =
            stage_iteration_dirs(root.path(), None, 597, &case.fixture, true).unwrap();
        let umask = selected_chmod_umask(1, 597);
        let environment = canonical_environment_config(umask).unwrap();
        let reference = prepare_controlled_chmod_variant(
            VariantKind::Ref,
            &paths,
            &case.argv,
            &case.cwd,
            &ref_dir,
            &environment,
            umask,
            None,
        )
        .unwrap();
        let dut = prepare_controlled_chmod_variant(
            VariantKind::Dut,
            &paths,
            &case.argv,
            &case.cwd,
            &dut_dir,
            &environment,
            umask,
            None,
        )
        .unwrap();

        apply_fixture_modes(&ref_dir, &case.fixture).unwrap();
        apply_fixture_modes(&dut_dir, &case.fixture).unwrap();
        for role_dir in [&ref_dir, &dut_dir] {
            assert_eq!(
                fs::symlink_metadata(role_dir.join("d"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o7777,
                0o000
            );
        }
        let (pre_fs, mut ref_observer) = chmod_snapshot_pre(&ref_dir).unwrap();
        let (dut_pre_fs, mut dut_observer) = chmod_snapshot_pre(&dut_dir).unwrap();
        assert!(fs_snapshots_match(&pre_fs, &dut_pre_fs, true).unwrap());

        let reference_result = reference
            .go_and_collect(&case.stdin, std::time::Duration::from_secs(10))
            .unwrap();
        let dut_result = dut
            .go_and_collect(&case.stdin, std::time::Duration::from_secs(10))
            .unwrap();
        assert_eq!(reference_result, dut_result);
        let (reference_fs, _) = chmod_snapshot_post(&ref_dir, &mut ref_observer).unwrap();
        let (dut_fs, _) = chmod_snapshot_post(&dut_dir, &mut dut_observer).unwrap();
        assert!(fs_snapshots_match(&reference_fs, &dut_fs, true).unwrap());
        for role_dir in [&ref_dir, &dut_dir] {
            assert_eq!(
                fs::symlink_metadata(role_dir.join("d"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o7777,
                0o000
            );
        }

        let evaluation =
            evaluate_case_in_work_dir(&args, &paths, root.path(), None, 1, 597, 1_000_597, &case)
                .unwrap();

        assert_eq!(
            evaluation.comparison.observable,
            crate::fuzz::CompareResult::Match
        );
        assert_eq!(
            evaluation.comparison.verdict(),
            crate::fuzz::time_coverage::CaseVerdict::Match
        );
        for snapshot in [
            &evaluation.pre_fs,
            &evaluation.reference_fs,
            &evaluation.dut_fs,
        ] {
            assert_eq!(snapshot["d"].kind, "inaccessible");
            assert!(snapshot["d"].mode_octal.is_empty());
        }
        for role in ["ref", "dut"] {
            assert_eq!(
                fs::symlink_metadata(root.path().join("iter-1000597").join(role).join("d"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o7777,
                0o000
            );
        }
    }

    // Recursive chmod preserves controlled access/modification times without reversing change time.
    #[cfg(unix)]
    #[test]
    fn chmod_recursive_traversal_preserves_controlled_raw_times() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/chmod"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let case = GeneratedCase {
            argv: vec!["-R".to_string(), "0755".to_string(), "dir".to_string()],
            fixture: FixtureBlueprint {
                directories: vec![DirSpec {
                    relative_path: PathBuf::from("dir"),
                    mode: 0o700,
                }],
                files: vec![FileSpec {
                    relative_path: PathBuf::from("dir/a.txt"),
                    bytes: b"alpha\n".to_vec(),
                    mode: 0o600,
                }],
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let root = tempfile::tempdir().unwrap();

        let evaluation =
            evaluate_case_in_work_dir(&args, &paths, root.path(), None, 1, 7, 7, &case).unwrap();

        assert_eq!(
            evaluation.comparison.observable,
            crate::fuzz::CompareResult::Match
        );
        assert_eq!(
            evaluation.comparison.verdict(),
            crate::fuzz::time_coverage::CaseVerdict::Match
        );
        assert!(fs_snapshots_match(&evaluation.reference_fs, &evaluation.dut_fs, true).unwrap());
        assert_eq!(
            evaluation.reference_fs.keys().collect::<Vec<_>>(),
            evaluation.pre_fs.keys().collect::<Vec<_>>()
        );
        assert_eq!(evaluation.reference_fs["dir"].mode_octal, "0755");
        assert_eq!(evaluation.reference_fs["dir/a.txt"].data, b"alpha\n");
        let before = evaluation.pre_fs["dir"].times;
        let after = evaluation.reference_fs["dir"].times;
        assert_eq!(
            (after.atime_sec, after.atime_nsec),
            (before.atime_sec, before.atime_nsec)
        );
        assert_eq!(
            (after.mtime_sec, after.mtime_nsec),
            (before.mtime_sec, before.mtime_nsec)
        );
        assert!(
            (after.ctime_sec, after.ctime_nsec) >= (before.ctime_sec, before.ctime_nsec),
            "chmod must not move change time backward"
        );
    }

    // Newly visible chmod nodes expose the same controlled raw times from both fixture roles.
    #[cfg(unix)]
    #[test]
    fn chmod_newly_visible_nodes_reveal_controlled_fixture_times() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/chmod"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let case = scenario_case("chmod", 40).unwrap();
        let root = tempfile::tempdir().unwrap();

        let evaluation =
            evaluate_case_in_work_dir(&args, &paths, root.path(), None, 1, 40, 40, &case).unwrap();

        assert_eq!(evaluation.pre_fs["d"].kind, "inaccessible");
        assert!(!evaluation.pre_fs.contains_key("d/e"));
        assert_eq!(
            evaluation.comparison.observable,
            crate::fuzz::CompareResult::Match
        );
        assert_eq!(
            evaluation.comparison.verdict(),
            crate::fuzz::time_coverage::CaseVerdict::Match
        );
        assert!(fs_snapshots_match(&evaluation.reference_fs, &evaluation.dut_fs, true).unwrap());
        assert_eq!(evaluation.reference_fs["d"].mode_octal, "0700");
        assert_eq!(evaluation.reference_fs["d/e"].mode_octal, "0700");
        for path in ["d", "d/e"] {
            let times = evaluation.reference_fs[path].times;
            assert_eq!(
                (times.atime_sec, times.atime_nsec),
                (
                    super::super::execution::CONTROLLED_FIXTURE_ATIME_SEC,
                    super::super::execution::CONTROLLED_FIXTURE_TIME_NSEC,
                )
            );
            assert_eq!(
                (times.mtime_sec, times.mtime_nsec),
                (
                    super::super::execution::CONTROLLED_FIXTURE_MTIME_SEC,
                    super::super::execution::CONTROLLED_FIXTURE_TIME_NSEC,
                )
            );
        }
    }

    // An explicit DUT mtime mutation must remain visible in the raw exact post-state comparison.
    #[cfg(unix)]
    #[test]
    fn chmod_explicit_mtime_mutation_is_detected() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "chmod",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            panic!("expected fuzz command");
        };
        let root = tempfile::tempdir().unwrap();
        let dut = root.path().join("mutating-chmod");
        fs::write(
            &dut,
            "#!/bin/sh\n/bin/chmod \"$@\" && /usr/bin/touch -m -d @946684800 -- dir\n",
        )
        .unwrap();
        fs::set_permissions(&dut, fs::Permissions::from_mode(0o755)).unwrap();
        let paths = ResolvedPaths {
            reference: ResolvedTarget {
                kind: ExecKind::Native,
                path: PathBuf::from("/bin/chmod"),
                label: "reference",
            },
            dut: ResolvedTarget {
                kind: ExecKind::Native,
                path: dut,
                label: "dut",
            },
        };
        let case = GeneratedCase {
            argv: vec!["0755".to_string(), "dir".to_string()],
            fixture: FixtureBlueprint {
                directories: vec![DirSpec {
                    relative_path: PathBuf::from("dir"),
                    mode: 0o700,
                }],
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };

        let evaluation =
            evaluate_case_in_work_dir(&args, &paths, root.path(), None, 1, 0, 0, &case).unwrap();

        assert!(matches!(
            evaluation.comparison.observable,
            crate::fuzz::CompareResult::Mismatch { ref fs_diff, .. }
                if fs_diff == &["fs changed paths: dir"]
        ));
        assert_eq!(evaluation.dut_fs["dir"].times.mtime_sec, 946_684_800);
    }
}
