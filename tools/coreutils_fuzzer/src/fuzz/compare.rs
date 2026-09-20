use super::execution::IdentityTransitionEvidence;
use super::input::{
    ls_direct_ctime_case, ls_short_ctime_sort_case, LsDirectCtimeCase, LsDirectOperandFollow,
    LsShortCtimeSortCase,
};
use super::process_outcome::Termination;
use super::{CompareResult, DiffOp, FsNodeSnapshot, FsSnapshot, RunResult};
use crate::utils::arg_semantics::requests_help_or_version;
use crate::{fuzzer_outcome_marker, SEMANTIC_MISMATCH};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Component, Path, PathBuf};

#[allow(clippy::too_many_arguments)]
pub(crate) fn compare_results_with_roots(
    util: &str,
    argv: &[String],
    reference: &RunResult,
    dut: &RunResult,
    reference_identity: &IdentityTransitionEvidence,
    reference_fs: &FsSnapshot,
    dut_identity: &IdentityTransitionEvidence,
    dut_fs: &FsSnapshot,
    ignore_stderr: bool,
    reference_root: Option<&Path>,
    dut_root: Option<&Path>,
    cwd: Option<&Path>,
) -> Result<CompareResult, String> {
    let strict_chmod = util == "chmod";
    let requested_message_output = !strict_chmod && requests_help_or_version(util, argv);
    let process_outcome_diff = (reference.termination != dut.termination).then_some((
        ProcessOutcomeEvidence::Observed(reference.termination),
        ProcessOutcomeEvidence::Observed(dut.termination),
    ));
    let stdout_diff = if requested_message_output {
        streams_differ_by_presence(&reference.stdout, &dut.stdout)
    } else {
        stdout_streams_differ(
            util,
            argv,
            &reference.stdout,
            &dut.stdout,
            reference_fs,
            dut_fs,
            reference_root,
            dut_root,
            cwd,
        )
    };
    let stderr_diff = !ignore_stderr && stderr_streams_differ(util, &reference.stderr, &dut.stderr);
    let fs_diff = filesystem_comparison_details(
        reference_fs,
        dut_fs,
        reference_identity,
        dut_identity,
        strict_chmod,
    )?;
    Ok(comparison_from_components(
        process_outcome_diff,
        stdout_diff,
        stderr_diff,
        fs_diff,
    ))
}

fn comparison_from_components(
    process_outcome_diff: Option<(ProcessOutcomeEvidence, ProcessOutcomeEvidence)>,
    stdout_diff: bool,
    stderr_diff: bool,
    fs_diff: Vec<String>,
) -> CompareResult {
    if process_outcome_diff.is_none() && !stdout_diff && !stderr_diff && fs_diff.is_empty() {
        CompareResult::Match
    } else {
        CompareResult::Mismatch {
            process_outcome_diff,
            stdout_diff,
            stderr_diff,
            fs_diff,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum MismatchSignature {
    ProcessOutcome,
    Stdout,
    Stderr,
    IdentityTransition,
    Filesystem,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(untagged)]
pub(crate) enum ProcessOutcomeEvidence {
    Observed(Termination),
}

impl<'de> Deserialize<'de> for ProcessOutcomeEvidence {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Termination::deserialize(deserializer).map(Self::Observed)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ReplayStreamEvidence {
    Ignored,
    Presence(bool),
    CanonicalBytes(Vec<u8>),
    RawBytes(Vec<u8>),
    Records(Vec<Vec<u8>>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReplayFsNodeEvidence {
    pub(crate) raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson,
    pub(crate) kind: String,
    pub(crate) mode_octal: String,
    pub(crate) atime: Option<(i64, i64)>,
    pub(crate) mtime: Option<(i64, i64)>,
    pub(crate) atime_changed_from_pre: bool,
    pub(crate) mtime_changed_from_pre: bool,
    pub(crate) ctime_changed_from_pre: bool,
    pub(crate) uid: Option<u32>,
    pub(crate) gid: Option<u32>,
    pub(crate) logical_size: Option<u64>,
    pub(crate) allocated_512_blocks: Option<u64>,
    pub(crate) preferred_io_block_bytes: Option<u64>,
    pub(crate) target: String,
    pub(crate) data: Vec<u8>,
    pub(crate) link_count: Option<u64>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReplayFsEvidence {
    pub(crate) nodes: BTreeMap<String, ReplayFsNodeEvidence>,
    pub(crate) hardlink_aliases: BTreeSet<(String, String)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReplayVerdict {
    pub(crate) comparison: CompareResult,
    pub(crate) reference_process_outcome: ProcessOutcomeEvidence,
    pub(crate) dut_process_outcome: ProcessOutcomeEvidence,
    pub(crate) reference_stdout: ReplayStreamEvidence,
    pub(crate) dut_stdout: ReplayStreamEvidence,
    pub(crate) reference_stderr: ReplayStreamEvidence,
    pub(crate) dut_stderr: ReplayStreamEvidence,
    pub(crate) reference_identity: IdentityTransitionEvidence,
    pub(crate) dut_identity: IdentityTransitionEvidence,
    pub(crate) reference_pre_fs: ReplayFsEvidence,
    pub(crate) dut_pre_fs: ReplayFsEvidence,
    pub(crate) reference_post_fs: ReplayFsEvidence,
    pub(crate) dut_post_fs: ReplayFsEvidence,
}

impl ReplayVerdict {
    pub(crate) fn validate_process_outcome_consistency(&self) -> Result<(), String> {
        if let CompareResult::Mismatch {
            process_outcome_diff: Some((reference, dut)),
            ..
        } = self.comparison
        {
            if reference == dut {
                return Err("comparison process outcome difference contains equal outcomes".into());
            }
            if reference != self.reference_process_outcome || dut != self.dut_process_outcome {
                return Err(
                    "comparison process outcome difference disagrees with saved outcomes".into(),
                );
            }
        } else if self.reference_process_outcome != self.dut_process_outcome {
            return Err("saved process outcomes differ without a comparison difference".into());
        }
        Ok(())
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn replay_verdict_with_roots(
    util: &str,
    argv: &[String],
    reference: &RunResult,
    dut: &RunResult,
    compare: &CompareResult,
    reference_identity: &IdentityTransitionEvidence,
    dut_identity: &IdentityTransitionEvidence,
    reference_pre_fs: &FsSnapshot,
    dut_pre_fs: &FsSnapshot,
    reference_post_fs: &FsSnapshot,
    dut_post_fs: &FsSnapshot,
    ignore_stderr: bool,
    reference_root: Option<&Path>,
    dut_root: Option<&Path>,
    cwd: Option<&Path>,
) -> Result<ReplayVerdict, String> {
    let requested_message_output = util != "chmod" && requests_help_or_version(util, argv);
    let (reference_stdout, dut_stdout) = if requested_message_output {
        (
            ReplayStreamEvidence::Presence(!reference.stdout.is_empty()),
            ReplayStreamEvidence::Presence(!dut.stdout.is_empty()),
        )
    } else {
        replay_stdout_evidence(
            util,
            argv,
            &reference.stdout,
            &dut.stdout,
            reference_post_fs,
            dut_post_fs,
            reference_root,
            dut_root,
            cwd,
        )
    };
    let (reference_stderr, dut_stderr) = if ignore_stderr {
        (ReplayStreamEvidence::Ignored, ReplayStreamEvidence::Ignored)
    } else {
        replay_stderr_evidence(util, &reference.stderr, &dut.stderr)
    };
    let include_times = matches!(util, "chmod" | "ls" | "stat");
    Ok(ReplayVerdict {
        comparison: compare.clone(),
        reference_process_outcome: ProcessOutcomeEvidence::Observed(reference.termination),
        dut_process_outcome: ProcessOutcomeEvidence::Observed(dut.termination),
        reference_stdout,
        dut_stdout,
        reference_stderr,
        dut_stderr,
        reference_identity: reference_identity.clone(),
        dut_identity: dut_identity.clone(),
        reference_pre_fs: replay_fs_evidence(
            reference_pre_fs,
            None,
            include_times,
            "reference pre",
        )?,
        dut_pre_fs: replay_fs_evidence(dut_pre_fs, None, include_times, "DUT pre")?,
        reference_post_fs: replay_fs_evidence(
            reference_post_fs,
            Some(reference_pre_fs),
            include_times,
            "reference post",
        )?,
        dut_post_fs: replay_fs_evidence(dut_post_fs, Some(dut_pre_fs), include_times, "DUT post")?,
    })
}

fn replay_fs_evidence(
    snapshot: &FsSnapshot,
    pre_snapshot: Option<&FsSnapshot>,
    include_times: bool,
    label: &str,
) -> Result<ReplayFsEvidence, String> {
    let nodes = snapshot
        .iter()
        .map(|(path, node)| {
            let pre = pre_snapshot.and_then(|snapshot| snapshot.get(path));
            let atime_changed_from_pre = include_times
                && pre.is_some_and(|before| {
                    (before.times.atime_sec, before.times.atime_nsec)
                        != (node.times.atime_sec, node.times.atime_nsec)
                });
            let mtime_changed_from_pre = include_times
                && pre.is_some_and(|before| {
                    (before.times.mtime_sec, before.times.mtime_nsec)
                        != (node.times.mtime_sec, node.times.mtime_nsec)
                });
            let ctime_changed_from_pre = include_times
                && pre.is_some_and(|before| {
                    (before.times.ctime_sec, before.times.ctime_nsec)
                        != (node.times.ctime_sec, node.times.ctime_nsec)
                });
            (
                path.clone(),
                ReplayFsNodeEvidence {
                    raw_stat_metadata: node.raw_stat_metadata,
                    kind: node.kind.to_string(),
                    mode_octal: node.mode_octal.clone(),
                    atime: (include_times && !atime_changed_from_pre)
                        .then_some((node.times.atime_sec, node.times.atime_nsec)),
                    mtime: (include_times && !mtime_changed_from_pre)
                        .then_some((node.times.mtime_sec, node.times.mtime_nsec)),
                    atime_changed_from_pre,
                    mtime_changed_from_pre,
                    ctime_changed_from_pre,
                    uid: node.uid,
                    gid: node.gid,
                    logical_size: node.logical_size,
                    allocated_512_blocks: node.allocated_512_blocks,
                    preferred_io_block_bytes: node.preferred_io_block_bytes,
                    target: node.target.clone(),
                    data: node.data.clone(),
                    link_count: node.link_count,
                },
            )
        })
        .collect();
    Ok(ReplayFsEvidence {
        nodes,
        hardlink_aliases: alias_partition(snapshot, label)?,
    })
}

pub(crate) fn mismatch_signature(
    compare: &CompareResult,
    reference_identity: &IdentityTransitionEvidence,
    dut_identity: &IdentityTransitionEvidence,
) -> Option<MismatchSignature> {
    match compare {
        CompareResult::Match => None,
        CompareResult::Mismatch {
            process_outcome_diff,
            stdout_diff,
            stderr_diff,
            fs_diff,
        } => {
            if process_outcome_diff.is_some() {
                Some(MismatchSignature::ProcessOutcome)
            } else if *stdout_diff {
                Some(MismatchSignature::Stdout)
            } else if *stderr_diff {
                Some(MismatchSignature::Stderr)
            } else if reference_identity != dut_identity {
                Some(MismatchSignature::IdentityTransition)
            } else if !fs_diff.is_empty() {
                Some(MismatchSignature::Filesystem)
            } else {
                None
            }
        }
    }
}

pub(crate) fn report_mismatch(
    seed: u64,
    iteration: usize,
    util: &str,
    argv: &[String],
    reference: &RunResult,
    dut: &RunResult,
    compare: &CompareResult,
) {
    eprintln!("{}", fuzzer_outcome_marker(SEMANTIC_MISMATCH));
    eprintln!("Mismatch detected");
    eprintln!("  util={util} seed={seed} iteration={iteration}");
    eprintln!("  argv={argv:?}");
    if let CompareResult::Mismatch {
        process_outcome_diff,
        stdout_diff,
        stderr_diff,
        fs_diff,
    } = compare
    {
        if let Some((r, d)) = process_outcome_diff {
            eprintln!("  process_outcome ref={r:?} dut={d:?}");
        }
        if *stdout_diff {
            eprintln!("  stdout differs");
            eprintln!(
                "{}",
                render_text_diff("stdout", &reference.stdout, &dut.stdout)
            );
        }
        if *stderr_diff {
            eprintln!("  stderr differs");
            eprintln!(
                "{}",
                render_text_diff("stderr", &reference.stderr, &dut.stderr)
            );
        }
        if !fs_diff.is_empty() {
            eprintln!("  filesystem differs");
            for detail in fs_diff {
                eprintln!("    - {detail}");
            }
        }
    }
}

pub(crate) fn render_text_diff(stream_name: &str, reference: &[u8], dut: &[u8]) -> String {
    let left_lines = bytes_to_diff_lines(reference);
    let right_lines = bytes_to_diff_lines(dut);
    let ops = diff_lines(&left_lines, &right_lines);
    let mut out = String::new();
    let _ = writeln!(out, "--- ref/{stream_name} ({} bytes)", reference.len());
    let _ = writeln!(out, "+++ dut/{stream_name} ({} bytes)", dut.len());
    out.push_str("@@\n");
    for op in ops {
        match op {
            DiffOp::Equal(line) => {
                let _ = writeln!(out, " {line}");
            }
            DiffOp::Remove(line) => {
                let _ = writeln!(out, "-{line}");
            }
            DiffOp::Add(line) => {
                let _ = writeln!(out, "+{line}");
            }
        }
    }
    out
}

fn filesystem_comparison_details(
    reference: &FsSnapshot,
    dut: &FsSnapshot,
    reference_identity: &IdentityTransitionEvidence,
    dut_identity: &IdentityTransitionEvidence,
    compare_times: bool,
) -> Result<Vec<String>, String> {
    let mut differences = fs_diff_details(reference, dut, compare_times)?;
    if reference_identity != dut_identity {
        differences.push("fs identity transition partition differs".to_string());
    }
    Ok(differences)
}

fn fs_diff_details(
    reference: &FsSnapshot,
    dut: &FsSnapshot,
    compare_times: bool,
) -> Result<Vec<String>, String> {
    let reference_keys: BTreeSet<&String> = reference.keys().collect();
    let dut_keys: BTreeSet<&String> = dut.keys().collect();

    let added: Vec<String> = dut_keys
        .difference(&reference_keys)
        .map(|s| (*s).clone())
        .collect();
    let removed: Vec<String> = reference_keys
        .difference(&dut_keys)
        .map(|s| (*s).clone())
        .collect();
    let changed: Vec<String> = reference_keys
        .intersection(&dut_keys)
        .filter_map(|key| {
            if !fs_nodes_match(
                reference.get(*key).expect("reference key is present"),
                dut.get(*key).expect("dut key is present"),
                compare_times,
            ) {
                Some((*key).clone())
            } else {
                None
            }
        })
        .collect();

    let mut details = Vec::new();
    if !added.is_empty() {
        details.push(format!("fs added paths: {}", added.join(", ")));
    }
    if !removed.is_empty() {
        details.push(format!("fs removed paths: {}", removed.join(", ")));
    }
    if !changed.is_empty() {
        details.push(format!("fs changed paths: {}", changed.join(", ")));
    }
    if alias_partition(reference, "reference")? != alias_partition(dut, "DUT")? {
        details.push("fs hardlink alias partition differs".to_string());
    }
    Ok(details)
}

pub(crate) fn fs_snapshots_match(
    reference: &FsSnapshot,
    dut: &FsSnapshot,
    compare_times: bool,
) -> Result<bool, String> {
    Ok(fs_diff_details(reference, dut, compare_times)?.is_empty())
}

fn paths_by_host_key<'a>(
    snapshot: &'a FsSnapshot,
    label: &str,
) -> Result<BTreeMap<super::HostInodeKeySnapshot, Vec<&'a String>>, String> {
    let mut paths_by_key = BTreeMap::new();
    for (path, node) in snapshot {
        let host_key = node
            .host_key
            .ok_or_else(|| format!("fs.identity unsupported: {label} path `{path}`"))?;
        paths_by_key
            .entry(host_key)
            .or_insert_with(Vec::new)
            .push(path);
    }
    Ok(paths_by_key)
}

fn alias_partition(
    snapshot: &FsSnapshot,
    label: &str,
) -> Result<BTreeSet<(String, String)>, String> {
    let mut pairs = BTreeSet::new();
    for paths in paths_by_host_key(snapshot, label)?.into_values() {
        for (index, left) in paths.iter().enumerate() {
            for right in &paths[index + 1..] {
                pairs.insert(((*left).clone(), (*right).clone()));
            }
        }
    }
    Ok(pairs)
}

fn fs_nodes_match(reference: &FsNodeSnapshot, dut: &FsNodeSnapshot, compare_times: bool) -> bool {
    let mut reference_without_times = reference.clone();
    let mut dut_without_times = dut.clone();
    reference_without_times.host_key = None;
    dut_without_times.host_key = None;
    // Clone creation gives corresponding nodes unrelated raw ctimes. Read-only
    // invariance is checked within each clone, so only atime/mtime compare here.
    reference_without_times.times.ctime_sec = dut_without_times.times.ctime_sec;
    reference_without_times.times.ctime_nsec = dut_without_times.times.ctime_nsec;
    if compare_times {
        return reference_without_times == dut_without_times;
    }
    reference_without_times.times = dut_without_times.times;
    reference_without_times == dut_without_times
}

fn streams_differ_by_presence(reference: &[u8], dut: &[u8]) -> bool {
    reference.is_empty() != dut.is_empty()
}

fn stderr_streams_differ(util: &str, reference: &[u8], dut: &[u8]) -> bool {
    if util == "ls" {
        const UNMODELED_GNU_TIME_SELECTOR: &[u8] = b"  - 'birth', 'creation'\n";
        let reference = reference
            .windows(UNMODELED_GNU_TIME_SELECTOR.len())
            .position(|window| window == UNMODELED_GNU_TIME_SELECTOR)
            .map(|offset| {
                [
                    &reference[..offset],
                    &reference[offset + UNMODELED_GNU_TIME_SELECTOR.len()..],
                ]
                .concat()
            });
        if let Some(reference) = reference {
            return reference != dut;
        }
    }
    reference != dut
}

fn replay_stderr_evidence(
    util: &str,
    reference: &[u8],
    dut: &[u8],
) -> (ReplayStreamEvidence, ReplayStreamEvidence) {
    if util == "ls" {
        const UNMODELED_GNU_TIME_SELECTOR: &[u8] = b"  - 'birth', 'creation'\n";
        let reference = reference
            .windows(UNMODELED_GNU_TIME_SELECTOR.len())
            .position(|window| window == UNMODELED_GNU_TIME_SELECTOR)
            .map_or_else(
                || reference.to_vec(),
                |offset| {
                    [
                        &reference[..offset],
                        &reference[offset + UNMODELED_GNU_TIME_SELECTOR.len()..],
                    ]
                    .concat()
                },
            );
        return (
            ReplayStreamEvidence::CanonicalBytes(reference),
            ReplayStreamEvidence::CanonicalBytes(dut.to_vec()),
        );
    }
    (
        ReplayStreamEvidence::RawBytes(reference.to_vec()),
        ReplayStreamEvidence::RawBytes(dut.to_vec()),
    )
}

#[allow(clippy::too_many_arguments)]
fn replay_stdout_evidence(
    util: &str,
    argv: &[String],
    reference: &[u8],
    dut: &[u8],
    reference_fs: &FsSnapshot,
    dut_fs: &FsSnapshot,
    reference_root: Option<&Path>,
    dut_root: Option<&Path>,
    cwd: Option<&Path>,
) -> (ReplayStreamEvidence, ReplayStreamEvidence) {
    if util == "printenv" {
        if let Some(separator) = printenv_environment_separator(argv) {
            return (
                ReplayStreamEvidence::Records(normalized_printenv_records(reference, separator)),
                ReplayStreamEvidence::Records(normalized_printenv_records(dut, separator)),
            );
        }
    }
    if util == "pwd" {
        if let (Some(reference_root), Some(dut_root)) = (reference_root, dut_root) {
            return (
                ReplayStreamEvidence::CanonicalBytes(normalized_pwd_output(
                    reference,
                    reference_root,
                )),
                ReplayStreamEvidence::CanonicalBytes(normalized_pwd_output(dut, dut_root)),
            );
        }
    }
    if util == "stat" {
        if let Some(evidence) =
            replay_stat_stdout_evidence(argv, reference, dut, reference_fs, dut_fs, cwd)
        {
            return evidence;
        }
    }
    if util == "ls" {
        if let Some(evidence) =
            replay_ls_stdout_evidence(argv, reference, dut, reference_fs, dut_fs, cwd)
        {
            return evidence;
        }
    }
    (
        ReplayStreamEvidence::RawBytes(reference.to_vec()),
        ReplayStreamEvidence::RawBytes(dut.to_vec()),
    )
}

#[allow(clippy::too_many_arguments)]
fn stdout_streams_differ(
    util: &str,
    argv: &[String],
    reference: &[u8],
    dut: &[u8],
    reference_fs: &FsSnapshot,
    dut_fs: &FsSnapshot,
    reference_root: Option<&Path>,
    dut_root: Option<&Path>,
    cwd: Option<&Path>,
) -> bool {
    if util == "printenv" {
        if let Some(separator) = printenv_environment_separator(argv) {
            return normalized_printenv_records(reference, separator)
                != normalized_printenv_records(dut, separator);
        }
    }
    if util == "pwd" {
        if let (Some(reference_root), Some(dut_root)) = (reference_root, dut_root) {
            return normalized_pwd_output(reference, reference_root)
                != normalized_pwd_output(dut, dut_root);
        }
    }
    if util == "stat" {
        if let Some(differs) =
            stat_stdout_streams_differ(argv, reference, dut, reference_fs, dut_fs, cwd)
        {
            return differs;
        }
    }
    if util == "ls" {
        if let Some(differs) =
            ls_stdout_streams_differ(argv, reference, dut, reference_fs, dut_fs, cwd)
        {
            return differs;
        }
    }
    reference != dut
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LsTimeColumns {
    DefaultC,
    FullIso,
    LongIso,
    Iso,
    EpochSeconds,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LsColumnOptions {
    numeric_long: bool,
    show_blocks: bool,
    time_columns: LsTimeColumns,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LsColumnSource {
    Reference,
    Dut,
}

fn ls_stdout_streams_differ(
    argv: &[String],
    reference: &[u8],
    dut: &[u8],
    reference_fs: &FsSnapshot,
    dut_fs: &FsSnapshot,
    cwd: Option<&Path>,
) -> Option<bool> {
    let options = ls_column_options(argv)?;
    if let Some(invocation) = ls_short_ctime_sort_case(argv) {
        let reference_expected = expected_ls_short_ctime_output(reference_fs, cwd?, invocation)?;
        let dut_expected = expected_ls_short_ctime_output(dut_fs, cwd?, invocation)?;
        return Some(reference != reference_expected || dut != dut_expected);
    }
    if !options.numeric_long && !options.show_blocks {
        return None;
    }

    if let Some(invocation) = ls_direct_ctime_case(argv) {
        let reference_ctime = ls_direct_operand_ctime(reference_fs, cwd?, invocation)?;
        let dut_ctime = ls_direct_operand_ctime(dut_fs, cwd?, invocation)?;
        let Some(dut_canonical) = normalize_ls_column_output(dut, options, LsColumnSource::Dut)
        else {
            return Some(true);
        };
        if dut_canonical != dut {
            return Some(true);
        }
        return match (
            normalize_ls_direct_ctime_output(
                reference,
                options,
                reference_ctime,
                LsColumnSource::Reference,
            ),
            normalize_ls_direct_ctime_output(dut, options, dut_ctime, LsColumnSource::Dut),
        ) {
            (Ok(reference), Ok(dut)) => Some(reference != dut),
            (Err(LsOutputNormalizationError::MetadataMismatch), _)
            | (_, Err(LsOutputNormalizationError::MetadataMismatch)) => Some(true),
            (Ok(_), Err(LsOutputNormalizationError::Ambiguous)) => Some(true),
            (Err(LsOutputNormalizationError::Ambiguous), _) => None,
        };
    }

    let reference = normalize_ls_column_output(reference, options, LsColumnSource::Reference)?;
    let Some(dut_normalized) = normalize_ls_column_output(dut, options, LsColumnSource::Dut) else {
        return Some(true);
    };
    Some(dut_normalized != dut || reference != dut_normalized)
}

fn replay_ls_stdout_evidence(
    argv: &[String],
    reference: &[u8],
    dut: &[u8],
    reference_fs: &FsSnapshot,
    dut_fs: &FsSnapshot,
    cwd: Option<&Path>,
) -> Option<(ReplayStreamEvidence, ReplayStreamEvidence)> {
    let options = ls_column_options(argv)?;
    if ls_short_ctime_sort_case(argv).is_some() {
        return Some((
            ReplayStreamEvidence::RawBytes(reference.to_vec()),
            ReplayStreamEvidence::RawBytes(dut.to_vec()),
        ));
    }
    if !options.numeric_long && !options.show_blocks {
        return None;
    }

    if let Some(invocation) = ls_direct_ctime_case(argv) {
        let reference_ctime = ls_direct_operand_ctime(reference_fs, cwd?, invocation)?;
        let dut_ctime = ls_direct_operand_ctime(dut_fs, cwd?, invocation)?;
        return Some((
            replay_ls_direct_stream(
                reference,
                options,
                reference_ctime,
                LsColumnSource::Reference,
            ),
            replay_ls_direct_stream(dut, options, dut_ctime, LsColumnSource::Dut),
        ));
    }

    Some((
        normalize_ls_column_output(reference, options, LsColumnSource::Reference).map_or_else(
            || ReplayStreamEvidence::RawBytes(reference.to_vec()),
            ReplayStreamEvidence::CanonicalBytes,
        ),
        normalize_ls_column_output(dut, options, LsColumnSource::Dut).map_or_else(
            || ReplayStreamEvidence::RawBytes(dut.to_vec()),
            ReplayStreamEvidence::CanonicalBytes,
        ),
    ))
}

fn replay_ls_direct_stream(
    data: &[u8],
    options: LsColumnOptions,
    expected_ctime: i64,
    source: LsColumnSource,
) -> ReplayStreamEvidence {
    normalize_ls_direct_ctime_output(data, options, expected_ctime, source).map_or_else(
        |_| ReplayStreamEvidence::RawBytes(data.to_vec()),
        ReplayStreamEvidence::CanonicalBytes,
    )
}

fn expected_ls_short_ctime_output(
    snapshot: &FsSnapshot,
    cwd: &Path,
    invocation: LsShortCtimeSortCase,
) -> Option<Vec<u8>> {
    let directory = snapshot_relative_key(cwd, ".")?;
    let mut entries = Vec::new();
    for (path, node) in snapshot {
        let path = Path::new(path);
        if normalized_snapshot_key(path.parent()?)? != directory {
            continue;
        }
        let name = path.file_name()?.to_str()?.as_bytes();
        if name.starts_with(b".") {
            continue;
        }
        entries.push(((node.times.ctime_sec, node.times.ctime_nsec), name.to_vec()));
    }

    entries.sort_by(|left, right| right.0.cmp(&left.0).then_with(|| left.1.cmp(&right.1)));
    if invocation.reverse {
        entries.reverse();
    }

    let mut output = Vec::new();
    for (_, name) in entries {
        output.extend_from_slice(&name);
        output.push(b'\n');
    }
    Some(output)
}

fn ls_direct_operand_ctime(
    snapshot: &FsSnapshot,
    cwd: &Path,
    invocation: LsDirectCtimeCase<'_>,
) -> Option<i64> {
    let key = snapshot_relative_key(cwd, invocation.operand)?;
    let follow = invocation.follow == LsDirectOperandFollow::Follow;
    Some(snapshot_node(snapshot, &key, follow)?.times.ctime_sec)
}

fn ls_column_options(argv: &[String]) -> Option<LsColumnOptions> {
    let mut result = LsColumnOptions {
        numeric_long: false,
        show_blocks: false,
        time_columns: LsTimeColumns::DefaultC,
    };
    let mut index = 0;
    while index < argv.len() {
        let arg = argv[index].as_str();
        if arg == "--" {
            break;
        }
        match arg {
            "--all"
            | "--almost-all"
            | "--directory"
            | "--reverse"
            | "--dereference-command-line"
            | "--dereference"
            | "--recursive"
            | "--help"
            | "--version" => {}
            "--numeric-uid-gid" => result.numeric_long = true,
            "--size" => result.show_blocks = true,
            "--time" => {
                index += 1;
                if !ls_selects_modeled_time(argv.get(index)?.as_str()) {
                    return None;
                }
            }
            "--time-style" => {
                index += 1;
                result.time_columns = ls_time_columns(argv.get(index)?.as_str())?;
            }
            "--block-size" => {
                index += 1;
                if !ls_positive_decimal(argv.get(index)?.as_str()) {
                    return None;
                }
            }
            _ => {
                if let Some(value) = arg.strip_prefix("--time=") {
                    if !ls_selects_modeled_time(value) {
                        return None;
                    }
                } else if let Some(value) = arg.strip_prefix("--time-style=") {
                    result.time_columns = ls_time_columns(value)?;
                } else if let Some(value) = arg.strip_prefix("--block-size=") {
                    if !ls_positive_decimal(value) {
                        return None;
                    }
                } else if let Some(shorts) = arg.strip_prefix('-') {
                    if shorts.starts_with('-')
                        || !shorts.chars().all(|short| {
                            matches!(
                                short,
                                'a' | 'A'
                                    | 'd'
                                    | 'n'
                                    | 's'
                                    | 'S'
                                    | 't'
                                    | 'r'
                                    | 'u'
                                    | 'c'
                                    | 'H'
                                    | 'L'
                                    | 'R'
                            )
                        })
                    {
                        return None;
                    }
                    result.numeric_long |= shorts.contains('n');
                    result.show_blocks |= shorts.contains('s');
                } else if arg.starts_with('-') {
                    return None;
                }
            }
        }
        index += 1;
    }
    Some(result)
}

fn ls_selects_modeled_time(value: &str) -> bool {
    matches!(
        value,
        "atime" | "access" | "use" | "ctime" | "status" | "mtime" | "modification"
    )
}

fn ls_time_columns(value: &str) -> Option<LsTimeColumns> {
    match value {
        "+%s" => Some(LsTimeColumns::EpochSeconds),
        "full-iso" => Some(LsTimeColumns::FullIso),
        "long-iso" => Some(LsTimeColumns::LongIso),
        "iso" => Some(LsTimeColumns::Iso),
        "locale" | "posix-full-iso" | "posix-long-iso" | "posix-iso" | "posix-locale" => {
            Some(LsTimeColumns::DefaultC)
        }
        _ => None,
    }
}

fn ls_positive_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.bytes().all(|byte| byte.is_ascii_digit())
        && value.bytes().any(|byte| byte != b'0')
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LsOutputNormalizationError {
    Ambiguous,
    MetadataMismatch,
}

fn normalize_ls_column_output(
    data: &[u8],
    options: LsColumnOptions,
    source: LsColumnSource,
) -> Option<Vec<u8>> {
    if data.is_empty() {
        return Some(Vec::new());
    }
    if !data.ends_with(b"\n") {
        return None;
    }

    let mut normalized = Vec::with_capacity(data.len());
    let mut start = 0;
    while start < data.len() {
        let newline = data.get(start..)?.iter().position(|byte| *byte == b'\n')? + start;
        let line = data.get(start..newline)?;
        if line.starts_with(b"total ") {
            normalize_ls_total_line(line, &mut normalized)?;
        } else if options.numeric_long {
            normalize_ls_long_line(line, options, None, source, &mut normalized).ok()?;
        } else if options.show_blocks {
            normalize_ls_block_line(line, &mut normalized)?;
        } else {
            normalized.extend_from_slice(line);
        }
        normalized.push(b'\n');
        start = newline + 1;
    }
    Some(normalized)
}

fn normalize_ls_direct_ctime_output(
    data: &[u8],
    options: LsColumnOptions,
    expected_ctime: i64,
    source: LsColumnSource,
) -> Result<Vec<u8>, LsOutputNormalizationError> {
    if !options.numeric_long
        || options.show_blocks
        || options.time_columns != LsTimeColumns::EpochSeconds
    {
        return Err(LsOutputNormalizationError::Ambiguous);
    }
    let line = data
        .strip_suffix(b"\n")
        .ok_or(LsOutputNormalizationError::Ambiguous)?;
    if line.is_empty() || line.contains(&b'\n') {
        return Err(LsOutputNormalizationError::Ambiguous);
    }

    let mut normalized = Vec::with_capacity(data.len());
    normalize_ls_long_line(line, options, Some(expected_ctime), source, &mut normalized)?;
    normalized.push(b'\n');
    Ok(normalized)
}

fn normalize_ls_total_line(line: &[u8], normalized: &mut Vec<u8>) -> Option<()> {
    let value = line.strip_prefix(b"total ")?;
    if !ascii_unsigned(value) {
        return None;
    }
    normalized.extend_from_slice(b"total ");
    normalized.extend_from_slice(value);
    Some(())
}

fn normalize_ls_block_line(line: &[u8], normalized: &mut Vec<u8>) -> Option<()> {
    if line.is_empty() || line.ends_with(b":") {
        normalized.extend_from_slice(line);
        return Some(());
    }
    let mut cursor = 0;
    let blocks = take_ascii_space_token(line, &mut cursor)?;
    if !ascii_unsigned(blocks) {
        return None;
    }
    let name = remaining_after_one_ascii_space(line, cursor)?;
    normalized.extend_from_slice(blocks);
    normalized.push(b' ');
    normalized.extend_from_slice(name);
    Some(())
}

fn normalize_ls_long_line(
    line: &[u8],
    options: LsColumnOptions,
    expected_ctime: Option<i64>,
    source: LsColumnSource,
    normalized: &mut Vec<u8>,
) -> Result<(), LsOutputNormalizationError> {
    if line.is_empty() || line.ends_with(b":") {
        if expected_ctime.is_some() {
            return Err(LsOutputNormalizationError::Ambiguous);
        }
        normalized.extend_from_slice(line);
        return Ok(());
    }

    let mut cursor = 0;
    let mut fields = Vec::<Vec<u8>>::new();
    if options.show_blocks {
        let blocks = take_ascii_space_token(line, &mut cursor)
            .ok_or(LsOutputNormalizationError::Ambiguous)?;
        if !ascii_unsigned(blocks) {
            return Err(LsOutputNormalizationError::Ambiguous);
        }
        fields.push(blocks.to_vec());
        if line.get(cursor) != Some(&b' ') {
            return Err(LsOutputNormalizationError::Ambiguous);
        }
        cursor += 1;
    }

    let raw_mode =
        take_ascii_token(line, &mut cursor).ok_or(LsOutputNormalizationError::Ambiguous)?;
    let mode = normalized_ls_mode(raw_mode, source).ok_or(LsOutputNormalizationError::Ambiguous)?;
    fields.push(mode.to_vec());
    for _ in 0..4 {
        let number = take_ascii_space_token(line, &mut cursor)
            .ok_or(LsOutputNormalizationError::Ambiguous)?;
        if !ascii_unsigned(number) {
            return Err(LsOutputNormalizationError::Ambiguous);
        }
        fields.push(number.to_vec());
    }

    match options.time_columns {
        LsTimeColumns::EpochSeconds => {
            let seconds = take_ascii_space_token(line, &mut cursor)
                .ok_or(LsOutputNormalizationError::Ambiguous)?;
            if !ascii_signed_decimal(seconds) {
                return Err(LsOutputNormalizationError::Ambiguous);
            }
            if let Some(expected_ctime) = expected_ctime {
                if seconds != expected_ctime.to_string().as_bytes() {
                    return Err(LsOutputNormalizationError::MetadataMismatch);
                }
                fields.push(b"<ctime-role:direct>".to_vec());
            } else {
                fields.push(seconds.to_vec());
            }
        }
        LsTimeColumns::FullIso => {
            let mut time = Vec::new();
            for _ in 0..3 {
                let part = take_ascii_space_token(line, &mut cursor)
                    .ok_or(LsOutputNormalizationError::Ambiguous)?;
                if !time.is_empty() {
                    time.push(b' ');
                }
                time.extend_from_slice(part);
            }
            fields.push(time);
        }
        LsTimeColumns::LongIso => {
            let mut time = Vec::new();
            for _ in 0..2 {
                let part = take_ascii_space_token(line, &mut cursor)
                    .ok_or(LsOutputNormalizationError::Ambiguous)?;
                if !time.is_empty() {
                    time.push(b' ');
                }
                time.extend_from_slice(part);
            }
            fields.push(time);
        }
        LsTimeColumns::Iso => {
            let mut time = take_ascii_space_token(line, &mut cursor)
                .ok_or(LsOutputNormalizationError::Ambiguous)?
                .to_vec();
            let mut lookahead = cursor;
            if let Some(candidate) = take_ascii_space_token(line, &mut lookahead) {
                if looks_like_hour_minute(candidate) {
                    time.push(b' ');
                    time.extend_from_slice(candidate);
                    cursor = lookahead;
                }
            }
            fields.push(time);
        }
        LsTimeColumns::DefaultC => {
            let month = take_ascii_space_token(line, &mut cursor)
                .ok_or(LsOutputNormalizationError::Ambiguous)?;
            let day = take_ascii_space_token(line, &mut cursor)
                .ok_or(LsOutputNormalizationError::Ambiguous)?;
            let time_or_year = take_ascii_space_token(line, &mut cursor)
                .ok_or(LsOutputNormalizationError::Ambiguous)?;
            let mut time = month.to_vec();
            time.push(b' ');
            if day.len() == 1 {
                time.push(b' ');
            }
            time.extend_from_slice(day);
            time.push(b' ');
            if !looks_like_hour_minute(time_or_year) {
                time.push(b' ');
            }
            time.extend_from_slice(time_or_year);
            fields.push(time);
        }
    }

    let name = remaining_after_one_ascii_space(line, cursor)
        .ok_or(LsOutputNormalizationError::Ambiguous)?;
    for (index, field) in fields.iter().enumerate() {
        if index > 0 {
            normalized.push(b' ');
        }
        normalized.extend_from_slice(field.as_slice());
    }
    normalized.push(b' ');
    normalized.extend_from_slice(name);
    Ok(())
}

fn take_ascii_space_token<'a>(line: &'a [u8], cursor: &mut usize) -> Option<&'a [u8]> {
    while line.get(*cursor).is_some_and(|byte| *byte == b' ') {
        *cursor += 1;
    }
    take_ascii_token(line, cursor)
}

fn take_ascii_token<'a>(line: &'a [u8], cursor: &mut usize) -> Option<&'a [u8]> {
    let start = *cursor;
    while line.get(*cursor).is_some_and(|byte| *byte != b' ') {
        *cursor += 1;
    }
    (start < *cursor).then(|| &line[start..*cursor])
}

fn remaining_after_one_ascii_space(line: &[u8], cursor: usize) -> Option<&[u8]> {
    (line.get(cursor) == Some(&b' ') && cursor + 1 < line.len()).then(|| &line[cursor + 1..])
}

fn ascii_unsigned(value: &[u8]) -> bool {
    !value.is_empty() && value.iter().all(u8::is_ascii_digit)
}

fn ascii_signed_decimal(value: &[u8]) -> bool {
    ascii_unsigned(value) || value.strip_prefix(b"-").is_some_and(ascii_unsigned)
}

fn looks_like_ls_mode(value: &[u8]) -> bool {
    value.len() == 10
        && matches!(value[0], b'-' | b'd' | b'l' | b'b' | b'c' | b'p' | b's')
        && value[1..]
            .iter()
            .all(|byte| matches!(byte, b'-' | b'r' | b'w' | b'x' | b's' | b'S' | b't' | b'T'))
}

fn normalized_ls_mode(value: &[u8], source: LsColumnSource) -> Option<&[u8]> {
    let mode = if source == LsColumnSource::Reference
        && value.len() == 11
        && matches!(value[10], b'+' | b'.' | b'?')
    {
        &value[..10]
    } else {
        value
    };
    looks_like_ls_mode(mode).then_some(mode)
}

fn looks_like_hour_minute(value: &[u8]) -> bool {
    value.len() == 5
        && value[0].is_ascii_digit()
        && value[1].is_ascii_digit()
        && value[2] == b':'
        && value[3].is_ascii_digit()
        && value[4].is_ascii_digit()
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum StatFormatPart {
    Literal(Vec<u8>),
    Directive(u8),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct StatInvocation<'a> {
    format: &'a str,
    dereference: bool,
    operands: Vec<&'a str>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct StatOperandMetadata {
    inode: u64,
    ctime_sec: i64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StatOutputNormalizationError {
    Ambiguous,
    MetadataMismatch,
}

fn stat_stdout_streams_differ(
    argv: &[String],
    reference: &[u8],
    dut: &[u8],
    reference_fs: &FsSnapshot,
    dut_fs: &FsSnapshot,
    cwd: Option<&Path>,
) -> Option<bool> {
    let invocation = parse_stat_invocation(argv)?;
    let parts = parse_stat_format(invocation.format)?;
    if !parts.iter().any(
        |part| matches!(part, StatFormatPart::Directive(directive) if matches!(directive, b'i' | b'Z')),
    ) {
        return None;
    }
    if !stat_format_has_safe_numeric_boundaries(&parts) {
        return None;
    }
    let cwd = cwd?;
    let reference_metadata = stat_operand_metadata(reference_fs, cwd, &invocation)?;
    let dut_metadata = stat_operand_metadata(dut_fs, cwd, &invocation)?;
    match (
        normalize_stat_output(reference, &parts, &reference_metadata),
        normalize_stat_output(dut, &parts, &dut_metadata),
    ) {
        (Ok(reference), Ok(dut)) => Some(reference != dut),
        (Err(StatOutputNormalizationError::MetadataMismatch), _)
        | (_, Err(StatOutputNormalizationError::MetadataMismatch)) => Some(true),
        _ => None,
    }
}

fn replay_stat_stdout_evidence(
    argv: &[String],
    reference: &[u8],
    dut: &[u8],
    reference_fs: &FsSnapshot,
    dut_fs: &FsSnapshot,
    cwd: Option<&Path>,
) -> Option<(ReplayStreamEvidence, ReplayStreamEvidence)> {
    let invocation = parse_stat_invocation(argv)?;
    let parts = parse_stat_format(invocation.format)?;
    if !parts.iter().any(
        |part| matches!(part, StatFormatPart::Directive(directive) if matches!(directive, b'i' | b'Z')),
    ) || !stat_format_has_safe_numeric_boundaries(&parts)
    {
        return None;
    }
    let cwd = cwd?;
    let reference_metadata = stat_operand_metadata(reference_fs, cwd, &invocation)?;
    let dut_metadata = stat_operand_metadata(dut_fs, cwd, &invocation)?;
    Some((
        normalize_stat_output(reference, &parts, &reference_metadata).map_or_else(
            |_| ReplayStreamEvidence::RawBytes(reference.to_vec()),
            ReplayStreamEvidence::CanonicalBytes,
        ),
        normalize_stat_output(dut, &parts, &dut_metadata).map_or_else(
            |_| ReplayStreamEvidence::RawBytes(dut.to_vec()),
            ReplayStreamEvidence::CanonicalBytes,
        ),
    ))
}

fn parse_stat_invocation(argv: &[String]) -> Option<StatInvocation<'_>> {
    let mut format = None;
    let mut dereference = false;
    let mut operands = Vec::new();
    let mut index = 0;
    let mut options = true;
    while index < argv.len() {
        let arg = argv[index].as_str();
        if options && arg == "--" {
            options = false;
            index += 1;
            continue;
        }
        if !options || !arg.starts_with('-') || arg == "-" {
            operands.push(arg);
            index += 1;
            continue;
        }
        if matches!(arg, "-L" | "--dereference") {
            dereference = true;
            index += 1;
            continue;
        }
        if matches!(arg, "-c" | "--format") {
            format = Some(argv.get(index + 1)?.as_str());
            index += 2;
            continue;
        }
        if let Some(value) = arg.strip_prefix("--format=") {
            format = Some(value);
            index += 1;
            continue;
        }
        if let Some(value) = arg.strip_prefix("-c").filter(|value| !value.is_empty()) {
            format = Some(value);
            index += 1;
            continue;
        }
        return None;
    }
    Some(StatInvocation {
        format: format?,
        dereference,
        operands,
    })
}

fn stat_operand_metadata(
    snapshot: &FsSnapshot,
    cwd: &Path,
    invocation: &StatInvocation<'_>,
) -> Option<Vec<StatOperandMetadata>> {
    let mut result = Vec::new();
    for operand in &invocation.operands {
        if operand.is_empty() {
            continue;
        }
        let key = snapshot_relative_key(cwd, operand)?;
        let Some(node) = snapshot_node(snapshot, &key, invocation.dereference) else {
            continue;
        };
        result.push(StatOperandMetadata {
            inode: node.host_key?.inode,
            ctime_sec: node.times.ctime_sec,
        });
    }
    Some(result)
}

fn snapshot_relative_key(cwd: &Path, operand: &str) -> Option<String> {
    let operand = Path::new(operand);
    if cwd.is_absolute() || operand.is_absolute() {
        return None;
    }
    normalized_snapshot_key(&cwd.join(operand))
}

fn normalized_snapshot_key(path: &Path) -> Option<String> {
    let mut parts = Vec::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::Normal(part) => parts.push(part.to_str()?.to_string()),
            Component::ParentDir => {
                parts.pop()?;
            }
            Component::RootDir | Component::Prefix(_) => return None,
        }
    }
    Some(if parts.is_empty() {
        ".".to_string()
    } else {
        parts.join("/")
    })
}

fn snapshot_node<'a>(
    snapshot: &'a FsSnapshot,
    key: &str,
    follow_symlinks: bool,
) -> Option<&'a FsNodeSnapshot> {
    let mut key = key.to_string();
    let mut visited = BTreeSet::new();
    loop {
        if key == "." {
            return snapshot.get(&key);
        }
        let components = key.split('/').collect::<Vec<_>>();
        let mut prefix = PathBuf::new();
        let mut redirected = false;
        for (index, component) in components.iter().enumerate() {
            prefix.push(component);
            let prefix_key = normalized_snapshot_key(&prefix)?;
            let node = snapshot.get(&prefix_key)?;
            let final_component = index + 1 == components.len();
            if node.kind != "symlink" || (final_component && !follow_symlinks) {
                continue;
            }
            if !visited.insert(prefix_key) || visited.len() > 40 {
                return None;
            }
            let parent = prefix.parent().unwrap_or_else(|| Path::new("."));
            let mut redirected_path = parent.join(&node.target);
            for remaining in &components[index + 1..] {
                redirected_path.push(remaining);
            }
            key = normalized_snapshot_key(&redirected_path)?;
            redirected = true;
            break;
        }
        if !redirected {
            return snapshot.get(&key);
        }
    }
}

fn parse_stat_format(format: &str) -> Option<Vec<StatFormatPart>> {
    if format.as_bytes().contains(&b'\n') {
        return None;
    }
    let bytes = format.as_bytes();
    let mut parts = Vec::new();
    let mut literal = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != b'%' {
            literal.push(bytes[index]);
            index += 1;
            continue;
        }
        let Some(directive) = bytes.get(index + 1).copied() else {
            literal.push(b'%');
            break;
        };
        if directive == b'%' {
            literal.push(b'%');
        } else if matches!(
            directive,
            b'a' | b'b'
                | b'B'
                | b'd'
                | b'D'
                | b'f'
                | b'g'
                | b'h'
                | b'i'
                | b'o'
                | b's'
                | b'u'
                | b'X'
                | b'Y'
                | b'Z'
        ) {
            if !literal.is_empty() {
                parts.push(StatFormatPart::Literal(std::mem::take(&mut literal)));
            }
            parts.push(StatFormatPart::Directive(directive));
        } else {
            literal.push(b'?');
        }
        index += 2;
    }
    if !literal.is_empty() {
        parts.push(StatFormatPart::Literal(literal));
    }
    Some(parts)
}

fn stat_format_has_safe_numeric_boundaries(parts: &[StatFormatPart]) -> bool {
    parts.iter().enumerate().all(|(index, part)| {
        let StatFormatPart::Directive(directive) = part else {
            return true;
        };
        match parts.get(index + 1) {
            None => true,
            Some(StatFormatPart::Literal(literal)) => {
                !literal.is_empty() && !stat_numeric_possible_byte(*directive, literal[0])
            }
            Some(StatFormatPart::Directive(_)) => false,
        }
    })
}

fn normalize_stat_output(
    data: &[u8],
    parts: &[StatFormatPart],
    metadata: &[StatOperandMetadata],
) -> Result<Vec<u8>, StatOutputNormalizationError> {
    if data.is_empty() {
        return if metadata.is_empty() {
            Ok(Vec::new())
        } else {
            Err(StatOutputNormalizationError::Ambiguous)
        };
    }
    let records = data
        .strip_suffix(b"\n")
        .ok_or(StatOutputNormalizationError::Ambiguous)?;
    let records = records.split(|byte| *byte == b'\n').collect::<Vec<_>>();
    if records.len() != metadata.len() {
        return Err(StatOutputNormalizationError::Ambiguous);
    }

    let mut inode_tokens = BTreeMap::<u64, usize>::new();
    let mut normalized = Vec::new();
    for (record_index, (record, expected)) in records.iter().zip(metadata).enumerate() {
        normalize_stat_record(
            record,
            parts,
            expected,
            record_index,
            &mut inode_tokens,
            &mut normalized,
        )?;
        normalized.push(b'\n');
    }
    Ok(normalized)
}

fn normalize_stat_record(
    record: &[u8],
    parts: &[StatFormatPart],
    metadata: &StatOperandMetadata,
    record_index: usize,
    inode_tokens: &mut BTreeMap<u64, usize>,
    normalized: &mut Vec<u8>,
) -> Result<(), StatOutputNormalizationError> {
    let mut cursor = 0;
    for (index, part) in parts.iter().enumerate() {
        match part {
            StatFormatPart::Literal(literal) => {
                if !record
                    .get(cursor..)
                    .ok_or(StatOutputNormalizationError::Ambiguous)?
                    .starts_with(literal)
                {
                    return Err(StatOutputNormalizationError::Ambiguous);
                }
                normalized.extend_from_slice(literal);
                cursor += literal.len();
            }
            StatFormatPart::Directive(directive) => {
                let end = match parts.get(index + 1) {
                    Some(StatFormatPart::Literal(literal)) => {
                        let remaining = record
                            .get(cursor..)
                            .ok_or(StatOutputNormalizationError::Ambiguous)?;
                        let offset = remaining
                            .iter()
                            .position(|byte| *byte == literal[0])
                            .ok_or(StatOutputNormalizationError::Ambiguous)?;
                        let boundary = cursor + offset;
                        if !record
                            .get(boundary..)
                            .ok_or(StatOutputNormalizationError::Ambiguous)?
                            .starts_with(literal)
                        {
                            return Err(StatOutputNormalizationError::Ambiguous);
                        }
                        boundary
                    }
                    None => record.len(),
                    Some(StatFormatPart::Directive(_)) => {
                        return Err(StatOutputNormalizationError::Ambiguous)
                    }
                };
                let value = record
                    .get(cursor..end)
                    .ok_or(StatOutputNormalizationError::Ambiguous)?;
                if !stat_numeric_value_is_valid(*directive, value) {
                    return Err(StatOutputNormalizationError::Ambiguous);
                }
                match directive {
                    b'i' => {
                        if value != metadata.inode.to_string().as_bytes() {
                            return Err(StatOutputNormalizationError::MetadataMismatch);
                        }
                        let token = match inode_tokens.get(&metadata.inode) {
                            Some(token) => *token,
                            None => {
                                let token = inode_tokens.len();
                                inode_tokens.insert(metadata.inode, token);
                                token
                            }
                        };
                        normalized.extend_from_slice(format!("<inode:{token}>").as_bytes());
                    }
                    b'Z' => {
                        if value != metadata.ctime_sec.to_string().as_bytes() {
                            return Err(StatOutputNormalizationError::MetadataMismatch);
                        }
                        normalized
                            .extend_from_slice(format!("<ctime-role:{record_index}>").as_bytes());
                    }
                    _ => normalized.extend_from_slice(value),
                }
                cursor = end;
            }
        }
    }
    if cursor == record.len() {
        Ok(())
    } else {
        Err(StatOutputNormalizationError::Ambiguous)
    }
}

fn stat_numeric_value_is_valid(directive: u8, value: &[u8]) -> bool {
    let unsigned = if matches!(directive, b'd' | b'D' | b'i' | b'X' | b'Y' | b'Z') {
        value.strip_prefix(b"-").unwrap_or(value)
    } else {
        value
    };
    !unsigned.is_empty()
        && unsigned
            .iter()
            .all(|byte| stat_numeric_body_byte(directive, *byte))
}

fn stat_numeric_body_byte(directive: u8, byte: u8) -> bool {
    match directive {
        b'a' => matches!(byte, b'0'..=b'7'),
        b'D' | b'f' => byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase(),
        _ => byte.is_ascii_digit(),
    }
}

fn stat_numeric_possible_byte(directive: u8, byte: u8) -> bool {
    stat_numeric_body_byte(directive, byte)
        || (byte == b'-' && matches!(directive, b'd' | b'D' | b'i' | b'X' | b'Y' | b'Z'))
}

fn normalized_pwd_output(data: &[u8], root: &Path) -> Vec<u8> {
    let root = root.display().to_string();
    let ends_with_newline = data.ends_with(b"\n");
    let text = String::from_utf8_lossy(data);
    let normalized: Vec<String> = text
        .lines()
        .map(|line| normalize_pwd_line(line, &root))
        .collect();
    if normalized.is_empty() && text.is_empty() {
        return Vec::new();
    }
    let mut output = normalized.join("\n").into_bytes();
    if ends_with_newline {
        output.push(b'\n');
    }
    output
}

fn normalize_pwd_line(line: &str, root: &str) -> String {
    match strip_path_prefix(line, root) {
        Some(suffix) => format!("$WORKDIR_ROOT{suffix}"),
        None => line.to_string(),
    }
}

fn strip_path_prefix<'a>(text: &'a str, prefix: &str) -> Option<&'a str> {
    let suffix = text.strip_prefix(prefix)?;
    if suffix.is_empty() || suffix.starts_with('/') {
        Some(suffix)
    } else {
        None
    }
}

fn printenv_environment_separator(argv: &[String]) -> Option<u8> {
    let mut separator = b'\n';
    let mut after_options = false;
    for arg in argv {
        if after_options {
            return None;
        }
        match arg.as_str() {
            "-0" | "--null" => separator = 0,
            "--" => after_options = true,
            _ => return None,
        }
    }
    Some(separator)
}

fn normalized_printenv_records(data: &[u8], separator: u8) -> Vec<Vec<u8>> {
    let mut records: Vec<Vec<u8>> = data
        .split(|b| *b == separator)
        .map(<[u8]>::to_vec)
        .collect();
    if records.last().is_some_and(Vec::is_empty) {
        records.pop();
    }
    records.sort();
    records
}

fn bytes_to_diff_lines(data: &[u8]) -> Vec<String> {
    if data.is_empty() {
        return vec!["<empty>".to_string()];
    }

    const MAX_LINES: usize = 400;
    let mut lines: Vec<String> = Vec::new();
    let mut current = String::new();

    for &b in data {
        match b {
            b'\n' => {
                lines.push(current);
                current = String::new();
            }
            b'\r' => current.push_str("\\r"),
            b'\t' => current.push_str("\\t"),
            0x20..=0x7e => current.push(char::from(b)),
            _ => {
                let _ = write!(current, "\\x{b:02x}");
            }
        }

        if lines.len() >= MAX_LINES {
            break;
        }
    }

    if lines.len() < MAX_LINES && (!current.is_empty() || data.last() != Some(&b'\n')) {
        lines.push(current);
    }
    if lines.len() >= MAX_LINES {
        lines.truncate(MAX_LINES);
        lines.push("... (truncated)".to_string());
    }
    lines
}

fn diff_lines(left: &[String], right: &[String]) -> Vec<DiffOp> {
    let n = left.len();
    let m = right.len();
    let mut lcs = vec![vec![0usize; m + 1]; n + 1];

    for i in (0..n).rev() {
        for j in (0..m).rev() {
            lcs[i][j] = if left[i] == right[j] {
                lcs[i + 1][j + 1] + 1
            } else {
                lcs[i + 1][j].max(lcs[i][j + 1])
            };
        }
    }

    let mut i = 0usize;
    let mut j = 0usize;
    let mut ops = Vec::new();

    while i < n && j < m {
        if left[i] == right[j] {
            ops.push(DiffOp::Equal(left[i].clone()));
            i += 1;
            j += 1;
        } else if lcs[i + 1][j] >= lcs[i][j + 1] {
            ops.push(DiffOp::Remove(left[i].clone()));
            i += 1;
        } else {
            ops.push(DiffOp::Add(right[j].clone()));
            j += 1;
        }
    }

    while i < n {
        ops.push(DiffOp::Remove(left[i].clone()));
        i += 1;
    }
    while j < m {
        ops.push(DiffOp::Add(right[j].clone()));
        j += 1;
    }

    ops
}

#[cfg(test)]
mod tests {
    use super::{
        compare_results_with_roots, ls_column_options, mismatch_signature, MismatchSignature,
        ProcessOutcomeEvidence,
    };
    use crate::fuzz::execution::IdentityTransitionEvidence;
    use crate::fuzz::{
        CompareResult, FsNodeSnapshot, FsSnapshot, FsTimes, HostInodeKeySnapshot, RunResult,
    };
    use std::path::Path;
    use std::process::Command;

    #[cfg(unix)]
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    // Direct outcome deserialization retains duplicate-field validation inside the tag.
    #[test]
    fn process_outcome_evidence_rejects_duplicate_code() {
        let error = serde_json::from_str::<ProcessOutcomeEvidence>(
            r#"{"kind":"exit","code":27,"code":0,"raw_status":0}"#,
        )
        .unwrap_err();
        assert!(
            error.to_string().contains("duplicate field `code`"),
            "{error}"
        );
    }

    // A repeated outcome discriminant cannot silently replace the first observation kind.
    #[test]
    fn process_outcome_evidence_rejects_duplicate_kind() {
        let error = serde_json::from_str::<ProcessOutcomeEvidence>(
            r#"{"kind":"signal","kind":"exit","code":0,"raw_status":0}"#,
        )
        .unwrap_err();
        assert!(
            error.to_string().contains("duplicate field `kind`"),
            "{error}"
        );
    }

    fn compare_results(
        util: &str,
        argv: &[String],
        reference: &RunResult,
        dut: &RunResult,
        reference_fs: &FsSnapshot,
        dut_fs: &FsSnapshot,
        ignore_stderr: bool,
    ) -> CompareResult {
        compare_results_with_roots(
            util,
            argv,
            reference,
            dut,
            &IdentityTransitionEvidence::new(),
            reference_fs,
            &IdentityTransitionEvidence::new(),
            dut_fs,
            ignore_stderr,
            None,
            None,
            None,
        )
        .unwrap()
    }

    #[cfg(unix)]
    fn shell_result(script: &str) -> RunResult {
        let output = Command::new("/bin/sh")
            .args(["-c", script])
            .output()
            .unwrap();
        RunResult {
            termination: crate::fuzz::process_outcome::Termination::from_status(output.status),
            stdout: output.stdout,
            stderr: output.stderr,
        }
    }

    // Exact process comparison distinguishes normal exit 141 from actual SIGPIPE 13.
    #[test]
    #[cfg(unix)]
    fn process_outcome_comparison_distinguishes_exit_141_from_sigpipe() {
        let exited = shell_result("exit 141");
        let signaled = shell_result("kill -PIPE $$");
        let comparison = compare_results(
            "true",
            &[],
            &exited,
            &signaled,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false,
        );
        assert!(matches!(
            comparison,
            CompareResult::Mismatch {
                process_outcome_diff: Some((
                    ProcessOutcomeEvidence::Observed(
                        crate::fuzz::process_outcome::Termination::Exit { code: 141, .. }
                    ),
                    ProcessOutcomeEvidence::Observed(
                        crate::fuzz::process_outcome::Termination::Signal { signal: 13, .. }
                    )
                )),
                ..
            }
        ));
    }

    // Repeated normal exits and repeated signals compare by their complete typed outcomes.
    #[test]
    #[cfg(unix)]
    fn process_outcome_comparison_accepts_equal_exit_and_signal_outcomes() {
        for script in ["exit 7", "kill -PIPE $$"] {
            let reference = shell_result(script);
            let dut = shell_result(script);
            assert_eq!(
                compare_results(
                    "true",
                    &[],
                    &reference,
                    &dut,
                    &FsSnapshot::new(),
                    &FsSnapshot::new(),
                    false,
                ),
                CompareResult::Match
            );
        }
    }

    // Exit code, signal number, and core-dump provenance each participate in comparison.
    #[test]
    fn process_outcome_comparison_rejects_each_typed_difference() {
        use crate::fuzz::process_outcome::Termination;

        let cases = [
            (Termination::test_exit(7), Termination::test_exit(8)),
            (
                Termination::Signal {
                    signal: 13,
                    core_dumped: false,
                    raw_status: 13,
                },
                Termination::Signal {
                    signal: 15,
                    core_dumped: false,
                    raw_status: 15,
                },
            ),
            (
                Termination::Signal {
                    signal: 13,
                    core_dumped: false,
                    raw_status: 13,
                },
                Termination::Signal {
                    signal: 13,
                    core_dumped: true,
                    raw_status: 141,
                },
            ),
        ];
        for (reference_termination, dut_termination) in cases {
            let reference = RunResult {
                termination: reference_termination,
                stdout: vec![],
                stderr: vec![],
            };
            let dut = RunResult {
                termination: dut_termination,
                stdout: vec![],
                stderr: vec![],
            };
            assert!(matches!(
                compare_results(
                    "true",
                    &[],
                    &reference,
                    &dut,
                    &FsSnapshot::new(),
                    &FsSnapshot::new(),
                    false,
                ),
                CompareResult::Mismatch {
                    process_outcome_diff: Some(_),
                    ..
                }
            ));
        }
    }

    #[cfg(unix)]
    fn compare_stat_with_roots(
        argv: &[String],
        reference: &RunResult,
        dut: &RunResult,
        reference_root: &Path,
        dut_root: &Path,
        cwd: &Path,
    ) -> CompareResult {
        let reference_fs =
            crate::fuzz::execution::snapshot_fs_without_restore(reference_root).unwrap();
        let dut_fs = crate::fuzz::execution::snapshot_fs_without_restore(dut_root).unwrap();
        compare_results_with_roots(
            "stat",
            argv,
            reference,
            dut,
            &IdentityTransitionEvidence::new(),
            &reference_fs,
            &IdentityTransitionEvidence::new(),
            &dut_fs,
            false,
            Some(reference_root),
            Some(dut_root),
            Some(cwd),
        )
        .unwrap()
    }

    #[cfg(unix)]
    fn compare_ls_with_roots(
        argv: &[String],
        reference: &RunResult,
        dut: &RunResult,
        reference_root: &Path,
        dut_root: &Path,
        cwd: &Path,
    ) -> CompareResult {
        let reference_fs =
            crate::fuzz::execution::snapshot_fs_without_restore(reference_root).unwrap();
        let dut_fs = crate::fuzz::execution::snapshot_fs_without_restore(dut_root).unwrap();
        compare_results_with_roots(
            "ls",
            argv,
            reference,
            dut,
            &IdentityTransitionEvidence::new(),
            &reference_fs,
            &IdentityTransitionEvidence::new(),
            &dut_fs,
            false,
            Some(reference_root),
            Some(dut_root),
            Some(cwd),
        )
        .unwrap()
    }

    #[cfg(unix)]
    fn stat_hardlink_fixture() -> tempfile::TempDir {
        let root = tempfile::tempdir().expect("stat fixture root");
        let cwd = root.path().join("work");
        std::fs::create_dir(&cwd).expect("create stat fixture cwd");
        std::fs::write(cwd.join("regular"), b"payload").expect("write stat fixture file");
        std::fs::hard_link(cwd.join("regular"), cwd.join("regular-hard"))
            .expect("create stat fixture hard link");
        std::os::unix::fs::symlink("regular", cwd.join("regular-link"))
            .expect("create stat fixture symbolic link");
        root
    }

    #[cfg(unix)]
    fn ls_ctime_fixture() -> tempfile::TempDir {
        use std::fs::FileTimes;
        use std::time::{Duration, SystemTime};

        let root = tempfile::tempdir().expect("ls ctime fixture root");
        let cwd = root.path().join("work");
        std::fs::create_dir(&cwd).expect("create ls ctime fixture cwd");
        std::fs::write(cwd.join("regular"), b"payload").expect("write ls ctime fixture file");
        let file = std::fs::OpenOptions::new()
            .write(true)
            .open(cwd.join("regular"))
            .expect("open ls ctime fixture file");
        file.set_times(
            FileTimes::new()
                .set_modified(SystemTime::UNIX_EPOCH + Duration::from_secs(946_684_800)),
        )
        .expect("set distinguishable ls fixture mtime");
        std::os::unix::fs::symlink("regular", cwd.join("regular-link"))
            .expect("create ls ctime fixture symbolic link");
        root
    }

    #[cfg(unix)]
    fn ls_short_ctime_sort_fixture(update_order: [&str; 2]) -> tempfile::TempDir {
        use std::time::Duration;

        let root = tempfile::tempdir().expect("ls short ctime fixture root");
        let cwd = root.path().join("work");
        std::fs::create_dir(&cwd).expect("create ls short ctime fixture cwd");
        for name in ["cg11-soc.bin", "i4-s13q"] {
            std::fs::write(cwd.join(name), b"payload").expect("write ls short ctime fixture file");
        }
        for (index, name) in update_order.into_iter().enumerate() {
            if index != 0 {
                std::thread::sleep(Duration::from_millis(10));
            }
            let path = cwd.join(name);
            let mut permissions = std::fs::metadata(&path)
                .expect("read ls short ctime fixture permissions")
                .permissions();
            permissions.set_mode(0o600);
            std::fs::set_permissions(path, permissions)
                .expect("advance ls short ctime fixture timestamp");
        }

        let earlier = std::fs::symlink_metadata(cwd.join(update_order[0]))
            .map(|metadata| (metadata.ctime(), metadata.ctime_nsec()))
            .expect("read earlier ls short ctime");
        let later = std::fs::symlink_metadata(cwd.join(update_order[1]))
            .map(|metadata| (metadata.ctime(), metadata.ctime_nsec()))
            .expect("read later ls short ctime");
        assert!(earlier < later, "fixture ctimes must be strictly ordered");
        root
    }

    #[cfg(unix)]
    fn direct_ls_epoch_output(
        root: &Path,
        operand: &str,
        follow: bool,
        seconds: i64,
        size_delta: u64,
    ) -> Vec<u8> {
        let path = root.join("work").join(operand);
        let metadata = if follow {
            std::fs::metadata(path)
        } else {
            std::fs::symlink_metadata(path)
        }
        .expect("read ls direct operand metadata");
        let mode = if metadata.file_type().is_symlink() {
            "lrwxrwxrwx"
        } else {
            "-rw-r--r--"
        };
        let display_name = if metadata.file_type().is_symlink() {
            format!("{operand} -> regular")
        } else {
            operand.to_string()
        };
        format!(
            "{mode} {} {} {} {} {seconds} {display_name}\n",
            metadata.nlink(),
            metadata.uid(),
            metadata.gid(),
            metadata.size() + size_delta,
        )
        .into_bytes()
    }

    #[cfg(unix)]
    fn followed_stat_output(root: &Path, operands: &[&str], size: u64) -> Vec<u8> {
        let mut output = Vec::new();
        for operand in operands {
            let metadata = std::fs::metadata(root.join("work").join(operand))
                .expect("read followed stat fixture metadata");
            output.extend_from_slice(
                format!("i={}|Z={}|s={size}\n", metadata.ino(), metadata.ctime()).as_bytes(),
            );
        }
        output
    }

    fn transition_snapshot(entries: &[(&str, Option<(u64, u64)>)]) -> FsSnapshot {
        entries
            .iter()
            .map(|(path, host_key)| {
                (
                    (*path).to_string(),
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
                        data: b"same bytes".to_vec(),
                        host_key: host_key
                            .map(|(device, inode)| HostInodeKeySnapshot { device, inode }),
                        link_count: Some(1),
                    },
                )
            })
            .collect()
    }

    // Current replay preserves the required raw metadata field exactly.
    #[test]
    fn replay_evidence_preserves_raw_metadata() {
        use crate::utils::world_json::RawStatMetadataJson;
        let mut snapshot = transition_snapshot(&[("a", Some((1, 2)))]);
        snapshot.get_mut("a").unwrap().raw_stat_metadata = RawStatMetadataJson::Known {
            device_number: u64::MAX,
            io_block_bytes: i64::MIN,
        };
        let evidence = super::replay_fs_evidence(&snapshot, None, false, "raw fixture").unwrap();
        let serialized = serde_json::to_value(&evidence).unwrap();
        assert_eq!(
            serialized["nodes"]["a"]["raw_stat_metadata"],
            serde_json::json!({
                "Known": { "device_number": u64::MAX, "io_block_bytes": i64::MIN }
            })
        );
        let restored: super::ReplayFsEvidence = serde_json::from_value(serialized.clone()).unwrap();
        assert_eq!(restored, evidence);
        assert_eq!(
            snapshot["a"].raw_stat_metadata,
            evidence.nodes["a"].raw_stat_metadata
        );
    }

    fn raw_replay_fixture(
        util: &str,
        reference: &FsSnapshot,
        dut: &FsSnapshot,
    ) -> super::ReplayVerdict {
        let run = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: vec![0, 128, 255],
            stderr: vec![0, 255],
        };
        let identity = IdentityTransitionEvidence::new();
        let compare = compare_results_with_roots(
            util,
            &[],
            &run,
            &run,
            &identity,
            reference,
            &identity,
            dut,
            false,
            None,
            None,
            None,
        )
        .unwrap();
        super::replay_verdict_with_roots(
            util,
            &[],
            &run,
            &run,
            &compare,
            &identity,
            &identity,
            reference,
            dut,
            reference,
            dut,
            false,
            None,
            None,
            None,
        )
        .unwrap()
    }

    // Current replay requires a present raw metadata value and rejects malformed omissions.
    #[test]
    fn replay_metadata_presence_is_not_an_unknown_value() {
        let snapshot = transition_snapshot(&[("a", Some((1, 2)))]);
        let current = raw_replay_fixture("cat", &snapshot, &snapshot);
        let mut value = serde_json::to_value(&current).unwrap();
        assert_eq!(
            value["reference_pre_fs"]["nodes"]["a"]["raw_stat_metadata"],
            "Unknown"
        );
        value["reference_pre_fs"]["nodes"]["a"]["raw_stat_metadata"] = serde_json::Value::Null;
        assert!(serde_json::from_value::<super::ReplayVerdict>(value.clone()).is_err());
        value["reference_pre_fs"]["nodes"]["a"]
            .as_object_mut()
            .unwrap()
            .remove("raw_stat_metadata");
        assert!(serde_json::from_value::<super::ReplayVerdict>(value).is_err());
        assert!(serde_json::to_value(&current).is_ok());
    }

    fn compare_transitions(
        reference_identity: &IdentityTransitionEvidence,
        reference_fs: &FsSnapshot,
        dut_identity: &IdentityTransitionEvidence,
        dut_fs: &FsSnapshot,
    ) -> Result<CompareResult, String> {
        let run = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: Vec::new(),
            stderr: Vec::new(),
        };
        compare_results_with_roots(
            "mv",
            &[],
            &run,
            &run,
            reference_identity,
            reference_fs,
            dut_identity,
            dut_fs,
            false,
            None,
            None,
            None,
        )
    }

    // Explicit transition evidence detects replacement even when both roles reuse the same raw numeric key.
    #[test]
    fn compare_detects_replacement_despite_same_numeric_key_reuse() {
        let reference_post = transition_snapshot(&[("b", Some((1, 10)))]);
        let dut_post = transition_snapshot(&[("b", Some((1, 10)))]);
        let reference_identity =
            IdentityTransitionEvidence::from([("a".to_string(), "b".to_string())]);
        let dut_identity = IdentityTransitionEvidence::new();

        let compare = compare_transitions(
            &reference_identity,
            &reference_post,
            &dut_identity,
            &dut_post,
        )
        .unwrap();

        assert!(matches!(compare, CompareResult::Mismatch { .. }));
        assert_eq!(
            mismatch_signature(&compare, &reference_identity, &dut_identity),
            Some(MismatchSignature::IdentityTransition)
        );
    }

    // Identity-transition mismatches have a distinct shrink signature from ordinary filesystem diffs.
    #[test]
    fn identity_transition_has_distinct_mismatch_signature() {
        let compare = CompareResult::Mismatch {
            process_outcome_diff: None,
            stdout_diff: false,
            stderr_diff: false,
            fs_diff: vec!["fs changed paths: a".to_string()],
        };
        let preserved = IdentityTransitionEvidence::from([("a".to_string(), "a".to_string())]);
        let replaced = IdentityTransitionEvidence::new();

        assert_eq!(
            mismatch_signature(&compare, &preserved, &preserved),
            Some(MismatchSignature::Filesystem)
        );
        assert_eq!(
            mismatch_signature(&compare, &preserved, &replaced),
            Some(MismatchSignature::IdentityTransition)
        );
    }

    // Equal renames compare by path continuity rather than raw inode values from separate processes.
    #[test]
    fn compare_accepts_equal_rename_with_different_raw_inode_values() {
        let reference_post = transition_snapshot(&[("b", Some((1, 10)))]);
        let dut_post = transition_snapshot(&[("b", Some((8, 80)))]);
        let identity = IdentityTransitionEvidence::from([("a".to_string(), "b".to_string())]);

        assert_eq!(
            compare_transitions(&identity, &reference_post, &identity, &dut_post).unwrap(),
            CompareResult::Match
        );
    }

    // Replacing an inode at the same path differs from preserving that inode in place.
    #[test]
    fn compare_detects_same_path_replacement() {
        let reference_post = transition_snapshot(&[("a", Some((1, 10)))]);
        let dut_post = transition_snapshot(&[("a", Some((2, 21)))]);
        let reference_identity =
            IdentityTransitionEvidence::from([("a".to_string(), "a".to_string())]);
        let dut_identity = IdentityTransitionEvidence::new();

        assert!(matches!(
            compare_transitions(
                &reference_identity,
                &reference_post,
                &dut_identity,
                &dut_post
            )
            .unwrap(),
            CompareResult::Mismatch { ref fs_diff, .. }
                if fs_diff.iter().any(|detail| detail.contains("identity transition"))
        ));
    }

    // Missing host identity must fail explicitly instead of silently weakening comparison.
    #[test]
    fn compare_rejects_unsupported_filesystem_identity() {
        let reference_post = transition_snapshot(&[("a", Some((1, 10)))]);
        let dut_post = transition_snapshot(&[("a", None)]);

        let error = compare_transitions(
            &IdentityTransitionEvidence::new(),
            &reference_post,
            &IdentityTransitionEvidence::new(),
            &dut_post,
        )
        .unwrap_err();

        assert!(error.contains("fs.identity unsupported"));
    }

    #[test]
    fn compare_ignores_filesystem_timestamp_only_changes() {
        let run = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: Vec::new(),
            stderr: Vec::new(),
        };
        let argv: Vec<String> = Vec::new();
        let mut reference_fs = FsSnapshot::new();
        reference_fs.insert(
            "a.txt".to_string(),
            node_with_times(FsTimes {
                atime_sec: 1,
                atime_nsec: 2,
                mtime_sec: 3,
                mtime_nsec: 4,
                ctime_sec: 5,
                ctime_nsec: 6,
            }),
        );
        let mut dut_fs = FsSnapshot::new();
        dut_fs.insert(
            "a.txt".to_string(),
            node_with_times(FsTimes {
                atime_sec: 10,
                atime_nsec: 20,
                mtime_sec: 30,
                mtime_nsec: 40,
                ctime_sec: 50,
                ctime_nsec: 60,
            }),
        );

        assert_eq!(
            compare_results("cat", &argv, &run, &run, &reference_fs, &dut_fs, false),
            CompareResult::Match
        );
    }

    // Chmod timestamp changes are modeled filesystem mismatches, even when every other field matches.
    #[test]
    fn chmod_compare_reports_filesystem_timestamp_only_changes() {
        let run = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: Vec::new(),
            stderr: Vec::new(),
        };
        let mut reference_fs = FsSnapshot::new();
        reference_fs.insert(
            "a.txt".to_string(),
            node_with_times(FsTimes {
                atime_sec: 1,
                atime_nsec: 2,
                mtime_sec: 3,
                mtime_nsec: 4,
                ctime_sec: 5,
                ctime_nsec: 6,
            }),
        );
        let mut dut_fs = FsSnapshot::new();
        dut_fs.insert(
            "a.txt".to_string(),
            node_with_times(FsTimes {
                atime_sec: 10,
                atime_nsec: 20,
                mtime_sec: 30,
                mtime_nsec: 40,
                ctime_sec: 50,
                ctime_nsec: 60,
            }),
        );

        assert!(matches!(
            compare_results(
                "chmod",
                &[],
                &run,
                &run,
                &reference_fs,
                &dut_fs,
                false,
            ),
            CompareResult::Mismatch { ref fs_diff, .. } if !fs_diff.is_empty()
        ));
    }

    // 순차 생성된 복제 트리의 원시 변경 시각만 다르면 엄격한 파일 시스템 비교에서도 무시한다.
    #[test]
    fn chmod_compare_ignores_cross_clone_ctime_only_difference() {
        let run = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: Vec::new(),
            stderr: Vec::new(),
        };
        let reference_fs = FsSnapshot::from([(
            "a.txt".to_string(),
            node_with_times(FsTimes {
                ctime_sec: 100,
                ctime_nsec: 10,
                ..FsTimes::default()
            }),
        )]);
        let dut_fs = FsSnapshot::from([(
            "a.txt".to_string(),
            node_with_times(FsTimes {
                ctime_sec: 200,
                ctime_nsec: 20,
                ..FsTimes::default()
            }),
        )]);

        assert_eq!(
            compare_results("chmod", &[], &run, &run, &reference_fs, &dut_fs, false,),
            CompareResult::Match
        );
    }

    // Chmod help output remains byte-exact rather than collapsing nonempty streams to presence.
    #[test]
    fn chmod_compare_reports_one_byte_help_mismatch() {
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"help\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"help!\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "chmod",
                &["--help".to_string()],
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // A stat format value named --help keeps stdout comparison byte-exact.
    #[test]
    fn stat_help_format_value_does_not_weaken_stdout_comparison() {
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"--help\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"corrupt\n".to_vec(),
            stderr: Vec::new(),
        };
        let argv = ["-c", "--help", "regular"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();

        assert!(matches!(
            compare_results(
                "stat",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // A file named --help after the option terminator keeps stdout comparison byte-exact.
    #[test]
    fn ls_help_operand_does_not_weaken_stdout_comparison() {
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"--help\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"corrupt\n".to_vec(),
            stderr: Vec::new(),
        };
        let argv = ["--", "--help"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // The common ignore policy also covers chmod diagnostic wording.
    #[test]
    fn chmod_compare_can_ignore_diagnostic_mismatch() {
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"chmod: missing operand\nTry 'chmod --help' for more information.\n".to_vec(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"/tmp/chmod: missing operand\nTry 'chmod --help' for more information.\n"
                .to_vec(),
        };

        assert!(matches!(
            compare_results(
                "chmod",
                &[],
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                true,
            ),
            CompareResult::Match
        ));
    }

    #[test]
    fn compare_ignores_printenv_environment_record_order() {
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"B=2\nA=1\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"A=1\nB=2\n".to_vec(),
            stderr: Vec::new(),
        };
        let argv: Vec<String> = Vec::new();

        assert_eq!(
            compare_results(
                "printenv",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Match
        );
    }

    #[test]
    fn compare_keeps_printenv_operand_output_order_significant() {
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"2\n1\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"1\n2\n".to_vec(),
            stderr: Vec::new(),
        };
        let argv = vec!["B".to_string(), "A".to_string()];

        assert!(matches!(
            compare_results(
                "printenv",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    #[test]
    fn compare_normalizes_pwd_variant_roots() {
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"/tmp/fuzz/iter-000001/ref/dir0\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"/tmp/fuzz/iter-000001/dut/dir0\n".to_vec(),
            stderr: Vec::new(),
        };
        let argv = vec!["--physical".to_string()];

        assert_eq!(
            compare_results_with_roots(
                "pwd",
                &argv,
                &reference,
                &dut,
                &IdentityTransitionEvidence::new(),
                &FsSnapshot::new(),
                &IdentityTransitionEvidence::new(),
                &FsSnapshot::new(),
                false,
                Some(Path::new("/tmp/fuzz/iter-000001/ref")),
                Some(Path::new("/tmp/fuzz/iter-000001/dut")),
                None,
            )
            .unwrap(),
            CompareResult::Match
        );

        assert!(matches!(
            compare_results(
                "pwd",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // Numeric-long comparison ignores only GNU's inter-column padding while retaining every value.
    #[test]
    fn ls_compare_normalizes_numeric_long_column_padding() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"total 4\n-rw-r----- 1 1013 1013    0 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"total 4\n-rw-r----- 1 1013 1013 0 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };

        assert_eq!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Match
        );
    }

    // GNU tests/ls/acl.sh의 참조 출력 표지는 모델 밖이므로 수치 긴 출력에서만 제거한다.
    #[test]
    fn ls_compare_excludes_reference_acl_mode_marker() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r-----+ 1 1013 1013 1 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013 1013 1 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };

        assert_eq!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Match
        );
    }

    // 접근 제어 목록 표지를 제외해도 GNU tests/ls/acl.sh의 권한 비트는 계속 비교한다.
    #[test]
    fn ls_compare_keeps_permissions_strict_with_reference_acl_marker() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r-----+ 1 1013 1013 1 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rwxr----- 1 1013 1013 1 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // 모델 밖 표지를 시험 대상에도 허용하면 명세의 10자 모드 출력 위반을 숨기게 된다.
    #[test]
    fn ls_compare_rejects_dut_acl_mode_marker() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r-----+ 1 1013 1013 1 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = reference.clone();

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // GNU column padding is normalized without accepting a noncanonical DUT field separator.
    #[test]
    fn ls_compare_rejects_extra_space_between_numeric_long_fields() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013 1013    1 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013  1013 1 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // The canonical C-style timestamp retains the leading blank in a one-digit day.
    #[test]
    fn ls_compare_rejects_missing_default_time_day_padding() {
        let argv = vec!["-n".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013 1013 1 Aug  7 12:34 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013 1013 1 Aug 7 12:34 visible\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // Numeric-long output must begin with the file mode rather than hidden leading padding.
    #[test]
    fn ls_compare_rejects_leading_space_before_long_mode() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013 1013 0 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b" -rw-r----- 1 1013 1013 0 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // Combined block and long output requires exactly one separator before the file mode.
    #[test]
    fn ls_compare_rejects_extra_space_between_block_count_and_mode() {
        let argv = vec!["-ns".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"4 -rw-r----- 1 1013 1013 0 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"4  -rw-r----- 1 1013 1013 0 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // A different modeled timestamp remains visible after numeric-long column normalization.
    #[test]
    fn ls_compare_keeps_numeric_long_values_exact() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013 1013    0 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013 1013 0 2000000001 visible\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // A standalone time selector never hides corruption in an emitted file name.
    #[test]
    fn ls_compare_keeps_standalone_time_selector_names_strict() {
        let argv = vec!["--time=status".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"expected-name\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"corrupt-name\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // Standalone time selectors keep exit and diagnostic differences strict.
    #[test]
    fn ls_compare_keeps_standalone_time_selector_errors_strict() {
        let argv = vec!["--time=status".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"newer\nolder\n".to_vec(),
            stderr: b"reference error\n".to_vec(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(2),
            stdout: b"older\nnewer\n".to_vec(),
            stderr: b"dut error\n".to_vec(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                process_outcome_diff: Some(_),
                stdout_diff: true,
                stderr_diff: true,
                ..
            }
        ));
    }

    // GNU's unmodeled birth-time selector line is removed without weakening modeled diagnostics.
    #[test]
    fn ls_compare_excludes_only_unmodeled_birth_time_diagnostic() {
        let argv = vec!["--time=XX".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"ls: invalid argument 'XX' for '--time'\nValid arguments are:\n  - 'atime', 'access', 'use'\n  - 'ctime', 'status'\n  - 'mtime', 'modification'\n  - 'birth', 'creation'\nTry 'ls --help' for more information.\n".to_vec(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"ls: invalid argument 'XX' for '--time'\nValid arguments are:\n  - 'atime', 'access', 'use'\n  - 'ctime', 'status'\n  - 'mtime', 'modification'\nTry 'ls --help' for more information.\n".to_vec(),
        };

        assert_eq!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Match
        );
    }

    // A ctime sort without fixture roots falls back to byte-for-byte comparison.
    #[test]
    fn ls_compare_keeps_explicit_time_sort_order_strict() {
        let argv = vec!["-t".to_string(), "--time=status".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"newer\nolder\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"older\nnewer\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // 복제본의 실제 변경 시각 순서가 달라도 각 출력이 자기 상태에 맞으면 일치한다.
    #[test]
    #[cfg(unix)]
    fn ls_compare_accepts_clone_local_ctime_sort_orders() {
        let reference_root = ls_short_ctime_sort_fixture(["cg11-soc.bin", "i4-s13q"]);
        let dut_root = ls_short_ctime_sort_fixture(["i4-s13q", "cg11-soc.bin"]);
        let argv = ["-t", "--time=ctime"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"i4-s13q\ncg11-soc.bin\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"cg11-soc.bin\ni4-s13q\n".to_vec(),
            stderr: Vec::new(),
        };

        assert_eq!(
            compare_ls_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Match
        );
    }

    // 역순 출력이 시험 대상 복제본의 실제 변경 시각 순서를 어기면 불일치한다.
    #[test]
    #[cfg(unix)]
    fn ls_compare_rejects_wrong_clone_local_reverse_ctime_order() {
        let reference_root = ls_short_ctime_sort_fixture(["cg11-soc.bin", "i4-s13q"]);
        let dut_root = ls_short_ctime_sort_fixture(["i4-s13q", "cg11-soc.bin"]);
        let argv = ["-tr", "--time=status"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"cg11-soc.bin\ni4-s13q\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"cg11-soc.bin\ni4-s13q\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_ls_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // Numeric-long time output remains strict even when the selected field is change time.
    #[test]
    fn ls_compare_keeps_numeric_long_change_time_strict() {
        let argv = vec!["-n".to_string(), "--time=status".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r--r-- 1 1000 1000 1 Jan  1 00:00 file\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r--r-- 1 1000 1000 1 Jan  2 00:00 file\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // 직접 심볼릭 링크의 실제 lstat 변경 시각만 검증한 뒤 복제본 차이를 역할로 치환한다.
    #[test]
    #[cfg(unix)]
    fn ls_compare_normalizes_verified_direct_lstat_ctime() {
        let reference_root = ls_ctime_fixture();
        let dut_root = ls_ctime_fixture();
        let operand = "regular-link";
        let argv = ["-n", "-d", "--time=status", "--time-style=+%s", operand]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let reference_ctime =
            std::fs::symlink_metadata(reference_root.path().join("work").join(operand))
                .expect("read reference symbolic link metadata")
                .ctime();
        let dut_ctime = std::fs::symlink_metadata(dut_root.path().join("work").join(operand))
            .expect("read DUT symbolic link metadata")
            .ctime();
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: direct_ls_epoch_output(
                reference_root.path(),
                operand,
                false,
                reference_ctime,
                0,
            ),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: direct_ls_epoch_output(dut_root.path(), operand, false, dut_ctime, 0),
            stderr: Vec::new(),
        };

        assert_eq!(
            compare_ls_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Match
        );
    }

    // 변경 시각 대신 수정 시각을 출력한 구현은 역할 치환 전에 실제 메타데이터와 대조해 거부한다.
    #[test]
    #[cfg(unix)]
    fn ls_compare_rejects_mtime_in_direct_ctime_column() {
        let reference_root = ls_ctime_fixture();
        let dut_root = ls_ctime_fixture();
        let operand = "regular";
        let argv = ["-ndc", "--time-style=+%s", operand]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let reference_metadata =
            std::fs::symlink_metadata(reference_root.path().join("work").join(operand))
                .expect("read reference regular metadata");
        let dut_metadata = std::fs::symlink_metadata(dut_root.path().join("work").join(operand))
            .expect("read DUT regular metadata");
        assert_ne!(dut_metadata.mtime(), dut_metadata.ctime());
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: direct_ls_epoch_output(
                reference_root.path(),
                operand,
                false,
                reference_metadata.ctime(),
                0,
            ),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: direct_ls_epoch_output(
                dut_root.path(),
                operand,
                false,
                dut_metadata.mtime(),
                0,
            ),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_ls_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // 검증된 변경 시각 옆의 파일 크기는 역할 치환 뒤에도 정확히 비교한다.
    #[test]
    #[cfg(unix)]
    fn ls_compare_keeps_direct_ctime_neighbor_fields_strict() {
        let reference_root = ls_ctime_fixture();
        let dut_root = ls_ctime_fixture();
        let operand = "regular";
        let argv = ["-nd", "--time=status", "--time-style=+%s", operand]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let reference_ctime =
            std::fs::symlink_metadata(reference_root.path().join("work").join(operand))
                .expect("read reference regular metadata")
                .ctime();
        let dut_ctime = std::fs::symlink_metadata(dut_root.path().join("work").join(operand))
            .expect("read DUT regular metadata")
            .ctime();
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: direct_ls_epoch_output(
                reference_root.path(),
                operand,
                false,
                reference_ctime,
                0,
            ),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: direct_ls_epoch_output(dut_root.path(), operand, false, dut_ctime, 1),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_ls_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // -H는 직접 심볼릭 링크 피연산자의 대상 변경 시각을 검증한다.
    #[test]
    #[cfg(unix)]
    fn ls_compare_uses_followed_ctime_for_command_line_dereference() {
        let reference_root = ls_ctime_fixture();
        let dut_root = ls_ctime_fixture();
        let operand = "regular-link";
        let argv = ["-ndcH", "--time-style=+%s", operand]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let reference_ctime = std::fs::metadata(reference_root.path().join("work").join(operand))
            .expect("read followed reference metadata")
            .ctime();
        let dut_ctime = std::fs::metadata(dut_root.path().join("work").join(operand))
            .expect("read followed DUT metadata")
            .ctime();
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: direct_ls_epoch_output(
                reference_root.path(),
                operand,
                true,
                reference_ctime,
                0,
            ),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: direct_ls_epoch_output(dut_root.path(), operand, true, dut_ctime, 0),
            stderr: Vec::new(),
        };

        assert_eq!(
            compare_ls_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Match
        );
    }

    // 변경 시각 정렬은 역할 치환 경계 밖이므로 원시 출력 차이를 그대로 보고한다.
    #[test]
    #[cfg(unix)]
    fn ls_compare_keeps_ctime_sort_raw_strict() {
        let reference_root = ls_ctime_fixture();
        let dut_root = ls_ctime_fixture();
        let operand = "regular";
        let argv = ["-ndtc", "--time-style=+%s", operand]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: direct_ls_epoch_output(reference_root.path(), operand, false, 1, 0),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: direct_ls_epoch_output(dut_root.path(), operand, false, 2, 0),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_ls_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // Block-only comparison removes the width padding before the block count but preserves the name.
    #[test]
    fn ls_compare_normalizes_only_the_block_prefix() {
        let argv = vec!["-s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b" 4 visible  name\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"4 visible name\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // Block-count normalization preserves spaces that belong to the start of a file name.
    #[test]
    fn ls_compare_preserves_leading_spaces_in_block_names() {
        let argv = vec!["-s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"4   name\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"4 name\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // Numeric-long normalization preserves spaces that belong to the start of a file name.
    #[test]
    fn ls_compare_preserves_leading_spaces_in_long_names() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r--r-- 1 1000 1000 1 0   name\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r--r-- 1 1000 1000 1 0 name\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "ls",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // Unknown long options make ls column parsing fail closed.
    #[test]
    fn ls_parser_rejects_unknown_long_option() {
        assert!(ls_column_options(&["--unknown".to_string()]).is_none());
    }

    // A required time-style value cannot be omitted from the parsed command line.
    #[test]
    fn ls_parser_rejects_missing_time_style_value() {
        assert!(ls_column_options(&["--time-style".to_string()]).is_none());
    }

    // An unrecognized time style cannot select a guessed output layout.
    #[test]
    fn ls_parser_rejects_unknown_time_style() {
        assert!(ls_column_options(&["--time-style=unknown".to_string()]).is_none());
    }

    // Unknown short options make ls column parsing fail closed.
    #[test]
    fn ls_parser_rejects_unknown_short_option() {
        assert!(ls_column_options(&["-Q".to_string()]).is_none());
    }

    // 서로 복제된 트리는 원시 아이노드와 변경 시각이 달라도 같은 하드 링크 관계로 비교된다.
    #[test]
    #[cfg(unix)]
    fn stat_compare_normalizes_inode_identity_and_change_time_observations() {
        let reference_root = stat_hardlink_fixture();
        let dut_root = stat_hardlink_fixture();
        let operands = ["regular-link", "regular-hard"];
        let argv = vec![
            "-L".to_string(),
            "-c".to_string(),
            "i=%i|Z=%Z|s=%s".to_string(),
            operands[0].to_string(),
            operands[1].to_string(),
        ];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(reference_root.path(), &operands, 7),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(dut_root.path(), &operands, 7),
            stderr: Vec::new(),
        };

        assert_eq!(
            compare_stat_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Match
        );
    }

    // Host comparison uses transported snapshots and never reopens container-only fixture paths.
    #[test]
    #[cfg(unix)]
    fn stat_compare_uses_snapshots_when_roots_do_not_exist_on_host() {
        let reference_root = stat_hardlink_fixture();
        let dut_root = stat_hardlink_fixture();
        let operands = ["regular-link", "regular-hard"];
        let argv = vec![
            "-L".to_string(),
            "-c".to_string(),
            "i=%i|Z=%Z|s=%s".to_string(),
            operands[0].to_string(),
            operands[1].to_string(),
        ];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(reference_root.path(), &operands, 7),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(dut_root.path(), &operands, 7),
            stderr: Vec::new(),
        };
        let reference_fs =
            crate::fuzz::execution::snapshot_fs_without_restore(reference_root.path()).unwrap();
        let dut_fs = crate::fuzz::execution::snapshot_fs_without_restore(dut_root.path()).unwrap();

        let result = compare_results_with_roots(
            "stat",
            &argv,
            &reference,
            &dut,
            &IdentityTransitionEvidence::new(),
            &reference_fs,
            &IdentityTransitionEvidence::new(),
            &dut_fs,
            false,
            Some(Path::new("/container-only/reference")),
            Some(Path::new("/container-only/dut")),
            Some(Path::new("work")),
        )
        .unwrap();

        assert_eq!(result, CompareResult::Match);
    }

    // A GNU-style unknown directive remains a literal question mark beside normalized inode output.
    #[test]
    #[cfg(unix)]
    fn stat_compare_normalizes_inode_beside_unknown_directive() {
        let reference_root = stat_hardlink_fixture();
        let dut_root = stat_hardlink_fixture();
        let argv = ["-c", "q=%Q|i=%i", "regular"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let reference_inode = std::fs::symlink_metadata(reference_root.path().join("work/regular"))
            .expect("read reference inode metadata")
            .ino();
        let dut_inode = std::fs::symlink_metadata(dut_root.path().join("work/regular"))
            .expect("read DUT inode metadata")
            .ino();
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: format!("q=?|i={reference_inode}\n").into_bytes(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: format!("q=?|i={dut_inode}\n").into_bytes(),
            stderr: Vec::new(),
        };

        assert_eq!(
            compare_stat_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Match
        );
    }

    // 실제 하드 링크 피연산자에서 0으로 조작된 아이노드와 변경 시각은 정규화로 숨지 않는다.
    #[test]
    #[cfg(unix)]
    fn stat_compare_rejects_zero_metadata_for_real_hardlink_operands() {
        let reference_root = stat_hardlink_fixture();
        let dut_root = stat_hardlink_fixture();
        let operands = ["regular-link", "regular-hard"];
        let argv = vec![
            "-L".to_string(),
            "-c".to_string(),
            "i=%i|Z=%Z|s=%s".to_string(),
            operands[0].to_string(),
            operands[1].to_string(),
        ];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(reference_root.path(), &operands, 7),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"i=0|Z=0|s=7\ni=0|Z=0|s=7\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_stat_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // 한 구현이 하드 링크 두 이름에 서로 다른 아이노드를 출력하면 관계 정규화 뒤에도 불일치다.
    #[test]
    #[cfg(unix)]
    fn stat_compare_reports_hardlink_identity_partition_difference() {
        let reference_root = stat_hardlink_fixture();
        let dut_root = stat_hardlink_fixture();
        let operands = ["regular", "regular-hard"];
        let argv = vec![
            "--format=i=%i|Z=%Z".to_string(),
            operands[0].to_string(),
            operands[1].to_string(),
        ];
        let reference_metadata = std::fs::metadata(reference_root.path().join("work/regular"))
            .expect("read reference hard link metadata");
        let dut_metadata = std::fs::metadata(dut_root.path().join("work/regular"))
            .expect("read DUT hard link metadata");
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: format!(
                "i={0}|Z={1}\ni={0}|Z={1}\n",
                reference_metadata.ino(),
                reference_metadata.ctime(),
            )
            .into_bytes(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: format!(
                "i={0}|Z={1}\ni={2}|Z={1}\n",
                dut_metadata.ino(),
                dut_metadata.ctime(),
                dut_metadata.ino() + 1,
            )
            .into_bytes(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_stat_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // 정규화 대상과 함께 출력된 결정적 크기 값은 바이트 단위로 계속 엄격히 비교된다.
    #[test]
    #[cfg(unix)]
    fn stat_compare_keeps_deterministic_directives_exact() {
        let reference_root = stat_hardlink_fixture();
        let dut_root = stat_hardlink_fixture();
        let operands = ["regular-link"];
        let argv = vec![
            "-L".to_string(),
            "-c".to_string(),
            "i=%i|Z=%Z|s=%s".to_string(),
            operands[0].to_string(),
        ];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(reference_root.path(), &operands, 7),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(dut_root.path(), &operands, 8),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_stat_with_roots(
                &argv,
                &reference,
                &dut,
                reference_root.path(),
                dut_root.path(),
                Path::new("work"),
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // 인접 수치 지시자로 경계를 확정할 수 없으면 stat 비교는 원문 비교로 닫힌다.
    #[test]
    fn stat_compare_falls_back_to_exact_output_for_ambiguous_format() {
        let argv = vec!["-c".to_string(), "%i%Z".to_string(), "file".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"1011700000000\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"90011800000000\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "stat",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // 부호 있는 변경 시각과 같은 빼기표 경계는 모호하므로 원문 비교를 유지한다.
    #[test]
    fn stat_compare_falls_back_when_literal_can_be_a_numeric_sign() {
        let argv = vec!["-c".to_string(), "%Z-%i".to_string(), "file".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-10-101\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(0),
            stdout: b"-20-9001\n".to_vec(),
            stderr: Vec::new(),
        };

        assert!(matches!(
            compare_results(
                "stat",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
    }

    // stat 표준 출력이 정규화되어도 오류 진단 문자열은 기본 정책에서 그대로 비교된다.
    #[test]
    fn stat_compare_keeps_stderr_strict() {
        let argv = vec![
            "-c".to_string(),
            "i=%i|Z=%Z".to_string(),
            "missing".to_string(),
        ];
        let reference = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"stat: cannot statx 'missing': No such file or directory\n".to_vec(),
        };
        let dut = RunResult {
            termination: crate::fuzz::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"stat: missing file 'missing'\n".to_vec(),
        };

        assert!(matches!(
            compare_results(
                "stat",
                &argv,
                &reference,
                &dut,
                &FsSnapshot::new(),
                &FsSnapshot::new(),
                false,
            ),
            CompareResult::Mismatch {
                stderr_diff: true,
                ..
            }
        ));
    }

    fn node_with_times(times: FsTimes) -> FsNodeSnapshot {
        FsNodeSnapshot {
            raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
            kind: "file".to_string(),
            mode_octal: "0644".to_string(),
            times,
            uid: None,
            gid: None,
            logical_size: None,
            allocated_512_blocks: None,
            preferred_io_block_bytes: None,
            target: String::new(),
            data: b"same bytes".to_vec(),
            host_key: Some(HostInodeKeySnapshot {
                device: 1,
                inode: 1,
            }),
            link_count: None,
        }
    }
}
