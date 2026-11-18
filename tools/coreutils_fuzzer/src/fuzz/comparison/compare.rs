use super::{CompareResult, DiffOp};
use crate::fuzz::comparison::fs_snapshot::IdentityTransitionEvidence;
use crate::fuzz::comparison::process_outcome::Termination;
use crate::fuzz::{FsNodeSnapshot, FsSnapshot, RunResult};
use crate::utils::arg_semantics::requests_help_or_version;
use crate::{fuzzer_outcome_marker, SEMANTIC_MISMATCH};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;

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
    _reference_root: Option<&Path>,
    _dut_root: Option<&Path>,
    _cwd: Option<&Path>,
) -> Result<CompareResult, String> {
    let process_outcome_diff = (reference.termination != dut.termination).then_some((
        ProcessOutcomeEvidence::Observed(reference.termination),
        ProcessOutcomeEvidence::Observed(dut.termination),
    ));
    let stdout_diff = stdout_streams_differ(util, argv, &reference.stdout, &dut.stdout);
    let stderr_diff = !ignore_stderr && stderr_streams_differ(&reference.stderr, &dut.stderr);
    let fs_diff = filesystem_comparison_details(
        reference_fs,
        dut_fs,
        reference_identity,
        dut_identity,
        false,
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
    CanonicalBytes(Vec<u8>),
    RawBytes(Vec<u8>),
    Records(Vec<Vec<u8>>),
    Bounded(BoundedStreamEvidence),
}

/// Streams longer than this are saved as their length, digest and both ends.
/// A crashing candidate can print megabytes of stack trace, which every bundle copy repeats.
pub(crate) const STREAM_EVIDENCE_LIMIT_BYTES: usize = 64 * 1024;

/// A stream too long to save whole. The digest covers every byte, so replay still
/// detects a change in the omitted middle.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct BoundedStreamEvidence {
    pub(crate) length: u64,
    pub(crate) fnv1a64: String,
    pub(crate) head: Vec<u8>,
    pub(crate) tail: Vec<u8>,
}

/// Saves a stream whole up to the limit and bounded above it.
pub(crate) fn stream_evidence(data: &[u8]) -> ReplayStreamEvidence {
    if data.len() <= STREAM_EVIDENCE_LIMIT_BYTES {
        return ReplayStreamEvidence::RawBytes(data.to_vec());
    }
    let half = STREAM_EVIDENCE_LIMIT_BYTES / 2;
    ReplayStreamEvidence::Bounded(BoundedStreamEvidence {
        length: data.len() as u64,
        fnv1a64: format!("{:016x}", fnv1a64(data)),
        head: data[..half].to_vec(),
        tail: data[data.len() - half..].to_vec(),
    })
}

/// 64-bit FNV-1a. Not cryptographic: it only tells replayed output from saved output.
fn fnv1a64(data: &[u8]) -> u64 {
    data.iter().fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReplayFsNodeEvidence {
    #[serde(default)]
    pub(crate) raw_times: Option<crate::fuzz::FsTimes>,
    #[serde(default)]
    pub(crate) host_key: Option<crate::fuzz::HostInodeKeySnapshot>,
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
    #[serde(default)]
    pub(crate) execution: Option<crate::fuzz::execution::ExecutionEvidence>,
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
    /// Returns the recorded reference time inputs after validating temporal evidence.
    pub(crate) fn fixture_time_inputs(
        &self,
    ) -> Result<BTreeMap<String, crate::fuzz::FsTimes>, String> {
        self.validate_time_evidence()?;
        self.reference_pre_fs
            .nodes
            .iter()
            .map(|(path, node)| {
                if node.kind == "inaccessible" {
                    return Err(format!(
                        "cannot restore unobserved fixture time input at {path}"
                    ));
                }
                Ok((
                    path.clone(),
                    node.raw_times
                        .ok_or("missing saved raw timestamps; rerun with --case-set")?,
                ))
            })
            .collect()
    }

    /// Checks raw timestamps, transition flags and run windows before replay abstraction.
    pub(crate) fn validate_time_evidence(&self) -> Result<(), String> {
        let execution = self
            .execution
            .as_ref()
            .ok_or("missing execution time/sharing evidence; rerun with --case-set")?;
        for window in [execution.reference_window, execution.dut_window] {
            if !window.contains(window.start) || !window.contains(window.end) {
                return Err("invalid execution wall-clock window".into());
            }
        }
        if execution.reference_window.end > execution.dut_window.start {
            return Err("execution windows are not sequential".into());
        }
        for (pre, post, identity) in [
            (
                &self.reference_pre_fs,
                &self.reference_post_fs,
                &self.reference_identity,
            ),
            (&self.dut_pre_fs, &self.dut_post_fs, &self.dut_identity),
        ] {
            let mut transitions = BTreeSet::new();
            for (before_path, before) in &pre.nodes {
                let key = before.host_key.ok_or("missing raw filesystem identity")?;
                for (after_path, after) in &post.nodes {
                    if after.host_key == Some(key) {
                        transitions.insert((before_path.clone(), after_path.clone()));
                    }
                }
            }
            if &transitions != identity {
                return Err("raw filesystem identity transition evidence disagrees".into());
            }
            for snapshot in [pre, post] {
                let mut aliases = BTreeSet::new();
                for (left_path, left) in &snapshot.nodes {
                    let key = left.host_key.ok_or("missing raw filesystem identity")?;
                    for (right_path, right) in snapshot.nodes.range::<String, _>((
                        std::ops::Bound::Excluded(left_path),
                        std::ops::Bound::Unbounded,
                    )) {
                        if right.host_key == Some(key) {
                            aliases.insert((left_path.clone(), right_path.clone()));
                        }
                    }
                }
                if aliases != snapshot.hardlink_aliases {
                    return Err("raw hardlink identity evidence disagrees".into());
                }
            }
            for (is_post, snapshot) in [(false, pre), (true, post)] {
                for (path, node) in &snapshot.nodes {
                    let times = node
                        .raw_times
                        .ok_or("missing raw timestamp evidence; rerun with --case-set")?;
                    if [times.atime_nsec, times.mtime_nsec, times.ctime_nsec]
                        .iter()
                        .any(|n| !(0..1_000_000_000).contains(n))
                    {
                        return Err(format!("invalid raw timestamp at {path}"));
                    }
                    let before = pre.nodes.get(path).and_then(|node| node.raw_times);
                    if node.atime != Some(atime(times))
                        || node.mtime != Some(mtime(times))
                        || node.atime_changed_from_pre
                            != (is_post && before.map(atime) != Some(atime(times)))
                        || node.mtime_changed_from_pre
                            != (is_post && before.map(mtime) != Some(mtime(times)))
                        || node.ctime_changed_from_pre
                            != (is_post && before.map(ctime) != Some(ctime(times)))
                    {
                        return Err(format!(
                            "raw timestamp transition evidence disagrees at {path}"
                        ));
                    }
                }
            }
        }
        if execution.fixture_sharing && self.reference_pre_fs != self.reference_post_fs {
            // Post transition flags are false precisely when every raw field was unchanged.
            return Err("shared fixture reference pre/post evidence differs".into());
        }
        if execution.fixture_sharing && self.reference_post_fs != self.dut_pre_fs {
            return Err("shared fixture DUT prestate differs from reference poststate".into());
        }
        Ok(())
    }

    /// Reproduces observable evidence without host allocations or timestamp metadata.
    pub(crate) fn reproduces(&self, saved: &Self) -> Result<bool, String> {
        Ok(self.replay_comparison_evidence()? == saved.replay_comparison_evidence()?)
    }

    fn replay_comparison_evidence(&self) -> Result<Self, String> {
        self.validate_time_evidence()?;
        let execution = self.execution.as_ref().expect("validated execution");
        let mut result = self.clone();
        // Runtime windows are diagnostic evidence; absolute clock readings vary across runs.
        result.execution = None;
        // Raw host keys are preserved and checked against alias/transition partitions;
        // fresh clones reproduce those partitions, not the host's inode allocations.
        for snapshot in [
            &mut result.reference_pre_fs,
            &mut result.dut_pre_fs,
            &mut result.reference_post_fs,
            &mut result.dut_post_fs,
        ] {
            for node in snapshot.nodes.values_mut() {
                node.host_key = None;
                // Time behavior is outside coverage. Preserve raw values in the bundle,
                // but do not require clock-dependent metadata to reproduce a mismatch.
                node.raw_times = None;
                node.atime = None;
                node.mtime = None;
                node.atime_changed_from_pre = false;
                node.mtime_changed_from_pre = false;
                node.ctime_changed_from_pre = false;
            }
        }
        // Preserve the reuse decision even though absolute wall-clock values vary.
        result.execution = Some(crate::fuzz::execution::ExecutionEvidence {
            fixture_sharing: execution.fixture_sharing,
            reference_window: crate::fuzz::execution::ExecutionWindow {
                start: (0, 0),
                end: (0, 0),
            },
            dut_window: crate::fuzz::execution::ExecutionWindow {
                start: (0, 0),
                end: (0, 0),
            },
        });
        Ok(result)
    }

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
    _reference_root: Option<&Path>,
    _dut_root: Option<&Path>,
    _cwd: Option<&Path>,
) -> Result<ReplayVerdict, String> {
    let (reference_stdout, dut_stdout) =
        replay_stdout_evidence(util, argv, &reference.stdout, &dut.stdout);
    let (reference_stderr, dut_stderr) = if ignore_stderr {
        (ReplayStreamEvidence::Ignored, ReplayStreamEvidence::Ignored)
    } else {
        replay_stderr_evidence(&reference.stderr, &dut.stderr)
    };
    Ok(ReplayVerdict {
        execution: None,
        comparison: compare.clone(),
        reference_process_outcome: ProcessOutcomeEvidence::Observed(reference.termination),
        dut_process_outcome: ProcessOutcomeEvidence::Observed(dut.termination),
        reference_stdout,
        dut_stdout,
        reference_stderr,
        dut_stderr,
        reference_identity: reference_identity.clone(),
        dut_identity: dut_identity.clone(),
        reference_pre_fs: replay_fs_evidence(reference_pre_fs, None, "reference pre")?,
        dut_pre_fs: replay_fs_evidence(dut_pre_fs, None, "DUT pre")?,
        reference_post_fs: replay_fs_evidence(
            reference_post_fs,
            Some(reference_pre_fs),
            "reference post",
        )?,
        dut_post_fs: replay_fs_evidence(dut_post_fs, Some(dut_pre_fs), "DUT post")?,
    })
}

fn replay_fs_evidence(
    snapshot: &FsSnapshot,
    pre_snapshot: Option<&FsSnapshot>,
    label: &str,
) -> Result<ReplayFsEvidence, String> {
    let nodes = snapshot
        .iter()
        .map(|(path, node)| {
            let pre = pre_snapshot.and_then(|snapshot| snapshot.get(path));
            let atime_changed_from_pre = pre_snapshot.is_some()
                && pre.is_none_or(|before| {
                    (before.times.atime_sec, before.times.atime_nsec)
                        != (node.times.atime_sec, node.times.atime_nsec)
                });
            let mtime_changed_from_pre = pre_snapshot.is_some()
                && pre.is_none_or(|before| {
                    (before.times.mtime_sec, before.times.mtime_nsec)
                        != (node.times.mtime_sec, node.times.mtime_nsec)
                });
            let ctime_changed_from_pre = pre_snapshot.is_some()
                && pre.is_none_or(|before| {
                    (before.times.ctime_sec, before.times.ctime_nsec)
                        != (node.times.ctime_sec, node.times.ctime_nsec)
                });
            (
                path.clone(),
                ReplayFsNodeEvidence {
                    raw_times: Some(node.times),
                    host_key: node.host_key,
                    raw_stat_metadata: node.raw_stat_metadata,
                    kind: node.kind.to_string(),
                    mode_octal: node.mode_octal.clone(),
                    atime: Some((node.times.atime_sec, node.times.atime_nsec)),
                    mtime: Some((node.times.mtime_sec, node.times.mtime_nsec)),
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

fn atime(times: crate::fuzz::FsTimes) -> (i64, i64) {
    (times.atime_sec, times.atime_nsec)
}
fn mtime(times: crate::fuzz::FsTimes) -> (i64, i64) {
    (times.mtime_sec, times.mtime_nsec)
}
fn ctime(times: crate::fuzz::FsTimes) -> (i64, i64) {
    (times.ctime_sec, times.ctime_nsec)
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
) -> Result<BTreeMap<crate::fuzz::HostInodeKeySnapshot, Vec<&'a String>>, String> {
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

fn stderr_streams_differ(reference: &[u8], dut: &[u8]) -> bool {
    reference != dut
}

fn replay_stderr_evidence(
    reference: &[u8],
    dut: &[u8],
) -> (ReplayStreamEvidence, ReplayStreamEvidence) {
    (stream_evidence(reference), stream_evidence(dut))
}

fn replay_stdout_evidence(
    util: &str,
    argv: &[String],
    reference: &[u8],
    dut: &[u8],
) -> (ReplayStreamEvidence, ReplayStreamEvidence) {
    if requests_help_or_version(util, argv) {
        return (stream_evidence(reference), stream_evidence(dut));
    }
    if util == "printenv" {
        if let Some(separator) = printenv_environment_separator(argv) {
            return (
                printenv_stdout_evidence(reference, separator),
                printenv_stdout_evidence(dut, separator),
            );
        }
    }
    (stream_evidence(reference), stream_evidence(dut))
}

/// Environment records in sorted order, bounded like other streams. A record never holds
/// the separator, so the sorted join is equal exactly when the record lists are equal.
fn printenv_stdout_evidence(data: &[u8], separator: u8) -> ReplayStreamEvidence {
    let records = normalized_printenv_records(data, separator);
    let canonical = records.join(&separator);
    if canonical.len() > STREAM_EVIDENCE_LIMIT_BYTES {
        return stream_evidence(&canonical);
    }
    ReplayStreamEvidence::Records(records)
}

fn stdout_streams_differ(util: &str, argv: &[String], reference: &[u8], dut: &[u8]) -> bool {
    if requests_help_or_version(util, argv) {
        return reference != dut;
    }
    if util == "printenv" {
        if let Some(separator) = printenv_environment_separator(argv) {
            return normalized_printenv_records(reference, separator)
                != normalized_printenv_records(dut, separator);
        }
    }
    reference != dut
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
        compare_results_with_roots, mismatch_signature, replay_stderr_evidence, stream_evidence,
        BoundedStreamEvidence, MismatchSignature, ProcessOutcomeEvidence, ReplayStreamEvidence,
        STREAM_EVIDENCE_LIMIT_BYTES,
    };
    use crate::fuzz::comparison::fs_snapshot::IdentityTransitionEvidence;
    use crate::fuzz::comparison::CompareResult;
    use crate::fuzz::{FsNodeSnapshot, FsSnapshot, FsTimes, HostInodeKeySnapshot, RunResult};
    use std::path::Path;
    use std::process::Command;

    #[cfg(unix)]
    use std::os::unix::fs::{MetadataExt, PermissionsExt};

    fn execution_windows() -> crate::fuzz::execution::ExecutionEvidence {
        use crate::fuzz::execution::{ExecutionEvidence, ExecutionWindow};
        ExecutionEvidence {
            fixture_sharing: false,
            reference_window: ExecutionWindow {
                start: (100, 0),
                end: (110, 999_999_999),
            },
            dut_window: ExecutionWindow {
                start: (200, 0),
                end: (210, 999_999_999),
            },
        }
    }

    fn timestamp_replay_fixture(reference_time: i64, dut_time: i64) -> super::ReplayVerdict {
        let pre = transition_snapshot(&[("a", Some((1, 2)))]);
        let mut reference = pre.clone();
        reference.get_mut("a").unwrap().times.mtime_sec = reference_time;
        let mut dut = pre.clone();
        dut.get_mut("a").unwrap().times.mtime_sec = dut_time;
        let mut verdict = raw_replay_fixture("cat", &pre, &pre);
        verdict.reference_post_fs =
            super::replay_fs_evidence(&reference, Some(&pre), "reference").unwrap();
        verdict.dut_post_fs = super::replay_fs_evidence(&dut, Some(&pre), "DUT").unwrap();
        verdict.reference_identity.insert(("a".into(), "a".into()));
        verdict.dut_identity = verdict.reference_identity.clone();
        verdict.execution = Some(execution_windows());
        verdict
    }

    // A claimed unchanged timestamp cannot disagree with the saved raw pre/post values.
    #[test]
    fn replay_rejects_forged_time_transition() {
        let mut verdict = timestamp_replay_fixture(100, 200);
        verdict
            .dut_post_fs
            .nodes
            .get_mut("a")
            .unwrap()
            .mtime_changed_from_pre = false;
        assert!(verdict
            .validate_time_evidence()
            .unwrap_err()
            .contains("transition evidence"));
    }

    // Raw replacement of an inode must agree with the saved identity transition partition.
    #[test]
    fn replay_rejects_forged_identity_transition() {
        let mut verdict = timestamp_replay_fixture(100, 200);
        verdict.dut_post_fs.nodes.get_mut("a").unwrap().host_key = Some(HostInodeKeySnapshot {
            device: 1,
            inode: 3,
        });
        assert!(verdict
            .validate_time_evidence()
            .unwrap_err()
            .contains("identity transition"));
    }

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
            termination: crate::fuzz::comparison::process_outcome::Termination::from_status(
                output.status,
            ),
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
                        crate::fuzz::comparison::process_outcome::Termination::Exit {
                            code: 141,
                            ..
                        }
                    ),
                    ProcessOutcomeEvidence::Observed(
                        crate::fuzz::comparison::process_outcome::Termination::Signal {
                            signal: 13,
                            ..
                        }
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
        use crate::fuzz::comparison::process_outcome::Termination;

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
            crate::fuzz::comparison::fs_snapshot::snapshot_fs_without_restore(reference_root)
                .unwrap();
        let dut_fs =
            crate::fuzz::comparison::fs_snapshot::snapshot_fs_without_restore(dut_root).unwrap();
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
            crate::fuzz::comparison::fs_snapshot::snapshot_fs_without_restore(reference_root)
                .unwrap();
        let dut_fs =
            crate::fuzz::comparison::fs_snapshot::snapshot_fs_without_restore(dut_root).unwrap();
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
        let evidence = super::replay_fs_evidence(&snapshot, None, "raw fixture").unwrap();
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

    fn raw_stream_replay(
        util: &str,
        argv: &[String],
        reference: &RunResult,
        dut: &RunResult,
        reference_fs: &FsSnapshot,
        dut_fs: &FsSnapshot,
        ignore_stderr: bool,
    ) -> super::ReplayVerdict {
        let comparison = compare_results(
            util,
            argv,
            reference,
            dut,
            reference_fs,
            dut_fs,
            ignore_stderr,
        );
        super::replay_verdict_with_roots(
            util,
            argv,
            reference,
            dut,
            &comparison,
            &IdentityTransitionEvidence::new(),
            &IdentityTransitionEvidence::new(),
            reference_fs,
            dut_fs,
            reference_fs,
            dut_fs,
            ignore_stderr,
            None,
            None,
            Some(Path::new(".")),
        )
        .unwrap()
    }

    // Numeric-long ACL markers remain raw bytes in both comparison and serialized replay evidence.
    #[test]
    fn ls_replay_preserves_raw_mode_markers_and_alignment() {
        let argv = ["-n", "--time-style=+%s"].map(str::to_string);
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r-----+ 1  1013 1013   1 2000000000 file\n".to_vec(),
            stderr: vec![],
        };
        let dut = RunResult {
            stdout: b"-rw-r----- 1  1013 1013   1 2000000000 file\n".to_vec(),
            ..reference.clone()
        };
        let replay = raw_stream_replay(
            "ls",
            &argv,
            &reference,
            &dut,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false,
        );
        assert!(matches!(
            replay.comparison,
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
        assert_eq!(
            replay.reference_stdout,
            ReplayStreamEvidence::RawBytes(reference.stdout)
        );
        assert_eq!(
            replay.dut_stdout,
            ReplayStreamEvidence::RawBytes(dut.stdout)
        );
        let restored: super::ReplayVerdict =
            serde_json::from_slice(&serde_json::to_vec(&replay).unwrap()).unwrap();
        assert_eq!(restored, replay);
    }

    // Direct ctime bytes retain their clone-local values while snapshot evidence remains untouched.
    #[test]
    fn ls_replay_preserves_direct_ctime_bytes() {
        let argv = ["-ndc", "--time-style=+%s", "file"].map(str::to_string);
        let mut reference_fs = transition_snapshot(&[("file", Some((1, 7)))]);
        reference_fs.get_mut("file").unwrap().times.ctime_sec = 100;
        let mut dut_fs = transition_snapshot(&[("file", Some((1, 8)))]);
        dut_fs.get_mut("file").unwrap().times.ctime_sec = 200;
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r--r-- 1 0 0 10 100 file\n".to_vec(),
            stderr: vec![],
        };
        let dut = RunResult {
            stdout: b"-rw-r--r-- 1 0 0 10 200 file\n".to_vec(),
            ..reference.clone()
        };
        let replay =
            raw_stream_replay("ls", &argv, &reference, &dut, &reference_fs, &dut_fs, false);
        assert!(matches!(
            replay.comparison,
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
        assert_eq!(
            replay.reference_stdout,
            ReplayStreamEvidence::RawBytes(reference.stdout)
        );
        assert_eq!(
            replay.dut_stdout,
            ReplayStreamEvidence::RawBytes(dut.stdout)
        );
        assert_eq!(
            replay.reference_pre_fs.nodes["file"].raw_times,
            Some(reference_fs["file"].times)
        );
        assert_eq!(
            replay.dut_pre_fs.nodes["file"].raw_times,
            Some(dut_fs["file"].times)
        );
    }

    // Stat replay preserves inode and ctime bytes even when snapshots establish the same alias pattern.
    #[test]
    #[cfg(unix)]
    fn stat_replay_preserves_clone_local_inode_and_ctime_bytes() {
        let reference_root = stat_hardlink_fixture();
        let dut_root = stat_hardlink_fixture();
        let argv =
            ["-L", "-c", "i=%i|Z=%Z|s=%s", "regular-link", "regular-hard"].map(str::to_string);
        let operands = ["regular-link", "regular-hard"];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(reference_root.path(), &operands, 7),
            stderr: vec![],
        };
        let dut = RunResult {
            stdout: followed_stat_output(dut_root.path(), &operands, 7),
            ..reference.clone()
        };
        let reference_fs = crate::fuzz::comparison::fs_snapshot::snapshot_fs_without_restore(
            reference_root.path(),
        )
        .unwrap();
        let dut_fs =
            crate::fuzz::comparison::fs_snapshot::snapshot_fs_without_restore(dut_root.path())
                .unwrap();
        let comparison = compare_stat_with_roots(
            &argv,
            &reference,
            &dut,
            reference_root.path(),
            dut_root.path(),
            Path::new("work"),
        );
        let replay = super::replay_verdict_with_roots(
            "stat",
            &argv,
            &reference,
            &dut,
            &comparison,
            &IdentityTransitionEvidence::new(),
            &IdentityTransitionEvidence::new(),
            &reference_fs,
            &dut_fs,
            &reference_fs,
            &dut_fs,
            false,
            Some(reference_root.path()),
            Some(dut_root.path()),
            Some(Path::new("work")),
        )
        .unwrap();
        assert!(matches!(
            replay.comparison,
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
        assert_eq!(
            replay.reference_stdout,
            ReplayStreamEvidence::RawBytes(reference.stdout)
        );
        assert_eq!(
            replay.dut_stdout,
            ReplayStreamEvidence::RawBytes(dut.stdout)
        );
        assert_eq!(
            replay.reference_pre_fs.hardlink_aliases,
            replay.dut_pre_fs.hardlink_aliases
        );
    }

    // Block-only replay retains right alignment and filename spaces as the observed stream.
    #[test]
    fn ls_replay_preserves_raw_block_alignment() {
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b" 4  file\n12 other\n".to_vec(),
            stderr: vec![],
        };
        let dut = RunResult {
            stdout: b"4  file\n12 other\n".to_vec(),
            ..reference.clone()
        };
        let replay = raw_stream_replay(
            "ls",
            &["-s".into()],
            &reference,
            &dut,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false,
        );
        assert!(matches!(
            replay.comparison,
            CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
        assert_eq!(
            replay.reference_stdout,
            ReplayStreamEvidence::RawBytes(reference.stdout)
        );
        assert_eq!(
            replay.dut_stdout,
            ReplayStreamEvidence::RawBytes(dut.stdout)
        );
    }

    // Ignoring stderr preserves stdout evidence and records the existing ignored-stream policy.
    #[test]
    fn stat_replay_honors_ignore_stderr_with_raw_stdout() {
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"file\n".to_vec(),
            stderr: b"reference\n".to_vec(),
        };
        let dut = RunResult {
            stderr: b"dut\n".to_vec(),
            ..reference.clone()
        };
        let replay = raw_stream_replay(
            "stat",
            &["-c".into(), "%n".into(), "file".into()],
            &reference,
            &dut,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            true,
        );
        assert_eq!(replay.comparison, CompareResult::Match);
        assert_eq!(
            replay.reference_stdout,
            ReplayStreamEvidence::RawBytes(reference.stdout)
        );
        assert_eq!(replay.reference_stderr, ReplayStreamEvidence::Ignored);
        assert_eq!(replay.dut_stderr, ReplayStreamEvidence::Ignored);
    }

    fn raw_replay_fixture(
        util: &str,
        reference: &FsSnapshot,
        dut: &FsSnapshot,
    ) -> super::ReplayVerdict {
        let run = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // 순차 생성된 복제 트리의 원시 변경 시각만 다르면 엄격한 파일 시스템 비교에서도 무시한다.
    #[test]
    fn chmod_compare_ignores_cross_clone_ctime_only_difference() {
        let run = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Chmod help output reports a byte difference in an otherwise successful request.
    #[test]
    fn chmod_compare_reports_one_byte_help_mismatch() {
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"help\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Requested help output preserves differing invalid UTF-8 bytes in comparison and replay.
    #[test]
    fn pwd_help_preserves_invalid_utf8_bytes_in_comparison_and_replay() {
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"Usage: pwd [OPTION]...\nReport bugs: <bugs@example.org>\x80\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            stdout: b"Usage: pwd [OPTION]...\nReport bugs: <bugs@example.org>\x81\n".to_vec(),
            ..reference.clone()
        };
        let argv = ["--help".to_string()];
        let identity = IdentityTransitionEvidence::new();
        let snapshot = FsSnapshot::new();
        let reference_root = Some(Path::new("/fixture/reference"));
        let dut_root = Some(Path::new("/fixture/dut"));
        let compare = compare_results_with_roots(
            "pwd",
            &argv,
            &reference,
            &dut,
            &identity,
            &snapshot,
            &identity,
            &snapshot,
            false,
            reference_root,
            dut_root,
            None,
        )
        .unwrap();

        assert_eq!(
            compare,
            CompareResult::Mismatch {
                process_outcome_diff: None,
                stdout_diff: true,
                stderr_diff: false,
                fs_diff: Vec::new(),
            }
        );
        assert_eq!(
            mismatch_signature(&compare, &identity, &identity),
            Some(MismatchSignature::Stdout)
        );
        let verdict = super::replay_verdict_with_roots(
            "pwd",
            &argv,
            &reference,
            &dut,
            &compare,
            &identity,
            &identity,
            &snapshot,
            &snapshot,
            &snapshot,
            &snapshot,
            false,
            reference_root,
            dut_root,
            None,
        )
        .unwrap();
        assert_eq!(
            verdict.reference_stdout,
            ReplayStreamEvidence::RawBytes(reference.stdout)
        );
        assert_eq!(
            verdict.dut_stdout,
            ReplayStreamEvidence::RawBytes(dut.stdout)
        );
    }

    // A stat format value named --help keeps stdout comparison byte-exact.
    #[test]
    fn stat_help_format_value_does_not_weaken_stdout_comparison() {
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"--help\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"--help\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"chmod: missing operand\nTry 'chmod --help' for more information.\n".to_vec(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"B=2\nA=1\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"2\n1\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Different absolute pwd output bytes remain a mismatch even when role roots are supplied.
    #[test]
    fn compare_preserves_pwd_absolute_path_bytes() {
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"/tmp/fuzz/iter-000001/ref/dir0\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            CompareResult::Mismatch {
                process_outcome_diff: None,
                stdout_diff: true,
                stderr_diff: false,
                fs_diff: Vec::new()
            }
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

    // Dafny LS must reproduce GNU's exact grouped column width, so a DUT that omits the
    // reference's size-column alignment padding is a real mismatch, not noise to collapse.
    #[test]
    fn ls_compare_rejects_missing_numeric_long_column_padding() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"total 4\n-rw-r----- 1 1013 1013    0 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"total 4\n-rw-r----- 1 1013 1013 0 2000000000 visible\n".to_vec(),
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

    // Byte-identical GNU-aligned output, including differing per-line size-column widths,
    // must match rather than being flagged semantic_mismatch by an overzealous self-check.
    #[test]
    fn ls_compare_matches_byte_identical_aligned_numeric_long_output() {
        let argv = vec!["-n".to_string()];
        let stdout = b"total 4\n\
drwxr-xr-x 2 1000 1000  40 Oct  1  2026 empty\n\
-rw-r--r-- 1 1000 1000 150 Sep 27 00:00 zzz-large\n"
            .to_vec();
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: stdout.clone(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout,
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

    // A reference ACL marker remains an exact stdout byte difference.
    #[test]
    fn ls_compare_preserves_reference_acl_mode_marker() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r-----+ 1 1013 1013 1 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            CompareResult::Mismatch {
                process_outcome_diff: None,
                stdout_diff: true,
                stderr_diff: false,
                fs_diff: Vec::new(),
            }
        );
    }

    // Permission bytes remain exact beside an ACL marker.
    #[test]
    fn ls_compare_keeps_permissions_strict_with_reference_acl_marker() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r-----+ 1 1013 1013 1 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Identical mode-marker bytes compare equally while only raw observable equality is assessed.
    #[test]
    fn ls_compare_matches_identical_mode_marker_bytes() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r-----+ 1 1013 1013 1 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = reference.clone();

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

    // Inter-field numeric-long spaces remain exact output bytes.
    #[test]
    fn ls_compare_rejects_extra_space_between_numeric_long_fields() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013 1013    1 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013 1013 1 Aug  7 12:34 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013 1013 0 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"4 -rw-r----- 1 1013 1013 0 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Different numeric-long timestamp bytes remain observable.
    #[test]
    fn ls_compare_keeps_numeric_long_values_exact() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r----- 1 1013 1013    0 2000000000 visible\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"expected-name\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"newer\nolder\n".to_vec(),
            stderr: b"reference error\n".to_vec(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(2),
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

    // Identical current LS invalid-time diagnostics, including the birth-time row, match exactly.
    #[test]
    fn ls_compare_matches_identical_invalid_time_diagnostics() {
        let argv = vec!["--time=invalid--end".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"ls: invalid argument 'invalid--end' for '--time'\nValid arguments are:\n  - 'atime', 'access', 'use'\n  - 'ctime', 'status'\n  - 'mtime', 'modification'\n  - 'birth', 'creation'\nTry 'ls --help' for more information.\n".to_vec(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"ls: invalid argument 'invalid--end' for '--time'\nValid arguments are:\n  - 'atime', 'access', 'use'\n  - 'ctime', 'status'\n  - 'mtime', 'modification'\n  - 'birth', 'creation'\nTry 'ls --help' for more information.\n".to_vec(),
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

    // A real difference on the formerly normalized LS diagnostic row remains visible.
    #[test]
    fn ls_compare_keeps_invalid_time_diagnostic_differences_strict() {
        let argv = vec!["--time=invalid--end".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"ls: invalid argument 'invalid--end' for '--time'\nValid arguments are:\n  - 'atime', 'access', 'use'\n  - 'ctime', 'status'\n  - 'mtime', 'modification'\n  - 'birth', 'creation'\nTry 'ls --help' for more information.\n".to_vec(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"ls: invalid argument 'invalid--end' for '--time'\nValid arguments are:\n  - 'atime', 'access', 'use'\n  - 'ctime', 'status'\n  - 'mtime', 'modification'\nTry 'ls --help' for more information.\n".to_vec(),
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
                stderr_diff: true,
                ..
            }
        ));
    }

    // LS replay evidence retains exact diagnostic bytes on both sides.
    #[test]
    fn ls_replay_preserves_exact_stderr_bytes() {
        let stderr = b"ls: invalid argument 'invalid--end' for '--time'\nValid arguments are:\n  - 'atime', 'access', 'use'\n  - 'ctime', 'status'\n  - 'mtime', 'modification'\n  - 'birth', 'creation'\nTry 'ls --help' for more information.\n";
        assert_eq!(stderr.len(), 211);
        assert_eq!(
            replay_stderr_evidence(stderr, stderr),
            (
                ReplayStreamEvidence::RawBytes(stderr.to_vec()),
                ReplayStreamEvidence::RawBytes(stderr.to_vec()),
            )
        );
    }

    // A ctime sort compares raw order bytes without requiring fixture roots.
    #[test]
    fn ls_compare_keeps_explicit_time_sort_order_strict() {
        let argv = vec!["-t".to_string(), "--time=status".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"newer\nolder\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Different clone-local ctime orders remain a raw observable difference.
    #[test]
    #[cfg(unix)]
    fn ls_compare_preserves_clone_local_ctime_sort_order_difference() {
        let reference_root = ls_short_ctime_sort_fixture(["cg11-soc.bin", "i4-s13q"]);
        let dut_root = ls_short_ctime_sort_fixture(["i4-s13q", "cg11-soc.bin"]);
        let argv = ["-t", "--time=ctime"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"i4-s13q\ncg11-soc.bin\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            CompareResult::Mismatch {
                process_outcome_diff: None,
                stdout_diff: true,
                stderr_diff: false,
                fs_diff: Vec::new(),
            }
        );
    }

    // Numeric-long time output remains strict even when the selected field is change time.
    #[test]
    fn ls_compare_keeps_numeric_long_change_time_strict() {
        let argv = vec!["-n".to_string(), "--time=status".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r--r-- 1 1000 1000 1 Jan  1 00:00 file\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // A direct ctime record with mtime bytes remains an observable stdout difference.
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // A size difference adjacent to direct ctime remains an observable byte difference.
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // A sorted numeric ctime output keeps its timestamp bytes exact.
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: direct_ls_epoch_output(reference_root.path(), operand, false, 1, 0),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Block-count padding and filename spacing remain exact output bytes.
    #[test]
    fn ls_compare_preserves_block_prefix_and_name_bytes() {
        let argv = vec!["-s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b" 4 visible  name\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Spaces at the start of a block-listing filename remain exact bytes.
    #[test]
    fn ls_compare_preserves_leading_spaces_in_block_names() {
        let argv = vec!["-s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"4   name\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // A different block-count column width remains an exact output byte difference.
    #[test]
    fn ls_compare_rejects_differing_block_column_padding() {
        let argv = vec!["-s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b" 4 file1\n12 file2\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            // Missing the leading padding that right-justifies "4" to the same
            // width as "12" in the reference.
            stdout: b"4 file1\n12 file2\n".to_vec(),
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

    // Byte-identical block-count columns, including differing per-line widths
    // right-justified within the same listing, must match.
    #[test]
    fn ls_compare_matches_identical_aligned_block_output() {
        let argv = vec!["-s".to_string()];
        let stdout = b" 4 file1\n12 file2\n".to_vec();
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: stdout.clone(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout,
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

    // Spaces at the start of a numeric-long filename remain exact bytes.
    #[test]
    fn ls_compare_preserves_leading_spaces_in_long_names() {
        let argv = vec!["-n".to_string(), "--time-style=+%s".to_string()];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-rw-r--r-- 1 1000 1000 1 0   name\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Clone-local inode and ctime output remains an exact byte difference.
    #[test]
    #[cfg(unix)]
    fn stat_compare_preserves_clone_local_inode_and_ctime_bytes() {
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(reference_root.path(), &operands, 7),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            CompareResult::Mismatch {
                process_outcome_diff: None,
                stdout_diff: true,
                stderr_diff: false,
                fs_diff: Vec::new(),
            }
        );
    }

    // Container-only roots do not prevent comparing transported raw output bytes.
    #[test]
    #[cfg(unix)]
    fn stat_compare_preserves_raw_difference_with_container_only_roots() {
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(reference_root.path(), &operands, 7),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(dut_root.path(), &operands, 7),
            stderr: Vec::new(),
        };
        let reference_fs = crate::fuzz::comparison::fs_snapshot::snapshot_fs_without_restore(
            reference_root.path(),
        )
        .unwrap();
        let dut_fs =
            crate::fuzz::comparison::fs_snapshot::snapshot_fs_without_restore(dut_root.path())
                .unwrap();

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

        assert_eq!(
            result,
            CompareResult::Mismatch {
                process_outcome_diff: None,
                stdout_diff: true,
                stderr_diff: false,
                fs_diff: Vec::new(),
            }
        );
    }

    // An unknown directive does not hide an adjacent inode byte difference.
    #[test]
    #[cfg(unix)]
    fn stat_compare_preserves_inode_bytes_beside_unknown_directive() {
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: format!("q=?|i={reference_inode}\n").into_bytes(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            CompareResult::Mismatch {
                process_outcome_diff: None,
                stdout_diff: true,
                stderr_diff: false,
                fs_diff: Vec::new(),
            }
        );
    }

    // Zeroed inode and ctime output differs from actual hardlink output bytes.
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(reference_root.path(), &operands, 7),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Different printed inode bytes for hardlink aliases remain observable.
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: format!(
                "i={0}|Z={1}\ni={0}|Z={1}\n",
                reference_metadata.ino(),
                reference_metadata.ctime(),
            )
            .into_bytes(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Size bytes adjacent to inode and ctime remain exact output evidence.
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: followed_stat_output(reference_root.path(), &operands, 7),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"1011700000000\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"-10-101\n".to_vec(),
            stderr: Vec::new(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
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

    // Stat error diagnostics remain exact under the ordinary stderr policy.
    #[test]
    fn stat_compare_keeps_stderr_strict() {
        let argv = vec![
            "-c".to_string(),
            "i=%i|Z=%Z".to_string(),
            "missing".to_string(),
        ];
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
            stdout: Vec::new(),
            stderr: b"stat: cannot statx 'missing': No such file or directory\n".to_vec(),
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(1),
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

    // A stderr just past the limit, like a crash's stack trace, keeps its length and both ends.
    #[test]
    fn long_stream_is_saved_as_length_digest_and_ends() {
        let half = STREAM_EVIDENCE_LIMIT_BYTES / 2;
        let mut data = vec![b'h'; half];
        data.push(b'm');
        data.extend(vec![b't'; half]);
        let ReplayStreamEvidence::Bounded(saved) = stream_evidence(&data) else {
            panic!("a stream over the limit must be bounded");
        };
        assert_eq!(saved.length, data.len() as u64);
        assert_eq!(saved.head, vec![b'h'; half]);
        assert_eq!(saved.tail, vec![b't'; half]);
        assert_eq!(saved.fnv1a64.len(), 16);
    }

    // A stream of exactly the limit is still saved byte for byte.
    #[test]
    fn stream_at_limit_is_saved_whole() {
        let data = vec![7; STREAM_EVIDENCE_LIMIT_BYTES];
        assert_eq!(stream_evidence(&data), ReplayStreamEvidence::RawBytes(data));
    }

    // The digest is standard 64-bit FNV-1a, so saved bundles stay comparable across builds.
    #[test]
    fn bounded_digest_matches_fnv1a_reference_vector() {
        assert_eq!(super::fnv1a64(b""), 0xcbf2_9ce4_8422_2325);
        assert_eq!(super::fnv1a64(b"foobar"), 0x8594_4171_f739_67e8);
    }

    // A long printenv listing is bounded in record order, so a reordered listing still matches.
    #[test]
    fn long_printenv_listing_is_bounded_in_record_order() {
        let records: Vec<Vec<u8>> = (0..20_000)
            .map(|index| format!("NAME_{index}=value").into_bytes())
            .collect();
        let forward = records.join(&b'\n');
        let backward = records
            .iter()
            .rev()
            .cloned()
            .collect::<Vec<_>>()
            .join(&b'\n');
        let (reference, dut) = super::replay_stdout_evidence("printenv", &[], &forward, &backward);
        assert!(matches!(reference, ReplayStreamEvidence::Bounded(_)));
        assert_eq!(reference, dut);
    }

    fn crash_replay(dut_stderr: Vec<u8>) -> super::ReplayVerdict {
        let reference = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(0),
            stdout: b"ok\n".to_vec(),
            stderr: vec![],
        };
        let dut = RunResult {
            termination: crate::fuzz::comparison::process_outcome::Termination::test_exit(134),
            stdout: vec![],
            stderr: dut_stderr,
        };
        let mut verdict = raw_stream_replay(
            "cat",
            &[],
            &reference,
            &dut,
            &FsSnapshot::new(),
            &FsSnapshot::new(),
            false,
        );
        verdict.execution = Some(execution_windows());
        verdict
    }

    fn stack_trace() -> Vec<u8> {
        b"   at CatCore.__default.ConcatPieces(Dafny.ISequence)\n".repeat(4096)
    }

    // Replaying the same long crash output reproduces the saved bounded evidence.
    #[test]
    fn replay_of_same_long_stream_reproduces() {
        let saved = crash_replay(stack_trace());
        assert!(matches!(
            saved.dut_stderr,
            ReplayStreamEvidence::Bounded(BoundedStreamEvidence { .. })
        ));
        let restored: super::ReplayVerdict =
            serde_json::from_slice(&serde_json::to_vec(&saved).unwrap()).unwrap();
        assert!(crash_replay(stack_trace()).reproduces(&restored).unwrap());
    }

    // A change only in the omitted middle of a long stream does not count as reproduced.
    #[test]
    fn replay_detects_change_in_omitted_middle() {
        let saved = crash_replay(stack_trace());
        let mut changed = stack_trace();
        let middle = changed.len() / 2;
        changed[middle] = b'X';
        assert!(!crash_replay(changed).reproduces(&saved).unwrap());
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
