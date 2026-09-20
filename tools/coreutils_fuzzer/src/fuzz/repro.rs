use super::compare::{MismatchSignature, ReplayVerdict};
use super::execution::IdentityTransitionEvidence;
use super::shrink::CaseEvaluation;
use super::time_coverage::{CaseVerdict, EvaluatedComparison};
use super::{CompareResult, FsSnapshot, GeneratedCase, ResolvedPaths, ResolvedTarget, RunResult};
use crate::utils::capabilities::require_fuzz_capability;
use crate::utils::chmod_campaign::current_process_umask;
use crate::utils::chmod_campaign::{canonical_process_environment, selected_chmod_umask};
use crate::utils::cli::{ExecKind, FuzzArgs, WorkdirMode};
use crate::utils::paths::sanitize_util_name;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

pub(crate) const REPRO_SCHEMA_VERSION: u32 = 6;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReproTarget {
    pub(crate) kind: ExecKind,
    pub(crate) path: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReproComparison {
    pub(crate) ignore_stderr: bool,
    pub(crate) expected_mismatch_signature: Option<MismatchSignature>,
    pub(crate) evaluated: EvaluatedComparison,
    pub(crate) expected_replay_verdict: ReplayVerdict,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReproExecutionContext {
    pub(crate) environment: BTreeMap<String, String>,
    pub(crate) umask: u32,
    pub(crate) read_only_time_anchor_seconds: Option<i64>,
    #[serde(
        default,
        deserialize_with = "deserialize_work_root_base",
        serialize_with = "serialize_work_root_base"
    )]
    pub(crate) work_root_base: Option<Option<PathBuf>>,
    pub(crate) container_image: String,
    pub(crate) container_image_id: String,
    pub(crate) target_uid: u32,
    pub(crate) target_gid: u32,
}

fn deserialize_work_root_base<'de, D>(deserializer: D) -> Result<Option<Option<PathBuf>>, D::Error>
where
    D: Deserializer<'de>,
{
    Option::<PathBuf>::deserialize(deserializer).map(Some)
}

fn serialize_work_root_base<S>(
    value: &Option<Option<PathBuf>>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    match value {
        Some(Some(path)) => path.serialize(serializer),
        None | Some(None) => serializer.serialize_none(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ToolProvenance {
    pub(crate) package_version: String,
    pub(crate) git_revision: Option<String>,
    pub(crate) git_dirty: Option<bool>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReproManifest<C = ReproComparison> {
    pub(crate) schema_version: u32,
    pub(crate) tool: ToolProvenance,
    pub(crate) seed: u64,
    pub(crate) iteration: usize,
    pub(crate) util: String,
    pub(crate) workdir_mode: WorkdirMode,
    pub(crate) process_timeout_seconds: u64,
    pub(crate) execution_context: ReproExecutionContext,
    pub(crate) case: GeneratedCase,
    pub(crate) reference: ReproTarget,
    pub(crate) dut: ReproTarget,
    pub(crate) comparison: C,
    pub(crate) diff_summary: String,
    pub(crate) reference_command: String,
    pub(crate) dut_command: String,
    pub(crate) reproduce_one_liner: String,
}

pub(crate) fn decode_manifest(bytes: &[u8]) -> Result<ReproManifest, String> {
    #[derive(Deserialize)]
    struct Version {
        schema_version: u32,
    }
    let version: Version = serde_json::from_slice(bytes)
        .map_err(|error| format!("invalid replay version: {error}"))?;
    let invalid_manifest = |error: serde_json::Error| {
        format!(
            "invalid version{} replay manifest: {error}",
            version.schema_version
        )
    };
    if version.schema_version != REPRO_SCHEMA_VERSION {
        return Err(format!(
            "unsupported replay schema version {}; supported versions: {REPRO_SCHEMA_VERSION}",
            version.schema_version
        ));
    }
    let manifest: ReproManifest = serde_json::from_slice(bytes).map_err(invalid_manifest)?;
    manifest
        .comparison
        .expected_replay_verdict
        .validate_process_outcome_consistency()
        .map_err(|error| {
            format!(
                "invalid version{} replay manifest: {error}",
                version.schema_version
            )
        })?;
    validate_manifest_work_root(&manifest)?;
    if manifest.execution_context.container_image.trim().is_empty()
        || manifest
            .execution_context
            .container_image_id
            .trim()
            .is_empty()
    {
        return Err(
            "invalid version6 replay manifest: container image provenance is empty".to_string(),
        );
    }
    Ok(manifest)
}

pub(crate) fn save_case_evaluation(
    args: &FuzzArgs,
    seed: u64,
    iteration: usize,
    paths: &ResolvedPaths,
    evaluation: &CaseEvaluation,
) -> io::Result<PathBuf> {
    save_repro(
        args,
        seed,
        iteration,
        paths,
        &evaluation.case,
        &evaluation.reference,
        &evaluation.dut,
        &evaluation.comparison.observable,
        evaluation.mismatch_signature.as_ref(),
        &evaluation.replay_verdict,
        &evaluation.pre_fs,
        &evaluation.dut_pre_fs,
        &evaluation.reference_fs,
        &evaluation.dut_fs,
        &evaluation.reference_identity,
        &evaluation.dut_identity,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn save_repro(
    args: &FuzzArgs,
    seed: u64,
    iteration: usize,
    paths: &ResolvedPaths,
    case: &GeneratedCase,
    reference: &RunResult,
    dut: &RunResult,
    compare: &CompareResult,
    mismatch_signature: Option<&MismatchSignature>,
    replay_verdict: &ReplayVerdict,
    pre_fs: &FsSnapshot,
    dut_pre_fs: &FsSnapshot,
    reference_fs: &FsSnapshot,
    dut_fs: &FsSnapshot,
    reference_identity: &IdentityTransitionEvidence,
    dut_identity: &IdentityTransitionEvidence,
) -> io::Result<PathBuf> {
    let root = std::env::var_os("FUZZ_REPRO_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/tmp/coreutils-fuzzer-repros"));
    save_repro_at(
        &root,
        args,
        seed,
        iteration,
        paths,
        case,
        reference,
        dut,
        compare,
        mismatch_signature,
        replay_verdict,
        pre_fs,
        dut_pre_fs,
        reference_fs,
        dut_fs,
        reference_identity,
        dut_identity,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn save_repro_at(
    root: &Path,
    args: &FuzzArgs,
    seed: u64,
    iteration: usize,
    paths: &ResolvedPaths,
    case: &GeneratedCase,
    reference: &RunResult,
    dut: &RunResult,
    compare: &CompareResult,
    mismatch_signature: Option<&MismatchSignature>,
    replay_verdict: &ReplayVerdict,
    pre_fs: &FsSnapshot,
    dut_pre_fs: &FsSnapshot,
    reference_fs: &FsSnapshot,
    dut_fs: &FsSnapshot,
    reference_identity: &IdentityTransitionEvidence,
    dut_identity: &IdentityTransitionEvidence,
) -> io::Result<PathBuf> {
    let util = &args.common.util;
    let evaluated = EvaluatedComparison::without_time_observations(
        compare.clone(),
        require_fuzz_capability(util)
            .map_err(io::Error::other)?
            .time_coverage,
    );
    let mismatch_signature = mismatch_signature.copied();
    if evaluated.verdict() == CaseVerdict::Match
        || (evaluated.verdict() == CaseVerdict::Mismatch && mismatch_signature.is_none())
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "cannot save a replay bundle without a mismatch or incomplete coverage",
        ));
    }
    replay_verdict
        .validate_process_outcome_consistency()
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidInput, error))?;
    let execution_context = repro_execution_context(args, seed, iteration)?;
    let base_name = format!(
        "{}-seed{}-iter{}",
        sanitize_util_name(util),
        seed,
        iteration
    );
    let path = unique_repro_path(root, &base_name)?;

    let ref_cmd = format_target_command(&paths.reference, &case.argv);
    let dut_cmd = format_target_command(&paths.dut, &case.argv);
    let diff_summary = render_diff_summary(compare, reference, dut);
    let repro_one_liner = build_repro_one_liner(&path, &execution_context);
    let manifest = ReproManifest {
        schema_version: REPRO_SCHEMA_VERSION,
        tool: tool_provenance(),
        seed,
        iteration,
        util: util.clone(),
        workdir_mode: args.common.workdir_mode,
        process_timeout_seconds: args.process_timeout_seconds,
        execution_context,
        case: case.clone(),
        reference: ReproTarget {
            kind: paths.reference.kind,
            path: paths.reference.path.clone(),
        },
        dut: ReproTarget {
            kind: paths.dut.kind,
            path: paths.dut.path.clone(),
        },
        comparison: ReproComparison {
            ignore_stderr: args.ignore_stderr,
            expected_mismatch_signature: mismatch_signature,
            evaluated,
            expected_replay_verdict: replay_verdict.clone(),
        },
        diff_summary,
        reference_command: ref_cmd,
        dut_command: dut_cmd,
        reproduce_one_liner: repro_one_liner,
    };

    write_json(path.join("manifest.json"), &manifest)?;
    write_json(path.join("case.json"), case)?;
    write_json(path.join("compare.json"), compare)?;
    write_json(path.join("mismatch_signature.json"), &mismatch_signature)?;
    write_json(path.join("pre_fs.json"), pre_fs)?;
    write_json(path.join("dut_pre_fs.json"), dut_pre_fs)?;
    write_json(path.join("reference_result.json"), reference)?;
    write_json(path.join("dut_result.json"), dut)?;
    write_json(path.join("reference_fs.json"), reference_fs)?;
    write_json(path.join("dut_fs.json"), dut_fs)?;
    write_json(
        path.join("reference_identity_transitions.json"),
        reference_identity,
    )?;
    write_json(path.join("dut_identity_transitions.json"), dut_identity)?;
    fs::write(path.join("stdin.bin"), &case.stdin)?;
    fs::write(path.join("reference.stdout"), &reference.stdout)?;
    fs::write(path.join("reference.stderr"), &reference.stderr)?;
    fs::write(path.join("dut.stdout"), &dut.stdout)?;
    fs::write(path.join("dut.stderr"), &dut.stderr)?;
    fs::write(
        path.join("reproduce.sh"),
        manifest.reproduce_one_liner.as_bytes(),
    )?;

    eprintln!("  repro saved to {}", path.display());
    Ok(path)
}

fn repro_execution_context(
    args: &FuzzArgs,
    seed: u64,
    iteration: usize,
) -> io::Result<ReproExecutionContext> {
    let is_read_only = matches!(args.common.util.as_str(), "ls" | "stat");
    if is_read_only != args.read_only_time_anchor_seconds.is_some() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "ls/stat replay evidence requires one captured timestamp anchor, and other utilities must not set one",
        ));
    }
    let work_root_base = args.common.work_root.clone().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "current replay evidence requires an effective work-root base",
        )
    })?;
    validate_saved_work_root_path(&work_root_base).map_err(io::Error::other)?;
    #[cfg(test)]
    let test_image_id = Some("local-test".to_string());
    #[cfg(not(test))]
    let test_image_id = None;
    let container_image_id = args
        .container_image_id
        .clone()
        .or(test_image_id)
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "current replay evidence requires a resolved container image id",
            )
        })?;
    Ok(ReproExecutionContext {
        environment: canonical_process_environment(),
        umask: if args.common.util == "chmod" {
            selected_chmod_umask(seed, iteration)
        } else {
            match args.process_umask {
                Some(umask) => umask,
                None => current_process_umask().map_err(io::Error::other)?,
            }
        },
        read_only_time_anchor_seconds: args.read_only_time_anchor_seconds,
        work_root_base: Some(Some(work_root_base)),
        container_image: args.common.container_image.clone(),
        container_image_id,
        target_uid: args.common.target_uid,
        target_gid: args.common.target_gid,
    })
}

fn validate_manifest_work_root(manifest: &ReproManifest) -> Result<(), String> {
    match manifest.execution_context.work_root_base.as_ref() {
        Some(Some(path)) => validate_saved_work_root_path(path),
        None => Err("invalid version6 replay manifest: missing work-root base".to_string()),
        Some(None) => Err("invalid version6 replay manifest: null work-root base".to_string()),
    }
}

fn validate_saved_work_root_path(path: &Path) -> Result<(), String> {
    if !path.is_absolute() {
        return Err(format!(
            "invalid version6 replay manifest: work-root base must be absolute: `{}`",
            path.display()
        ));
    }
    if path.components().any(|component| {
        matches!(
            component,
            Component::CurDir | Component::ParentDir | Component::Prefix(_)
        )
    }) || path.components().collect::<PathBuf>().as_os_str() != path.as_os_str()
    {
        return Err(format!(
            "invalid version6 replay manifest: work-root base must be normalized: `{}`",
            path.display()
        ));
    }
    Ok(())
}

fn unique_repro_path(root: &Path, base_name: &str) -> io::Result<PathBuf> {
    fs::create_dir_all(root)?;
    for attempt in 1usize.. {
        let name = if attempt == 1 {
            base_name.to_string()
        } else {
            format!("{base_name}-run{attempt}")
        };
        let path = root.join(name);
        match fs::create_dir(&path) {
            Ok(()) => return Ok(path),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error),
        }
    }
    unreachable!("unbounded repro suffix search")
}

fn write_json(path: PathBuf, value: &impl Serialize) -> io::Result<()> {
    let bytes = serde_json::to_vec_pretty(value).map_err(io::Error::other)?;
    fs::write(path, bytes)
}

pub(crate) fn tool_provenance() -> ToolProvenance {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    ToolProvenance {
        package_version: env!("CARGO_PKG_VERSION").to_string(),
        git_revision: git_stdout(&repo_root, &["rev-parse", "HEAD"]),
        git_dirty: git_stdout(
            &repo_root,
            &["status", "--short", "--", "tools/coreutils_fuzzer"],
        )
        .map(|output| !output.is_empty()),
    }
}

fn git_stdout(repo_root: &Path, args: &[&str]) -> Option<String> {
    let output = Command::new("git")
        .arg("-C")
        .arg(repo_root)
        .args(args)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    String::from_utf8(output.stdout)
        .ok()
        .map(|text| text.trim().to_string())
}

fn render_diff_summary(compare: &CompareResult, reference: &RunResult, dut: &RunResult) -> String {
    match compare {
        CompareResult::Match => "none".to_string(),
        CompareResult::Mismatch {
            process_outcome_diff,
            stdout_diff,
            stderr_diff,
            fs_diff,
        } => {
            let mut lines = Vec::new();
            if let Some((reference_outcome, dut_outcome)) = process_outcome_diff {
                lines.push(format!(
                    "process_outcome: ref={reference_outcome:?} dut={dut_outcome:?}"
                ));
            } else {
                lines.push(format!(
                    "process_outcome: same ({:?})",
                    reference.termination
                ));
            }

            if *stdout_diff {
                lines.push(format!(
                    "stdout: differs (ref={} bytes, dut={} bytes)",
                    reference.stdout.len(),
                    dut.stdout.len()
                ));
            } else {
                lines.push(format!("stdout: same ({} bytes)", reference.stdout.len()));
            }

            if *stderr_diff {
                lines.push(format!(
                    "stderr: differs (ref={} bytes, dut={} bytes)",
                    reference.stderr.len(),
                    dut.stderr.len()
                ));
            } else {
                lines.push(format!("stderr: same ({} bytes)", reference.stderr.len()));
            }

            if fs_diff.is_empty() {
                lines.push("fs: same".to_string());
            } else {
                lines.push(format!("fs: differs ({})", fs_diff.join("; ")));
            }

            lines.join("\n")
        }
    }
}

fn build_repro_one_liner(path: &Path, context: &ReproExecutionContext) -> String {
    format!(
        "python3 tools/coreutils_fuzzer/run.py replay {} --container-image {}",
        shell_quote(&path.display().to_string()),
        shell_quote(&context.container_image_id),
    )
}

fn format_target_command(target: &ResolvedTarget, argv: &[String]) -> String {
    match target.kind {
        ExecKind::Native => {
            let mut parts = vec![target.path.display().to_string()];
            parts.extend(argv.iter().cloned());
            shell_join(&parts)
        }
        ExecKind::DotnetDll => {
            let mut parts = vec!["dotnet".to_string(), target.path.display().to_string()];
            parts.extend(argv.iter().cloned());
            shell_join(&parts)
        }
    }
}

fn shell_join(parts: &[String]) -> String {
    parts
        .iter()
        .map(|p| shell_quote(p))
        .collect::<Vec<_>>()
        .join(" ")
}

fn shell_quote(input: &str) -> String {
    if input
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || "/._-".contains(c))
    {
        input.to_string()
    } else {
        format!("'{}'", input.replace('\'', "'\"'\"'"))
    }
}

#[cfg(test)]
mod tests {
    use super::{build_repro_one_liner, validate_saved_work_root_path, ReproExecutionContext};
    use std::collections::BTreeMap;
    use std::path::{Path, PathBuf};

    // Saved provenance accepts a normalized absolute path without requiring it to exist.
    #[test]
    fn saved_work_root_validation_does_not_access_host_path() {
        validate_saved_work_root_path(Path::new(
            "/definitely-not-present/coreutils-fuzzer-work-root",
        ))
        .unwrap();
    }

    // A relative saved base cannot masquerade as normalized host provenance.
    #[test]
    fn saved_work_root_rejects_relative_path() {
        let error = validate_saved_work_root_path(Path::new("relative/root")).unwrap_err();
        assert!(error.contains("must be absolute"));
    }

    // Parent traversal is rejected from saved bytes without resolving the named path.
    #[test]
    fn saved_work_root_rejects_parent_component() {
        let error = validate_saved_work_root_path(Path::new("/tmp/../outside")).unwrap_err();
        assert!(error.contains("must be normalized"));
    }

    // Redundant path syntax is rejected instead of being silently canonicalized.
    #[test]
    fn saved_work_root_rejects_redundant_separator() {
        let error = validate_saved_work_root_path(Path::new("/tmp//nested")).unwrap_err();
        assert!(error.contains("must be normalized"));
    }

    // The generated replay command quotes the bundle and immutable image identity.
    #[test]
    fn replay_command_quotes_saved_container_image() {
        let context = ReproExecutionContext {
            environment: BTreeMap::new(),
            umask: 0o022,
            read_only_time_anchor_seconds: None,
            work_root_base: Some(Some(PathBuf::from("/fuzz"))),
            container_image: "tag".to_string(),
            container_image_id: "sha256:image with quote's".to_string(),
            target_uid: 2001,
            target_gid: 3001,
        };
        let command = build_repro_one_liner(Path::new("/tmp/bundle with quote's"), &context);
        assert_eq!(
            command,
            "python3 tools/coreutils_fuzzer/run.py replay '/tmp/bundle with quote'\"'\"'s' --container-image 'sha256:image with quote'\"'\"'s'"
        );
    }
}
