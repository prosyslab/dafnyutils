#[cfg(test)]
use super::fixture::reset_dir;
use super::{ResolvedPaths, ResolvedTarget};
#[cfg(test)]
use crate::utils::cli::WorkdirMode;
use crate::utils::cli::{ExecKind, FuzzArgs};
#[cfg(test)]
use crate::utils::paths::sanitize_util_name;
use crate::{fuzzer_outcome_marker, FUZZER_TARGET_SPAWN_FAILURE};
use std::fs;
use std::path::{Path, PathBuf};
#[cfg(test)]
use tempfile::TempDir;

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WorkRootSource {
    Default,
    Explicit,
}

#[cfg(test)]
impl WorkRootSource {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Default => "default",
            Self::Explicit => "explicit",
        }
    }
}

#[cfg(test)]
pub(crate) struct OwnedWorkRoot {
    path: PathBuf,
    effective_base: PathBuf,
    source: WorkRootSource,
    _temporary: Option<TempDir>,
}

#[cfg(test)]
impl OwnedWorkRoot {
    pub(crate) fn path(&self) -> &Path {
        &self.path
    }

    pub(crate) fn effective_base(&self) -> &Path {
        &self.effective_base
    }

    pub(crate) fn source(&self) -> WorkRootSource {
        self.source
    }
}

#[cfg(test)]
pub(crate) fn prepare_shared_root(
    work_root: &Path,
    workdir_mode: WorkdirMode,
    seed: u64,
) -> Result<Option<PathBuf>, String> {
    if workdir_mode == WorkdirMode::Shared {
        let path = work_root.join(format!("shared-seed-{seed}-pid-{}", std::process::id()));
        reset_dir(&path)?;
        Ok(Some(path))
    } else {
        Ok(None)
    }
}

pub(crate) fn resolve_fuzz_paths(args: &FuzzArgs) -> Result<ResolvedPaths, String> {
    let util = args.common.util.as_str();
    let repo_root = current_repo_root()?;
    let reference = resolve_target(
        util,
        args.common.ref_bin.as_deref(),
        args.common.ref_kind,
        repo_root.join("_build/coreutils/src").join(util),
        "reference",
        "ref",
    )?;
    let dut = resolve_target(
        util,
        args.dut_bin.as_deref(),
        args.dut_kind,
        repo_root
            .join("_build/bench")
            .join(format!("{util}_bench.dll")),
        "dut",
        "dut",
    )?;
    Ok(ResolvedPaths { reference, dut })
}

#[cfg(test)]
pub(crate) fn work_root_for_util(util: &str) -> PathBuf {
    let safe_util = sanitize_util_name(util);
    PathBuf::from("/tmp").join(format!("{safe_util}-{}", run_workspace_hash()))
}

#[cfg(test)]
pub(crate) fn campaign_work_root(
    util: &str,
    requested_base: Option<&Path>,
) -> Result<OwnedWorkRoot, String> {
    if let Some(base) = requested_base {
        return temporary_work_root(
            &format!("coreutils-fuzzer-{}-", sanitize_util_name(util)),
            Some(base),
        );
    }

    let path = work_root_for_util(util);
    fs::create_dir_all(&path)
        .map_err(|error| format!("failed to create work root `{}`: {error}", path.display()))?;
    let effective_base = fs::canonicalize("/tmp")
        .map_err(|error| format!("failed to resolve default work root base `/tmp`: {error}"))?;
    Ok(OwnedWorkRoot {
        path,
        effective_base,
        source: WorkRootSource::Default,
        _temporary: None,
    })
}

#[cfg(test)]
pub(crate) fn temporary_work_root(
    prefix: &str,
    requested_base: Option<&Path>,
) -> Result<OwnedWorkRoot, String> {
    let (temporary, source) = if let Some(base) = requested_base {
        let canonical = canonical_explicit_work_root(base)?;
        let temporary = tempfile::Builder::new()
            .prefix(prefix)
            .tempdir_in(&canonical)
            .map_err(|error| {
                format!(
                    "failed to create private workspace in explicit work root `{}`: {error}",
                    canonical.display()
                )
            })?;
        (temporary, WorkRootSource::Explicit)
    } else {
        let temporary = tempfile::Builder::new()
            .prefix(prefix)
            .tempdir()
            .map_err(|error| format!("failed to create default private workspace: {error}"))?;
        (temporary, WorkRootSource::Default)
    };
    let path = temporary.path().to_path_buf();
    let effective_base = path
        .parent()
        .ok_or_else(|| format!("private workspace has no parent: `{}`", path.display()))?
        .canonicalize()
        .map_err(|error| {
            format!(
                "failed to resolve private workspace base `{}`: {error}",
                path.display()
            )
        })?;
    Ok(OwnedWorkRoot {
        path,
        effective_base,
        source,
        _temporary: Some(temporary),
    })
}

#[cfg(test)]
fn canonical_explicit_work_root(path: &Path) -> Result<PathBuf, String> {
    let canonical = fs::canonicalize(path).map_err(|error| {
        format!(
            "failed to resolve explicit work root `{}`: {error}",
            path.display()
        )
    })?;
    if !canonical.is_dir() {
        return Err(format!(
            "explicit work root is not a directory: `{}`",
            canonical.display()
        ));
    }
    Ok(canonical)
}

#[cfg(test)]
fn run_workspace_hash() -> String {
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let input = format!("{}:{}", cwd.display(), std::process::id());
    format!("{:016x}", fnv1a64(input.as_bytes()))
}

#[cfg(test)]
fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut hash = 0xcbf29ce484222325;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn current_repo_root() -> Result<PathBuf, String> {
    std::env::current_dir().map_err(|e| format!("failed to detect current directory: {e}"))
}

fn resolve_target(
    util: &str,
    override_path: Option<&Path>,
    kind: ExecKind,
    default_path: PathBuf,
    label: &'static str,
    override_name: &str,
) -> Result<ResolvedTarget, String> {
    if util.trim().is_empty() {
        return Err("`--util` must not be empty".to_string());
    }

    let path = resolve_path(override_path, &default_path);
    let mut errors = Vec::new();
    if !path.exists() {
        errors.push(missing_target_error(
            util,
            &path,
            override_path.is_some(),
            override_name,
        ));
    }
    if kind == ExecKind::Native && !is_executable(&path) {
        errors.push(format!(
            "{label} binary is not executable: `{}`",
            path.display()
        ));
    }

    if errors.is_empty() {
        Ok(ResolvedTarget { kind, path, label })
    } else {
        Err(format!(
            "{}\n{}",
            fuzzer_outcome_marker(FUZZER_TARGET_SPAWN_FAILURE),
            errors.join("\n")
        ))
    }
}

fn resolve_path(override_path: Option<&Path>, default_path: &Path) -> PathBuf {
    match override_path {
        Some(path) if path.is_absolute() => path.to_path_buf(),
        Some(path) => current_repo_root()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(path),
        None => default_path.to_path_buf(),
    }
}

fn missing_target_error(util: &str, path: &Path, is_override: bool, override_name: &str) -> String {
    if is_override {
        format!(
            "missing {} binary override `{}`\n  provided via --{}-bin",
            override_name.to_uppercase(),
            path.display(),
            override_name,
        )
    } else if override_name == "ref" {
        format!(
            "missing reference binary `{}`\n  build hint:\n    make build-coreutils",
            path.display()
        )
    } else {
        format!(
            "missing DUT binary `{}`\n  build hint:\n    make build TASK={util}",
            path.display()
        )
    }
}

fn is_executable(path: &Path) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        match fs::metadata(path) {
            Ok(meta) => (meta.permissions().mode() & 0o111) != 0,
            Err(_) => false,
        }
    }
    #[cfg(not(unix))]
    {
        path.is_file()
    }
}

#[cfg(test)]
mod tests {
    use super::{campaign_work_root, temporary_work_root, work_root_for_util, WorkRootSource};
    use std::fs;
    use std::path::Path;

    // An omitted campaign option retains the historical deterministic /tmp parent.
    #[test]
    fn campaign_default_retains_fixed_tmp_parent() {
        assert_eq!(work_root_for_util("cat").parent(), Some(Path::new("/tmp")));
    }

    // An explicit base owns a unique child and removes only that child on drop.
    #[test]
    fn explicit_base_owns_private_child() {
        let base = tempfile::tempdir().unwrap();
        let sentinel = base.path().join("keep");
        fs::write(&sentinel, b"keep").unwrap();
        let path = {
            let root = temporary_work_root("placement-test-", Some(base.path())).unwrap();
            assert_eq!(root.source(), WorkRootSource::Explicit);
            assert_eq!(root.effective_base(), base.path());
            assert_eq!(root.path().parent(), Some(base.path()));
            assert!(root.path().is_dir());
            root.path().to_path_buf()
        };
        assert!(!path.exists());
        assert_eq!(fs::read(&sentinel).unwrap(), b"keep");
    }

    // A missing explicit base fails instead of falling back to the default temporary directory.
    #[test]
    fn missing_explicit_base_has_no_fallback() {
        let parent = tempfile::tempdir().unwrap();
        let missing = parent.path().join("missing");
        let error = match campaign_work_root("cat", Some(&missing)) {
            Ok(_) => panic!("missing work root unexpectedly succeeded"),
            Err(error) => error,
        };
        assert!(error.contains("failed to resolve explicit work root"));
        assert!(!missing.exists());
    }

    // An explicit regular file is rejected before any private workspace is created.
    #[test]
    fn explicit_file_is_not_a_work_root() {
        let base = tempfile::tempdir().unwrap();
        let file = base.path().join("file");
        fs::write(&file, b"data").unwrap();
        let error = match campaign_work_root("cat", Some(&file)) {
            Ok(_) => panic!("file work root unexpectedly succeeded"),
            Err(error) => error,
        };
        assert!(error.contains("explicit work root is not a directory"));
    }
}
