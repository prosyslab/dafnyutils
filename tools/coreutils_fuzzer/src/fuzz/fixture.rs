use super::execution::{
    control_chmod_fixture_node, restore_path_times, suppress_fixture_atime_updates_for_node,
    times_from_metadata,
};
use super::{DirSpec, FixtureBlueprint, FsTimes, HostInodeKeySnapshot};
use crate::utils::paths::format_path_error;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

const READ_ONLY_DAY_SECONDS: i64 = 86_400;
const READ_ONLY_RECENT_WINDOW_SECONDS: i64 = 15_778_476;
const READ_ONLY_TIME_PROFILES: [(i64, i64, i64, i64); 3] = [
    (
        -READ_ONLY_DAY_SECONDS,
        123_456_789,
        -2 * READ_ONLY_RECENT_WINDOW_SECONDS,
        234_567_890,
    ),
    (
        -2 * READ_ONLY_RECENT_WINDOW_SECONDS - READ_ONLY_DAY_SECONDS,
        345_678_901,
        2 * READ_ONLY_DAY_SECONDS,
        456_789_012,
    ),
    (
        3 * READ_ONLY_DAY_SECONDS,
        567_890_123,
        -2 * READ_ONLY_DAY_SECONDS,
        678_901_234,
    ),
];

pub(crate) fn reset_dir(path: &Path) -> Result<(), String> {
    if path.exists() {
        remove_dir_forcefully(path)?;
    }
    fs::create_dir_all(path).map_err(|e| format_path_error("create directory", path, e))?;
    Ok(())
}

pub(crate) fn prepare_iteration_dirs(
    work_root: &Path,
    shared_root: Option<&Path>,
    iteration: usize,
    fixture: &FixtureBlueprint,
    control_chmod_times: bool,
) -> Result<(PathBuf, PathBuf), String> {
    let (ref_dir, dut_dir) = stage_iteration_dirs(
        work_root,
        shared_root,
        iteration,
        fixture,
        control_chmod_times,
    )?;
    apply_fixture_modes(&ref_dir, fixture)?;
    apply_fixture_modes(&dut_dir, fixture)?;
    Ok((ref_dir, dut_dir))
}

#[cfg(test)]
pub(crate) fn prepare_read_only_iteration_dirs(
    work_root: &Path,
    shared_root: Option<&Path>,
    iteration: usize,
    fixture: &FixtureBlueprint,
) -> Result<(PathBuf, PathBuf), String> {
    prepare_read_only_iteration_dirs_at(
        work_root,
        shared_root,
        iteration,
        fixture,
        current_read_only_time_anchor()?,
    )
}

pub(crate) fn prepare_read_only_iteration_dirs_at(
    work_root: &Path,
    shared_root: Option<&Path>,
    iteration: usize,
    fixture: &FixtureBlueprint,
    time_anchor_seconds: i64,
) -> Result<(PathBuf, PathBuf), String> {
    validate_read_only_time_anchor(time_anchor_seconds)?;
    let (ref_dir, dut_dir) =
        stage_iteration_dirs(work_root, shared_root, iteration, fixture, false)?;
    suppress_fixture_atime_updates(&ref_dir)?;
    suppress_fixture_atime_updates(&dut_dir)?;
    #[cfg(unix)]
    apply_read_only_time_profiles(&ref_dir, &dut_dir, time_anchor_seconds)?;
    apply_fixture_modes(&ref_dir, fixture)?;
    apply_fixture_modes(&dut_dir, fixture)?;
    Ok((ref_dir, dut_dir))
}

pub(crate) fn current_read_only_time_anchor() -> Result<i64, String> {
    use std::time::{SystemTime, UNIX_EPOCH};

    let elapsed = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| format!("failed to determine read-only fixture time anchor: {error}"))?;
    let now = i64::try_from(elapsed.as_secs())
        .map_err(|error| format!("read-only fixture time anchor is out of range: {error}"))?;
    Ok(now - now.rem_euclid(READ_ONLY_DAY_SECONDS))
}

pub(crate) fn validate_read_only_time_anchor(anchor: i64) -> Result<(), String> {
    if anchor.rem_euclid(READ_ONLY_DAY_SECONDS) != 0 {
        return Err(format!(
            "read-only fixture time anchor must be day-aligned: {anchor}"
        ));
    }
    for (atime_offset, _, mtime_offset, _) in READ_ONLY_TIME_PROFILES {
        anchor
            .checked_add(atime_offset)
            .ok_or_else(|| format!("read-only fixture time anchor is out of range: {anchor}"))?;
        anchor
            .checked_add(mtime_offset)
            .ok_or_else(|| format!("read-only fixture time anchor is out of range: {anchor}"))?;
    }
    Ok(())
}

pub(crate) fn stage_iteration_dirs(
    work_root: &Path,
    shared_root: Option<&Path>,
    iteration: usize,
    fixture: &FixtureBlueprint,
    control_chmod_times: bool,
) -> Result<(PathBuf, PathBuf), String> {
    let root_path = prepare_iteration_root(work_root, shared_root, iteration)?;
    let base_dir = root_path.join("base");
    let ref_dir = root_path.join("ref");
    let dut_dir = root_path.join("dut");

    reset_dir(&base_dir)?;
    materialize_fixture(&base_dir, fixture)?;

    #[cfg(unix)]
    {
        make_tree_owner_writable(&base_dir).map_err(|e| {
            format!(
                "failed to ensure base fixture readability `{}`: {e}",
                base_dir.display()
            )
        })?;
    }

    clone_fixture_tree(&base_dir, &ref_dir)?;
    clone_fixture_tree(&base_dir, &dut_dir)?;
    #[cfg(unix)]
    synchronize_clone_times(&ref_dir, &dut_dir)?;
    if control_chmod_times {
        control_chmod_fixture_tree(&ref_dir)?;
        control_chmod_fixture_tree(&dut_dir)?;
    }
    Ok((ref_dir, dut_dir))
}

#[cfg(unix)]
fn collect_fixture_nodes(
    root: &Path,
) -> Result<Vec<(PathBuf, FsTimes, bool, HostInodeKeySnapshot)>, String> {
    fn visit(
        root: &Path,
        current: &Path,
        nodes: &mut Vec<(PathBuf, FsTimes, bool, HostInodeKeySnapshot)>,
    ) -> Result<(), String> {
        use std::os::unix::fs::MetadataExt;

        let metadata = fs::symlink_metadata(current)
            .map_err(|error| format_path_error("read cloned fixture metadata", current, error))?;
        let file_type = metadata.file_type();
        let times = times_from_metadata(&metadata);
        let relative_path = current
            .strip_prefix(root)
            .map_err(|error| {
                format!(
                    "failed to make cloned fixture path `{}` relative to `{}`: {error}",
                    current.display(),
                    root.display()
                )
            })?
            .to_path_buf();
        nodes.push((
            relative_path,
            times,
            file_type.is_symlink(),
            HostInodeKeySnapshot {
                device: metadata.dev(),
                inode: metadata.ino(),
            },
        ));

        if file_type.is_dir() {
            let mut children = fs::read_dir(current)
                .map_err(|error| {
                    format_path_error("read cloned fixture directory", current, error)
                })?
                .map(|entry| {
                    entry.map(|entry| entry.path()).map_err(|error| {
                        format_path_error("read cloned fixture directory entry", current, error)
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            children.sort();
            for child in children {
                visit(root, &child, nodes)?;
            }
        }
        Ok(())
    }

    let mut nodes = Vec::new();
    visit(root, root, &mut nodes)?;
    Ok(nodes)
}

#[cfg(unix)]
fn synchronize_clone_times(reference: &Path, dut: &Path) -> Result<(), String> {
    let captured = collect_fixture_nodes(reference)?;
    for (relative_path, times, is_symlink, _) in captured.iter().rev() {
        restore_path_times(&reference.join(relative_path), *times, *is_symlink)?;
        restore_path_times(&dut.join(relative_path), *times, *is_symlink)?;
    }
    Ok(())
}

#[cfg(unix)]
fn apply_read_only_time_profiles(reference: &Path, dut: &Path, anchor: i64) -> Result<(), String> {
    let reference_nodes = collect_fixture_nodes(reference)?;
    let dut_nodes: BTreeMap<_, _> = collect_fixture_nodes(dut)?
        .into_iter()
        .map(|(path, _, is_symlink, host_key)| (path, (is_symlink, host_key)))
        .collect();
    if reference_nodes.len() != dut_nodes.len() {
        return Err("reference and DUT fixture trees differ before time profiling".to_string());
    }

    let mut reference_to_dut = BTreeMap::new();
    let mut dut_to_reference = BTreeMap::new();
    let mut representatives = Vec::new();
    for (relative_path, _, reference_is_symlink, reference_key) in reference_nodes {
        let Some((dut_is_symlink, dut_key)) = dut_nodes.get(&relative_path).copied() else {
            return Err(format!(
                "DUT fixture is missing `{}` before time profiling",
                relative_path.display()
            ));
        };
        if reference_is_symlink != dut_is_symlink {
            return Err(format!(
                "fixture node kind differs at `{}` before time profiling",
                relative_path.display()
            ));
        }
        if let Some(mapped) = reference_to_dut.get(&reference_key) {
            if *mapped != dut_key {
                return Err(format!(
                    "DUT fixture splits a hard-link alias at `{}` before time profiling",
                    relative_path.display()
                ));
            }
        } else {
            reference_to_dut.insert(reference_key, dut_key);
            representatives.push((relative_path.clone(), reference_is_symlink));
        }
        if let Some(mapped) = dut_to_reference.get(&dut_key) {
            if *mapped != reference_key {
                return Err(format!(
                    "DUT fixture merges distinct inodes at `{}` before time profiling",
                    relative_path.display()
                ));
            }
        } else {
            dut_to_reference.insert(dut_key, reference_key);
        }
    }

    for (profile_index, (relative_path, is_symlink)) in representatives.into_iter().enumerate() {
        let (atime_offset, atime_nsec, mtime_offset, mtime_nsec) =
            READ_ONLY_TIME_PROFILES[profile_index % READ_ONLY_TIME_PROFILES.len()];
        let times = FsTimes {
            atime_sec: anchor
                .checked_add(atime_offset)
                .ok_or_else(|| "read-only atime profile overflowed".to_string())?,
            atime_nsec,
            mtime_sec: anchor
                .checked_add(mtime_offset)
                .ok_or_else(|| "read-only mtime profile overflowed".to_string())?,
            mtime_nsec,
            // restore_path_times changes only atime and mtime; ctime remains host-controlled.
            ctime_sec: 0,
            ctime_nsec: 0,
        };
        restore_path_times(&reference.join(&relative_path), times, is_symlink)?;
        restore_path_times(&dut.join(&relative_path), times, is_symlink)?;
        for (label, path) in [
            ("reference", reference.join(&relative_path)),
            ("DUT", dut.join(&relative_path)),
        ] {
            let observed = times_from_metadata(&fs::symlink_metadata(&path).map_err(|error| {
                format_path_error("verify read-only fixture times", &path, error)
            })?);
            if (
                observed.atime_sec,
                observed.atime_nsec,
                observed.mtime_sec,
                observed.mtime_nsec,
            ) != (
                times.atime_sec,
                times.atime_nsec,
                times.mtime_sec,
                times.mtime_nsec,
            ) {
                return Err(format!(
                    "{label} fixture did not preserve the requested time profile at `{}`",
                    relative_path.display()
                ));
            }
        }
    }
    Ok(())
}

fn control_chmod_fixture_tree(root: &Path) -> Result<(), String> {
    control_fixture_tree(root, control_chmod_fixture_node)
}

pub(crate) fn suppress_fixture_atime_updates(root: &Path) -> Result<(), String> {
    control_fixture_tree(root, suppress_fixture_atime_updates_for_node)
}

fn control_fixture_tree(
    root: &Path,
    control_node: fn(&Path, bool) -> Result<(), String>,
) -> Result<(), String> {
    fn visit(
        path: &Path,
        control_node: fn(&Path, bool) -> Result<(), String>,
    ) -> Result<(), String> {
        let metadata = fs::symlink_metadata(path)
            .map_err(|error| format_path_error("read fixture metadata", path, error))?;
        let file_type = metadata.file_type();
        control_node(path, file_type.is_symlink())?;
        if file_type.is_dir() {
            let mut children = fs::read_dir(path)
                .map_err(|error| format_path_error("read fixture directory", path, error))?
                .map(|entry| {
                    entry.map(|entry| entry.path()).map_err(|error| {
                        format_path_error("read fixture directory entry", path, error)
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            children.sort();
            for child in children {
                visit(&child, control_node)?;
            }
        }
        Ok(())
    }

    visit(root, control_node)
}

pub(crate) fn materialize_fixture(root: &Path, fixture: &FixtureBlueprint) -> Result<(), String> {
    validate_fixture(fixture)?;
    for dir in &fixture.directories {
        let path = root.join(&dir.relative_path);
        fs::create_dir_all(&path).map_err(|e| format_path_error("create fixture dir", &path, e))?;
    }
    for file in &fixture.files {
        let path = root.join(&file.relative_path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                format!(
                    "failed to create fixture dir `{}` for `{}`: {e}",
                    parent.display(),
                    path.display()
                )
            })?;
        }
        fs::write(&path, &file.bytes)
            .map_err(|e| format_path_error("write fixture file", &path, e))?;
    }

    for symlink_spec in &fixture.symlinks {
        let path = root.join(&symlink_spec.relative_path);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                format!(
                    "failed to create fixture dir `{}` for symlink `{}`: {e}",
                    parent.display(),
                    path.display()
                )
            })?;
        }
        create_fixture_symlink(&symlink_spec.target, &path)?;
    }

    for hardlink in &fixture.hardlinks {
        let source = root.join(&hardlink.source_relative_path);
        let destination = root.join(&hardlink.relative_path);
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format_path_error("create hardlink parent", parent, e))?;
        }
        fs::hard_link(&source, &destination)
            .map_err(|e| format_path_error("create fixture hardlink", &destination, e))?;
    }

    apply_fixture_modes(root, fixture)?;

    Ok(())
}

pub(crate) fn validate_fixture(fixture: &FixtureBlueprint) -> Result<(), String> {
    let mut destinations = BTreeSet::new();
    for (kind, path) in fixture
        .directories
        .iter()
        .map(|entry| ("directory", entry.relative_path.as_path()))
        .chain(
            fixture
                .files
                .iter()
                .map(|entry| ("file", entry.relative_path.as_path())),
        )
        .chain(
            fixture
                .symlinks
                .iter()
                .map(|entry| ("symlink", entry.relative_path.as_path())),
        )
        .chain(
            fixture
                .hardlinks
                .iter()
                .map(|entry| ("hardlink", entry.relative_path.as_path())),
        )
    {
        if !is_safe_fixture_path(path) {
            return Err(format!("invalid fixture {kind} path `{}`", path.display()));
        }
        if !destinations.insert(path) {
            return Err(format!("duplicate fixture path `{}`", path.display()));
        }
    }

    for symlink in &fixture.symlinks {
        if !symlink_target_stays_within_fixture(&symlink.relative_path, &symlink.target) {
            return Err(format!(
                "fixture symlink target escapes fixture root: `{}` -> `{}`",
                symlink.relative_path.display(),
                symlink.target.display()
            ));
        }
    }
    let sources: BTreeSet<&Path> = fixture
        .files
        .iter()
        .map(|entry| entry.relative_path.as_path())
        .chain(
            fixture
                .symlinks
                .iter()
                .map(|entry| entry.relative_path.as_path()),
        )
        .collect();
    let declared_symlink_paths: BTreeSet<&Path> = fixture
        .symlinks
        .iter()
        .map(|entry| entry.relative_path.as_path())
        .collect();
    let non_directory_paths: BTreeSet<&Path> = fixture
        .files
        .iter()
        .map(|entry| entry.relative_path.as_path())
        .chain(
            fixture
                .symlinks
                .iter()
                .map(|entry| entry.relative_path.as_path()),
        )
        .chain(
            fixture
                .hardlinks
                .iter()
                .map(|entry| entry.relative_path.as_path()),
        )
        .collect();
    let symlink_paths: BTreeSet<&Path> = declared_symlink_paths
        .iter()
        .copied()
        .chain(
            fixture
                .hardlinks
                .iter()
                .filter(|hardlink| {
                    declared_symlink_paths.contains(hardlink.source_relative_path.as_path())
                })
                .map(|hardlink| hardlink.relative_path.as_path()),
        )
        .collect();

    for hardlink in &fixture.hardlinks {
        if !is_safe_fixture_path(&hardlink.source_relative_path) {
            return Err(format!(
                "invalid fixture hardlink source `{}`",
                hardlink.source_relative_path.display()
            ));
        }
        for path in [&hardlink.relative_path, &hardlink.source_relative_path] {
            if path
                .ancestors()
                .skip(1)
                .any(|ancestor| symlink_paths.contains(ancestor))
            {
                return Err(format!(
                    "fixture hardlink path crosses symlink `{}`",
                    path.display()
                ));
            }
        }
        if !sources.contains(hardlink.source_relative_path.as_path()) {
            return Err(format!(
                "missing or unsupported fixture hardlink source `{}`",
                hardlink.source_relative_path.display()
            ));
        }
    }

    for path in destinations {
        if path
            .ancestors()
            .skip(1)
            .any(|ancestor| declared_symlink_paths.contains(ancestor))
        {
            return Err(format!("fixture path crosses symlink `{}`", path.display()));
        }
        if path
            .ancestors()
            .skip(1)
            .any(|ancestor| non_directory_paths.contains(ancestor))
        {
            return Err(format!(
                "fixture path crosses non-directory entry `{}`",
                path.display()
            ));
        }
    }
    Ok(())
}

fn symlink_target_stays_within_fixture(link: &Path, target: &Path) -> bool {
    if target.as_os_str().is_empty() || target.is_absolute() {
        return false;
    }
    let mut depth = link
        .parent()
        .map_or(0, |parent| parent.components().count());
    for component in target.components() {
        match component {
            Component::Normal(_) => depth += 1,
            Component::CurDir => {}
            Component::ParentDir if depth > 0 => depth -= 1,
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => return false,
        }
    }
    true
}

fn is_safe_fixture_path(path: &Path) -> bool {
    !path.as_os_str().is_empty()
        && !path.is_absolute()
        && !path.components().any(|component| {
            matches!(
                component,
                Component::CurDir
                    | Component::ParentDir
                    | Component::RootDir
                    | Component::Prefix(_)
            )
        })
}

fn prepare_iteration_root(
    work_root: &Path,
    shared_root: Option<&Path>,
    iteration: usize,
) -> Result<PathBuf, String> {
    let root = if let Some(shared) = shared_root {
        shared.join(format!("iter-{iteration:06}"))
    } else {
        work_root.join(format!("iter-{iteration:06}"))
    };
    reset_dir(&root)?;
    Ok(root)
}

fn clone_fixture_tree(source: &Path, destination: &Path) -> Result<(), String> {
    reset_dir(destination)?;
    let status = Command::new("cp")
        .arg("-a")
        .arg(source.join("."))
        .arg(destination)
        .status()
        .map_err(|e| {
            format!(
                "failed to launch fixture clone command from `{}` to `{}`: {e}",
                source.display(),
                destination.display()
            )
        })?;
    if !status.success() {
        return Err(format!(
            "fixture clone command failed from `{}` to `{}` with status {:?}",
            source.display(),
            destination.display(),
            status.code()
        ));
    }
    Ok(())
}

pub(crate) fn apply_fixture_modes(root: &Path, fixture: &FixtureBlueprint) -> Result<(), String> {
    for file in &fixture.files {
        let path = root.join(&file.relative_path);
        apply_entry_mode(&path, file.mode, "file")?;
    }

    let mut dirs_by_depth: Vec<&DirSpec> = fixture.directories.iter().collect();
    dirs_by_depth.sort_by(|left, right| {
        right
            .relative_path
            .components()
            .count()
            .cmp(&left.relative_path.components().count())
    });
    for dir in dirs_by_depth {
        let path = root.join(&dir.relative_path);
        apply_entry_mode(&path, dir.mode, "directory")?;
    }

    Ok(())
}

pub(crate) fn set_fixture_owner(root: &Path, uid: u32, gid: u32) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::ffi::CString;
        use std::os::unix::ffi::OsStrExt;

        unsafe extern "C" {
            fn lchown(path: *const std::os::raw::c_char, owner: u32, group: u32) -> i32;
        }

        fn visit(path: &Path, uid: u32, gid: u32) -> Result<(), String> {
            let metadata = fs::symlink_metadata(path)
                .map_err(|error| format_path_error("read fixture ownership", path, error))?;
            if metadata.is_dir() {
                let mut children = fs::read_dir(path)
                    .map_err(|error| {
                        format_path_error("read fixture ownership directory", path, error)
                    })?
                    .map(|entry| {
                        entry.map(|entry| entry.path()).map_err(|error| {
                            format_path_error("read fixture ownership entry", path, error)
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                children.sort();
                for child in children {
                    visit(&child, uid, gid)?;
                }
            }
            let display = path.display().to_string();
            let raw = CString::new(path.as_os_str().as_bytes()).map_err(|_| {
                format!("fixture ownership path contains an unsupported NUL byte: `{display}`")
            })?;
            if unsafe { lchown(raw.as_ptr(), uid, gid) } != 0 {
                return Err(format!(
                    "failed to set fixture ownership `{display}` to {uid}:{gid}: {}",
                    io::Error::last_os_error()
                ));
            }
            Ok(())
        }

        visit(root, uid, gid)
    }
    #[cfg(not(unix))]
    {
        let _ = (root, uid, gid);
        Err("numeric fixture ownership requires Unix".to_string())
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::{
        apply_fixture_modes, materialize_fixture, prepare_read_only_iteration_dirs,
        restore_path_times, stage_iteration_dirs, times_from_metadata, validate_fixture,
        READ_ONLY_RECENT_WINDOW_SECONDS,
    };
    use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, FsTimes, HardlinkSpec, SymlinkSpec};
    use std::collections::BTreeSet;
    use std::fs;
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    use std::path::{Path, PathBuf};
    use std::time::{SystemTime, UNIX_EPOCH};

    // Replay fixture validation rejects traversal before an external sentinel can be overwritten.
    #[test]
    fn materialize_fixture_rejects_escape_before_writing() {
        let sandbox = tempfile::tempdir().unwrap();
        let fixture_root = sandbox.path().join("fixture");
        fs::create_dir(&fixture_root).unwrap();
        let sentinel = sandbox.path().join("outside");
        fs::write(&sentinel, b"unchanged").unwrap();
        let fixture = FixtureBlueprint {
            directories: Vec::new(),
            files: vec![FileSpec {
                relative_path: PathBuf::from("../outside"),
                bytes: b"overwritten".to_vec(),
                mode: 0o644,
            }],
            symlinks: Vec::new(),
            hardlinks: Vec::new(),
        };

        let error = materialize_fixture(&fixture_root, &fixture).unwrap_err();

        assert!(error.contains("invalid fixture file path"));
        assert_eq!(fs::read(&sentinel).unwrap(), b"unchanged");
    }

    // A replay symlink target cannot lexically escape the isolated fixture root.
    #[test]
    fn fixture_validation_rejects_escaping_symlink_target() {
        let fixture = FixtureBlueprint {
            directories: Vec::new(),
            files: Vec::new(),
            symlinks: vec![SymlinkSpec {
                relative_path: PathBuf::from("escape"),
                target: PathBuf::from("../outside"),
            }],
            hardlinks: Vec::new(),
        };

        let error = validate_fixture(&fixture).unwrap_err();

        assert!(error.contains("symlink target escapes fixture root"));
    }

    // Parent traversal within a nested fixture remains a valid relative symlink target.
    #[test]
    fn fixture_validation_allows_internal_parent_symlink_target() {
        let fixture = FixtureBlueprint {
            directories: vec![DirSpec {
                relative_path: PathBuf::from("dir"),
                mode: 0o755,
            }],
            files: vec![FileSpec {
                relative_path: PathBuf::from("inside"),
                bytes: Vec::new(),
                mode: 0o644,
            }],
            symlinks: vec![SymlinkSpec {
                relative_path: PathBuf::from("dir/link"),
                target: PathBuf::from("../inside"),
            }],
            hardlinks: Vec::new(),
        };

        validate_fixture(&fixture).unwrap();
    }

    // Searchable staging must defer the fixture's exact directory mode until explicit finalization.
    #[test]
    fn staged_iteration_dirs_are_searchable_until_exact_mode_finalization() {
        let root = tempfile::tempdir().unwrap();
        let fixture = FixtureBlueprint {
            directories: vec![DirSpec {
                relative_path: PathBuf::from("d"),
                mode: 0o000,
            }],
            files: Vec::new(),
            symlinks: Vec::new(),
            hardlinks: Vec::new(),
        };
        let (reference, dut) = stage_iteration_dirs(root.path(), None, 0, &fixture, false).unwrap();

        for role_root in [&reference, &dut] {
            assert_eq!(
                fs::symlink_metadata(role_root.join("d"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o700,
                0o700
            );
            apply_fixture_modes(role_root, &fixture).unwrap();
            assert_eq!(
                fs::symlink_metadata(role_root.join("d"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o7777,
                0o000
            );
        }
    }

    // A prepared read-only fixture must preserve regular-file and directory atimes during traversal.
    #[cfg(target_os = "linux")]
    #[test]
    fn prepared_read_only_iteration_dirs_preserve_regular_node_atimes() {
        let root = tempfile::tempdir().unwrap();
        let fixture = FixtureBlueprint {
            directories: vec![
                DirSpec {
                    relative_path: PathBuf::from("listed"),
                    mode: 0o700,
                },
                DirSpec {
                    relative_path: PathBuf::from("denied"),
                    mode: 0o000,
                },
            ],
            files: vec![
                FileSpec {
                    relative_path: PathBuf::from("listed/entry"),
                    bytes: b"entry".to_vec(),
                    mode: 0o600,
                },
                FileSpec {
                    relative_path: PathBuf::from("unreadable"),
                    bytes: b"unreadable".to_vec(),
                    mode: 0o000,
                },
            ],
            symlinks: Vec::new(),
            hardlinks: Vec::new(),
        };
        let (reference, dut) =
            prepare_read_only_iteration_dirs(root.path(), None, 1, &fixture).unwrap();

        for role_root in [&reference, &dut] {
            assert_eq!(
                fs::symlink_metadata(role_root.join("denied"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o7777,
                0o000
            );
            assert_eq!(
                fs::symlink_metadata(role_root.join("unreadable"))
                    .unwrap()
                    .permissions()
                    .mode()
                    & 0o7777,
                0o000
            );

            let listed = role_root.join("listed");
            let entry = listed.join("entry");
            let controlled_atime = (1_600_000_000, 123);
            let mut before = Vec::new();
            for path in [&listed, &entry] {
                let original = times_from_metadata(&fs::symlink_metadata(path).unwrap());
                restore_path_times(
                    path,
                    FsTimes {
                        atime_sec: controlled_atime.0,
                        atime_nsec: controlled_atime.1,
                        mtime_sec: original.mtime_sec,
                        mtime_nsec: original.mtime_nsec,
                        ctime_sec: original.ctime_sec,
                        ctime_nsec: original.ctime_nsec,
                    },
                    false,
                )
                .unwrap();
                before.push(times_from_metadata(&fs::symlink_metadata(path).unwrap()));
            }

            assert_eq!(fs::read_dir(&listed).unwrap().count(), 1);
            assert_eq!(fs::read(&entry).unwrap(), b"entry");

            for (path, before) in [listed, entry].iter().zip(before) {
                let after = times_from_metadata(&fs::symlink_metadata(path).unwrap());
                assert_eq!(
                    (after.atime_sec, after.atime_nsec),
                    (before.atime_sec, before.atime_nsec)
                );
            }
        }
    }

    // A realistic metadata fixture must give both clones varied times without splitting hard-link aliases.
    #[cfg(target_os = "linux")]
    #[test]
    fn prepared_read_only_iteration_dirs_assign_inode_time_profiles() {
        let root = tempfile::tempdir().unwrap();
        let fixture = FixtureBlueprint {
            directories: vec![DirSpec {
                relative_path: PathBuf::from("listed"),
                mode: 0o700,
            }],
            files: vec![
                FileSpec {
                    relative_path: PathBuf::from("listed/primary"),
                    bytes: b"primary".to_vec(),
                    mode: 0o600,
                },
                FileSpec {
                    relative_path: PathBuf::from("listed/second"),
                    bytes: b"second".to_vec(),
                    mode: 0o600,
                },
            ],
            symlinks: vec![SymlinkSpec {
                relative_path: PathBuf::from("entry-link"),
                target: PathBuf::from("listed/primary"),
            }],
            hardlinks: vec![HardlinkSpec {
                relative_path: PathBuf::from("listed/primary-hard"),
                source_relative_path: PathBuf::from("listed/primary"),
            }],
        };
        let (reference, dut) =
            prepare_read_only_iteration_dirs(root.path(), None, 2, &fixture).unwrap();

        let mut atimes = BTreeSet::new();
        let mut mtimes = BTreeSet::new();
        for relative in [
            ".",
            "entry-link",
            "listed",
            "listed/primary",
            "listed/primary-hard",
            "listed/second",
        ] {
            let reference_times =
                times_from_metadata(&fs::symlink_metadata(reference.join(relative)).unwrap());
            let dut_times = times_from_metadata(&fs::symlink_metadata(dut.join(relative)).unwrap());
            assert_eq!(
                (
                    reference_times.atime_sec,
                    reference_times.atime_nsec,
                    reference_times.mtime_sec,
                    reference_times.mtime_nsec,
                ),
                (
                    dut_times.atime_sec,
                    dut_times.atime_nsec,
                    dut_times.mtime_sec,
                    dut_times.mtime_nsec,
                ),
                "{relative}"
            );
            atimes.insert((reference_times.atime_sec, reference_times.atime_nsec));
            mtimes.insert((reference_times.mtime_sec, reference_times.mtime_nsec));
        }

        assert!(atimes.len() >= 3);
        assert!(mtimes.len() >= 3);
        assert!(atimes.iter().any(|(_, nanoseconds)| *nanoseconds != 0));
        assert!(mtimes.iter().any(|(_, nanoseconds)| *nanoseconds != 0));

        let now = i64::try_from(
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        )
        .unwrap();
        for observed in [&atimes, &mtimes] {
            assert!(observed.iter().any(|(seconds, _)| {
                now - READ_ONLY_RECENT_WINDOW_SECONDS < *seconds && *seconds <= now
            }));
            assert!(observed
                .iter()
                .any(|(seconds, _)| *seconds <= now - READ_ONLY_RECENT_WINDOW_SECONDS));
            assert!(observed.iter().any(|(seconds, _)| *seconds > now));
        }

        for role_root in [&reference, &dut] {
            let source = fs::symlink_metadata(role_root.join(Path::new("listed/primary"))).unwrap();
            let alias =
                fs::symlink_metadata(role_root.join(Path::new("listed/primary-hard"))).unwrap();
            assert_eq!((source.dev(), source.ino()), (alias.dev(), alias.ino()));
            assert_eq!(times_from_metadata(&source), times_from_metadata(&alias));
        }
    }
}

fn apply_entry_mode(path: &Path, mode: u32, kind: &str) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        fs::set_permissions(path, fs::Permissions::from_mode(mode)).map_err(|e| {
            format!(
                "failed to set fixture {kind} mode {:04o} on `{}`: {e}",
                mode,
                path.display()
            )
        })?;
    }
    #[cfg(not(unix))]
    {
        let _ = (path, mode, kind);
    }
    Ok(())
}

fn create_fixture_symlink(target: &Path, path: &Path) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;

        symlink(target, path).map_err(|e| {
            format!(
                "failed to create fixture symlink `{}` -> `{}`: {e}",
                path.display(),
                target.display()
            )
        })?;
    }
    #[cfg(not(unix))]
    {
        let _ = (target, path);
    }
    Ok(())
}

fn remove_dir_forcefully(path: &Path) -> Result<(), String> {
    match fs::remove_dir_all(path) {
        Ok(()) => Ok(()),
        Err(first_err) => {
            #[cfg(unix)]
            {
                if first_err.kind() == io::ErrorKind::PermissionDenied {
                    make_tree_owner_writable(path).map_err(|e| {
                        format!(
                            "failed to make directory writable `{}` after permission error: {e}",
                            path.display()
                        )
                    })?;
                    fs::remove_dir_all(path).map_err(|e| {
                        format!(
                            "failed to clear directory `{}` after permission recovery: {e}",
                            path.display()
                        )
                    })?;
                    return Ok(());
                }
            }
            Err(format!(
                "failed to clear directory `{}`: {first_err}",
                path.display()
            ))
        }
    }
}

#[cfg(unix)]
fn make_tree_owner_writable(path: &Path) -> io::Result<()> {
    use std::os::unix::fs::PermissionsExt;

    if !path.exists() {
        return Ok(());
    }

    fn visit(path: &Path) -> io::Result<()> {
        let meta = fs::symlink_metadata(path)?;
        if meta.file_type().is_symlink() {
            return Ok(());
        }

        if meta.is_dir() {
            let mut perms = meta.permissions();
            perms.set_mode(0o700);
            fs::set_permissions(path, perms)?;
            for entry in fs::read_dir(path)? {
                let entry = entry?;
                visit(&entry.path())?;
            }
        } else {
            let mut perms = meta.permissions();
            perms.set_mode(0o600);
            fs::set_permissions(path, perms)?;
        }
        Ok(())
    }

    visit(path)
}
