use super::input::{generate_argv, mutate_argv};
use super::{
    DirSpec, FileSpec, FixtureBlueprint, GeneratedCase, HardlinkSpec, SymlinkSpec, UtilityProfile,
};
use crate::utils::arg_semantics::{positional_args, requests_help_or_version};
use rand::rngs::StdRng;
use rand::Rng;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

pub(crate) fn generate_case(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    max_fs_entries: usize,
) -> GeneratedCase {
    let profile = utility_profile(util);
    let mut fixture = generate_fixture_blueprint_for_util(util, rng, max_fs_entries);
    let mut argv = generate_argv(util, &profile, option_pool, rng, max_args, &fixture);
    if util == "ls" && super::input::ls_argv_requires_followed_entry_metadata(&argv) {
        fixture = generate_fixture_blueprint(rng, max_fs_entries, false);
        argv = generate_argv(util, &profile, option_pool, rng, max_args, &fixture);
    }
    let stdin = if rng.random_bool(0.4) {
        random_file_contents(rng)
    } else {
        Vec::new()
    };
    let cwd = if matches!(
        util,
        "cat"
            | "comm"
            | "csplit"
            | "cut"
            | "expand"
            | "head"
            | "ls"
            | "mv"
            | "nl"
            | "paste"
            | "stat"
            | "tac"
            | "tail"
            | "uniq"
            | "wc"
    ) {
        PathBuf::from(".")
    } else {
        fixture.random_cwd(rng)
    };
    let mut case = GeneratedCase {
        argv,
        fixture,
        stdin,
        cwd,
    };
    keep_within_supported_slice(util, &mut case);
    case
}

pub(crate) fn mutate_case_from_corpus(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    max_fs_entries: usize,
    base: &GeneratedCase,
) -> GeneratedCase {
    let mut case = base.clone();
    match rng.random_range(0..5) {
        0 if util == "ls" => {
            return generate_case(util, option_pool, rng, max_args, max_fs_entries)
        }
        0 => mutate_argv(
            util,
            option_pool,
            rng,
            max_args,
            &case.fixture,
            &mut case.argv,
        ),
        1 => mutate_stdin(rng, &mut case.stdin),
        2 => mutate_fixture_contents(rng, &mut case.fixture),
        3 => {
            case.cwd = if matches!(
                util,
                "comm"
                    | "csplit"
                    | "cut"
                    | "expand"
                    | "head"
                    | "ls"
                    | "mv"
                    | "nl"
                    | "paste"
                    | "stat"
                    | "tac"
                    | "tail"
                    | "uniq"
            ) {
                PathBuf::from(".")
            } else {
                case.fixture.random_cwd(rng)
            }
        }
        _ => return generate_case(util, option_pool, rng, max_args, max_fs_entries),
    }
    keep_within_supported_slice(util, &mut case);
    if util == "uniq" && !uniq_argv_is_supported(&case.argv) {
        return generate_case(util, option_pool, rng, max_args, max_fs_entries);
    }
    case
}

fn mutate_stdin(rng: &mut StdRng, stdin: &mut Vec<u8>) {
    if stdin.is_empty() || rng.random_bool(0.4) {
        *stdin = random_file_contents(rng);
    } else {
        stdin.truncate(stdin.len() / 2);
    }
}

fn mutate_fixture_contents(rng: &mut StdRng, fixture: &mut FixtureBlueprint) {
    if fixture.files.is_empty() {
        return;
    }
    let idx = rng.random_range(0..fixture.files.len());
    fixture.files[idx].bytes = random_file_contents(rng);
}

fn keep_within_supported_slice(util: &str, case: &mut GeneratedCase) {
    if util == "comm" {
        case.fixture = generate_comm_fixture_blueprint();
        if comm_consumes_stdin(&case.argv) {
            case.stdin = if comm_uses_zero_terminated_records(&case.argv) {
                b"apple\0banana\0banana\0orange\0".to_vec()
            } else {
                b"apple\nbanana\nbanana\norange\n".to_vec()
            };
        }
    }
    if util == "csplit" {
        case.fixture = generate_csplit_fixture_blueprint();
    }
    if util == "csplit" && case.argv.first().is_some_and(|arg| arg == "-") && case.stdin.is_empty()
    {
        case.stdin = b"alpha\nbeta\ngamma\n".to_vec();
    }
    if util == "fold" {
        case.cwd = PathBuf::from(".");
        if !case.stdin.is_empty() {
            case.stdin =
                b"alpha beta gamma delta epsilon zeta eta theta iota kappa lambda mu\n".to_vec();
        }
    }
    if util == "printenv" {
        keep_printenv_on_explicit_variables(&mut case.argv);
    }
    if util == "expand" {
        case.cwd = PathBuf::from(".");
        if case.stdin.is_empty() {
            case.stdin = b"\tstdin\tfield\n aaa\x08\x08b\tc\n".to_vec();
        }
    }
    if matches!(util, "ls" | "stat") {
        case.cwd = PathBuf::from(".");
    }
}

fn uniq_argv_is_supported(argv: &[String]) -> bool {
    if requests_help_or_version("uniq", argv) {
        return true;
    }
    let operands = positional_args("uniq", argv);
    !operands.iter().any(|operand| {
        operand
            .strip_prefix('+')
            .is_some_and(|digits| !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
    }) && (operands.len() != 2 || operands[1] == "-")
}

fn keep_printenv_on_explicit_variables(argv: &mut Vec<String>) {
    if printenv_has_explicit_variable(argv)
        || argv
            .iter()
            .any(|arg| matches!(arg.as_str(), "--help" | "--version"))
    {
        return;
    }
    argv.push("LC_ALL".to_string());
    argv.push("LANG".to_string());
}

fn printenv_has_explicit_variable(argv: &[String]) -> bool {
    let mut after_options = false;
    for arg in argv {
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

pub(super) fn utility_profile(util: &str) -> UtilityProfile {
    match util {
        "comm" | "csplit" | "du" | "ln" | "touch" | "chmod" | "readlink" | "chown" | "chgrp"
        | "mkdir" | "rmdir" | "rm" | "mv" | "cp" | "install" => UtilityProfile {
            requires_path_operand: true,
            prefers_existing_paths: true,
        },
        "ls" => UtilityProfile {
            requires_path_operand: false,
            prefers_existing_paths: true,
        },
        "stat" => UtilityProfile {
            requires_path_operand: true,
            prefers_existing_paths: true,
        },
        _ => UtilityProfile {
            requires_path_operand: false,
            prefers_existing_paths: false,
        },
    }
}

fn generate_fixture_blueprint_for_util(
    util: &str,
    rng: &mut StdRng,
    max_fs_entries: usize,
) -> FixtureBlueprint {
    match util {
        "comm" => generate_comm_fixture_blueprint(),
        "csplit" => generate_csplit_fixture_blueprint(),
        "cut" => generate_cut_fixture_blueprint(),
        "fold" | "head" | "nl" | "paste" | "tac" | "tail" | "uniq" => {
            generate_line_fixture_blueprint()
        }
        "expand" => generate_expand_fixture_blueprint(),
        "chmod" => generate_chmod_fixture_blueprint(rng, max_fs_entries),
        _ => generate_fixture_blueprint(rng, max_fs_entries, true),
    }
}

fn generate_chmod_fixture_blueprint(rng: &mut StdRng, max_fs_entries: usize) -> FixtureBlueprint {
    let budget = max_fs_entries.max(1);
    let mut fixture = generate_fixture_blueprint(rng, budget, true);
    fixture.symlinks.clear();
    fixture.hardlinks.clear();
    match rng.random_range(0..4) {
        0 if budget >= 2 => {
            if fixture.files.is_empty() {
                fixture.directories.truncate(budget.saturating_sub(2));
                fixture.files.push(FileSpec {
                    relative_path: PathBuf::from("chmod-target"),
                    bytes: Vec::new(),
                    mode: random_file_mode(rng),
                });
            }
            trim_fixture_for_links(&mut fixture, budget, 1, true, false);
            fixture.symlinks.push(SymlinkSpec {
                relative_path: PathBuf::from("chmod-file-link"),
                target: fixture.files[0].relative_path.clone(),
            });
        }
        1 if budget >= 2 => {
            trim_fixture_for_links(&mut fixture, budget, 1, false, true);
            fixture.symlinks.push(SymlinkSpec {
                relative_path: PathBuf::from("chmod-dir-link"),
                target: fixture.directories[0].relative_path.clone(),
            });
        }
        2 if budget >= 1 => {
            trim_fixture_for_links(&mut fixture, budget, 1, false, false);
            fixture.symlinks.push(SymlinkSpec {
                relative_path: PathBuf::from("chmod-dangling-link"),
                target: PathBuf::from("chmod-missing-target"),
            });
        }
        _ if budget >= 2 => {
            trim_fixture_for_links(&mut fixture, budget, 2, false, false);
            fixture.symlinks.extend([
                SymlinkSpec {
                    relative_path: PathBuf::from("chmod-cycle-a"),
                    target: PathBuf::from("chmod-cycle-b"),
                },
                SymlinkSpec {
                    relative_path: PathBuf::from("chmod-cycle-b"),
                    target: PathBuf::from("chmod-cycle-a"),
                },
            ]);
        }
        _ => {}
    }
    fixture
}

fn trim_fixture_for_links(
    fixture: &mut FixtureBlueprint,
    budget: usize,
    link_count: usize,
    keep_file: bool,
    keep_directory: bool,
) {
    while fixture.directories.len() + fixture.files.len() + link_count > budget {
        if fixture.files.len() > usize::from(keep_file) {
            fixture.files.pop();
        } else if fixture.directories.len() > usize::from(keep_directory) {
            fixture.directories.pop();
        } else {
            break;
        }
    }
}

fn generate_comm_fixture_blueprint() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("left.txt"),
                bytes: b"apple\nbanana\nbanana\norange\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("right.txt"),
                bytes: b"banana\ncarrot\norange\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("left0.txt"),
                bytes: b"apple\0banana\0banana\0orange\0".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("right0.txt"),
                bytes: b"banana\0carrot\0orange\0".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}

fn comm_consumes_stdin(argv: &[String]) -> bool {
    argv.iter().filter(|arg| arg.as_str() == "-").count() == 1
}

fn comm_uses_zero_terminated_records(argv: &[String]) -> bool {
    argv.iter()
        .any(|arg| arg == "-z" || arg == "--zero-terminated" || arg.starts_with("-z"))
}

fn generate_csplit_fixture_blueprint() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("split.txt"),
                bytes: b"red\nblue\ngreen\nyellow\npurple\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha\nbeta\ngamma\ndelta\n".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}

fn generate_expand_fixture_blueprint() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"a\tb\n \tlead\tlater\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("b.txt"),
                bytes: b"aaa\x08\x08\x08c\td\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("empty.txt"),
                bytes: Vec::new(),
                mode: 0o644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}

fn generate_cut_fixture_blueprint() -> FixtureBlueprint {
    let mut fixture = generate_line_fixture_blueprint();
    fixture.files.push(FileSpec {
        relative_path: PathBuf::from("nul.txt"),
        bytes: b"ab\0cd\0tail".to_vec(),
        mode: 0o644,
    });
    fixture
}

fn generate_line_fixture_blueprint() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("a.txt"),
                bytes: b"alpha\nbeta\ngamma\ndelta\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("b.txt"),
                bytes: b"one\n\nthree\nfour\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("split.txt"),
                bytes: b"red\nblue\ngreen\nyellow\npurple\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("dups.txt"),
                bytes: b"a\na\nb\nc\nc\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("case.txt"),
                bytes: b"A\na\nB\nb\n".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("empty.txt"),
                bytes: Vec::new(),
                mode: 0o644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}

fn generate_fixture_blueprint(
    rng: &mut StdRng,
    max_fs_entries: usize,
    allow_dangling_symlinks: bool,
) -> FixtureBlueprint {
    let total_entries = max_fs_entries.max(1);
    let mut directory_paths = BTreeSet::new();
    let target_dir_count = rng.random_range(1..=usize::min(4, total_entries));
    while directory_paths.len() < target_dir_count {
        directory_paths.insert(random_relative_dir(rng));
    }

    let directory_pool: Vec<PathBuf> = directory_paths.iter().cloned().collect();
    let mut files = Vec::new();
    let mut occupied_paths = directory_paths.clone();
    let remaining_after_dirs = total_entries.saturating_sub(directory_paths.len());
    let target_file_count = if remaining_after_dirs == 0 {
        0
    } else {
        rng.random_range(1..=remaining_after_dirs)
    };
    while files.len() < target_file_count {
        let mut relative_path = PathBuf::new();
        if !directory_pool.is_empty() && rng.random_bool(0.8) {
            let idx = rng.random_range(0..directory_pool.len());
            relative_path.push(&directory_pool[idx]);
        }
        relative_path.push(random_file_name(rng));
        if occupied_paths.insert(relative_path.clone()) {
            files.push(FileSpec {
                relative_path,
                bytes: random_file_contents(rng),
                mode: random_file_mode(rng),
            });
        }
    }

    let existing_targets: Vec<PathBuf> = directory_paths
        .iter()
        .cloned()
        .chain(files.iter().map(|f| f.relative_path.clone()))
        .collect();

    let remaining_after_files = total_entries.saturating_sub(directory_paths.len() + files.len());
    let symlink_budget = usize::min(2, remaining_after_files);
    let symlinks = generate_symlink_specs(
        rng,
        &directory_pool,
        &existing_targets,
        &mut occupied_paths,
        symlink_budget,
        allow_dangling_symlinks,
    );
    let mut hardlink_rng = rng.clone();
    let hardlinks = if total_entries > directory_paths.len() + files.len() + symlinks.len()
        && !files.is_empty()
        && hardlink_rng.random_bool(0.3)
    {
        let source_relative_path = if !symlinks.is_empty() && hardlink_rng.random_bool(0.2) {
            symlinks[hardlink_rng.random_range(0..symlinks.len())]
                .relative_path
                .clone()
        } else {
            files[hardlink_rng.random_range(0..files.len())]
                .relative_path
                .clone()
        };
        let relative_path = loop {
            let mut path = PathBuf::new();
            if !directory_pool.is_empty() && hardlink_rng.random_bool(0.8) {
                path.push(&directory_pool[hardlink_rng.random_range(0..directory_pool.len())]);
            }
            path.push(random_file_name(&mut hardlink_rng));
            if occupied_paths.insert(path.clone()) {
                break path;
            }
        };
        vec![HardlinkSpec {
            relative_path,
            source_relative_path,
        }]
    } else {
        Vec::new()
    };

    let directories = directory_paths
        .into_iter()
        .map(|relative_path| DirSpec {
            relative_path,
            mode: random_directory_mode(rng),
        })
        .collect();

    FixtureBlueprint {
        directories,
        files,
        symlinks,
        hardlinks,
    }
}

impl FixtureBlueprint {
    pub(super) fn existing_operands(&self) -> Vec<String> {
        let mut paths = BTreeSet::new();
        paths.insert(".".to_string());
        for dir in &self.directories {
            paths.insert(dir.relative_path.display().to_string());
        }
        for file in &self.files {
            paths.insert(file.relative_path.display().to_string());
            if let Some(parent) = file.relative_path.parent() {
                if !parent.as_os_str().is_empty() {
                    paths.insert(parent.display().to_string());
                }
            }
        }
        for symlink in &self.symlinks {
            paths.insert(symlink.relative_path.display().to_string());
            if let Some(parent) = symlink.relative_path.parent() {
                if !parent.as_os_str().is_empty() {
                    paths.insert(parent.display().to_string());
                }
            }
        }
        for hardlink in &self.hardlinks {
            paths.insert(hardlink.relative_path.display().to_string());
            if let Some(parent) = hardlink.relative_path.parent() {
                if !parent.as_os_str().is_empty() {
                    paths.insert(parent.display().to_string());
                }
            }
            paths.insert(hardlink.source_relative_path.display().to_string());
        }
        paths.into_iter().collect()
    }

    pub(super) fn random_cwd(&self, rng: &mut StdRng) -> PathBuf {
        if self.directories.is_empty() || !rng.random_bool(0.5) {
            return PathBuf::from(".");
        }
        let idx = rng.random_range(0..self.directories.len());
        self.directories[idx].relative_path.clone()
    }
}

pub(super) fn generate_missing_operands(rng: &mut StdRng) -> Vec<String> {
    let mut missing = BTreeSet::new();
    let target_count = rng.random_range(2..=6);
    while missing.len() < target_count {
        missing.insert(random_missing_operand(rng));
    }
    missing.into_iter().collect()
}

fn random_missing_operand(rng: &mut StdRng) -> String {
    match rng.random_range(0..5) {
        0 => format!(
            "{}{}",
            random_name_component(rng, 5, 12),
            rng.random_range(100..10000)
        ),
        1 => format!(
            "{}/{}",
            random_name_component(rng, 4, 10),
            random_file_name(rng)
        ),
        2 => format!(
            "{}/{}",
            random_name_component(rng, 4, 10),
            random_name_component(rng, 4, 10)
        ),
        3 => format!(".{}", random_name_component(rng, 3, 8)),
        _ => format!(
            "{}-{}",
            random_name_component(rng, 4, 10),
            rng.random_range(100..10000)
        ),
    }
}

fn generate_symlink_specs(
    rng: &mut StdRng,
    directory_pool: &[PathBuf],
    existing_targets: &[PathBuf],
    occupied_paths: &mut BTreeSet<PathBuf>,
    symlink_budget: usize,
    allow_dangling_symlinks: bool,
) -> Vec<SymlinkSpec> {
    #[cfg(unix)]
    {
        let target_count = if symlink_budget == 0 {
            0
        } else {
            rng.random_range(0..=symlink_budget)
        };
        let mut symlinks = Vec::new();
        let mut attempts = 0usize;
        while symlinks.len() < target_count && attempts < target_count * 40 + 20 {
            attempts += 1;
            let mut relative_path = PathBuf::new();
            if !directory_pool.is_empty() && rng.random_bool(0.7) {
                let idx = rng.random_range(0..directory_pool.len());
                relative_path.push(&directory_pool[idx]);
            }
            relative_path.push(random_symlink_name(rng));

            if !occupied_paths.insert(relative_path.clone()) {
                continue;
            }

            let parent = relative_path.parent().unwrap_or_else(|| Path::new(""));
            let target =
                random_symlink_target(rng, parent, existing_targets, allow_dangling_symlinks);
            symlinks.push(SymlinkSpec {
                relative_path,
                target,
            });
        }
        symlinks
    }
    #[cfg(not(unix))]
    {
        let _ = (
            rng,
            directory_pool,
            existing_targets,
            occupied_paths,
            symlink_budget,
            allow_dangling_symlinks,
        );
        Vec::new()
    }
}

fn random_symlink_target(
    rng: &mut StdRng,
    parent: &Path,
    existing_targets: &[PathBuf],
    allow_dangling_symlinks: bool,
) -> PathBuf {
    if !existing_targets.is_empty() && (!allow_dangling_symlinks || rng.random_bool(0.75)) {
        let idx = rng.random_range(0..existing_targets.len());
        let target = &existing_targets[idx];
        if !allow_dangling_symlinks || rng.random_bool(0.7) {
            relative_path_from(parent, target)
        } else {
            target.clone()
        }
    } else {
        random_dangling_target(rng)
    }
}

fn relative_path_from(base: &Path, target: &Path) -> PathBuf {
    let base_components: Vec<_> = base.components().collect();
    let target_components: Vec<_> = target.components().collect();
    let mut shared = 0usize;
    while shared < base_components.len()
        && shared < target_components.len()
        && base_components[shared] == target_components[shared]
    {
        shared += 1;
    }

    let mut relative = PathBuf::new();
    for _ in shared..base_components.len() {
        relative.push("..");
    }
    for component in target_components.iter().skip(shared) {
        relative.push(component.as_os_str());
    }

    if relative.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        relative
    }
}

fn random_dangling_target(rng: &mut StdRng) -> PathBuf {
    match rng.random_range(0..4) {
        0 => PathBuf::from(format!("missing-{}", rng.random_range(100..10000))),
        1 => {
            let mut path = PathBuf::from("missing");
            path.push(random_name_component(rng, 4, 10));
            path.push(random_file_name(rng));
            path
        }
        2 => PathBuf::from(format!(
            "ghost-{}.{}",
            random_name_component(rng, 3, 8),
            random_name_component(rng, 2, 4)
        )),
        _ => {
            let mut path = PathBuf::new();
            path.push(random_name_component(rng, 4, 10));
            path.push(random_name_component(rng, 4, 10));
            path
        }
    }
}

fn random_relative_dir(rng: &mut StdRng) -> PathBuf {
    let depth = rng.random_range(1..=3);
    let mut path = PathBuf::new();
    for _ in 0..depth {
        path.push(random_name_component(rng, 3, 10));
    }
    path
}

fn random_file_name(rng: &mut StdRng) -> String {
    let ext_pool = ["txt", "bin", "dat", "log", "cfg", "tmp", "md"];
    let stem = random_name_component(rng, 3, 12);
    let ext = ext_pool[rng.random_range(0..ext_pool.len())];
    match rng.random_range(0..6) {
        0 => format!("{stem}.{ext}"),
        1 => format!(".{stem}.{ext}"),
        2 => format!("{stem}-{}", rng.random_range(0..1000)),
        3 => format!("{stem}_{:02}.{ext}", rng.random_range(0..100)),
        4 => format!("{}.{}", random_name_component(rng, 1, 4), ext),
        _ => stem,
    }
}

fn random_symlink_name(rng: &mut StdRng) -> String {
    match rng.random_range(0..4) {
        0 => format!("{}-link", random_name_component(rng, 3, 10)),
        1 => format!("ln-{}", random_name_component(rng, 3, 10)),
        2 => format!("{}.lnk", random_name_component(rng, 3, 10)),
        _ => format!(".{}-sym", random_name_component(rng, 3, 8)),
    }
}

fn random_file_mode(rng: &mut StdRng) -> u32 {
    const MODES: &[u32] = &[
        0o400, 0o444, 0o600, 0o640, 0o644, 0o666, 0o700, 0o744, 0o755, 0o777, 0o4755, 0o2755,
        0o1755,
    ];
    MODES[rng.random_range(0..MODES.len())]
}

fn random_directory_mode(rng: &mut StdRng) -> u32 {
    const MODES: &[u32] = &[
        0o700, 0o711, 0o750, 0o755, 0o770, 0o775, 0o777, 0o1777, 0o2755,
    ];
    MODES[rng.random_range(0..MODES.len())]
}

fn random_file_contents(rng: &mut StdRng) -> Vec<u8> {
    match rng.random_range(0..9) {
        0 => Vec::new(),
        1 => random_bytes(rng, 1, 64),
        2 => random_bytes(rng, 65, 2048),
        3 => random_bytes(rng, 4097, 16384),
        4 => random_printable_text_bytes(rng),
        5 => random_line_text_bytes(rng),
        6 => random_repeated_pattern_bytes(rng),
        7 => random_zero_heavy_bytes(rng),
        _ => random_incrementing_bytes(rng),
    }
}

fn random_printable_text_bytes(rng: &mut StdRng) -> Vec<u8> {
    let alphabet =
        b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789 .,;:_-+/()[]{}!?";
    let len = rng.random_range(8..=512);
    (0..len)
        .map(|_| {
            let idx = rng.random_range(0..alphabet.len());
            alphabet[idx]
        })
        .collect()
}

fn random_line_text_bytes(rng: &mut StdRng) -> Vec<u8> {
    let line_count = rng.random_range(1..=24);
    let mut out = Vec::new();
    for line_idx in 0..line_count {
        let repeat_count = rng.random_range(1..=8);
        let tail = "x".repeat(repeat_count);
        let line = format!(
            "{}:{}:{}\n",
            line_idx,
            random_name_component(rng, 3, 10),
            tail
        );
        out.extend_from_slice(line.as_bytes());
    }
    out
}

fn random_repeated_pattern_bytes(rng: &mut StdRng) -> Vec<u8> {
    let pattern = random_bytes(rng, 1, 16);
    let repeat_count = rng.random_range(1..=128);
    let mut out = Vec::with_capacity(pattern.len() * repeat_count);
    for _ in 0..repeat_count {
        out.extend_from_slice(&pattern);
    }
    out
}

fn random_zero_heavy_bytes(rng: &mut StdRng) -> Vec<u8> {
    let len = rng.random_range(1..=1024);
    let mut out = Vec::with_capacity(len);
    for _ in 0..len {
        if rng.random_bool(0.7) {
            out.push(0);
        } else {
            out.push(rng.random::<u8>());
        }
    }
    out
}

fn random_incrementing_bytes(rng: &mut StdRng) -> Vec<u8> {
    let len = rng.random_range(1..=512);
    let start = rng.random::<u8>();
    (0..len)
        .map(|idx| start.wrapping_add((idx % 251) as u8))
        .collect()
}

// Bytes on which the utilities' shell-quoting specifications actually branch.
// `/` and NUL are excluded so every generated name stays a legal POSIX filename,
// and everything here is valid UTF-8 so the JSON repro bundles keep working.
const QUOTE_TRIGGER_CHARS: &[char] = &[
    '\'', ' ', '#', '~', '{', '}', '$', '!', '"', '&', '(', ')', '*', ';', '<', '=', '>', '[', ']',
    '^', '`', '|', '?', '\\', ':', '\t', 'é',
];

/// One in this many name components is generated with quote triggers, so the
/// existing plain-name coverage is preserved while the quoting paths are reached.
const QUOTE_TRIGGER_ONE_IN: u32 = 4;

pub(super) fn contains_quote_trigger(text: &str) -> bool {
    text.chars().any(|ch| QUOTE_TRIGGER_CHARS.contains(&ch))
}

/// A name component carrying at least one shell-quote trigger, mixed with
/// ordinary characters so operands stay realistic rather than degenerate.
fn random_quote_trigger_component(rng: &mut StdRng, min_len: usize, max_len: usize) -> String {
    let plain = b"abcdefghijklmnopqrstuvwxyz0123456789";
    let len = if max_len <= min_len {
        min_len.max(1)
    } else {
        rng.random_range(min_len.max(1)..=max_len)
    };
    let trigger_at = rng.random_range(0..len);
    let mut out = String::with_capacity(len + 1);
    for position in 0..len {
        if position == trigger_at {
            let idx = rng.random_range(0..QUOTE_TRIGGER_CHARS.len());
            out.push(QUOTE_TRIGGER_CHARS[idx]);
        } else {
            let idx = rng.random_range(0..plain.len());
            out.push(char::from(plain[idx]));
        }
    }
    out
}

fn random_name_component(rng: &mut StdRng, min_len: usize, max_len: usize) -> String {
    if max_len > 0 && rng.random_range(0..QUOTE_TRIGGER_ONE_IN) == 0 {
        return random_quote_trigger_component(rng, min_len, max_len);
    }
    let alphabet = b"abcdefghijklmnopqrstuvwxyz0123456789-_";
    let leading_alphabet = b"abcdefghijklmnopqrstuvwxyz0123456789_";
    let len = if max_len <= min_len {
        min_len
    } else {
        rng.random_range(min_len..=max_len)
    };
    let mut out = String::with_capacity(len);
    if len == 0 {
        return out;
    }
    let idx = rng.random_range(0..leading_alphabet.len());
    out.push(char::from(leading_alphabet[idx]));
    for _ in 1..len {
        let idx = rng.random_range(0..alphabet.len());
        out.push(char::from(alphabet[idx]));
    }
    out
}

fn random_bytes(rng: &mut StdRng, min_len: usize, max_len: usize) -> Vec<u8> {
    let len = if max_len <= min_len {
        min_len
    } else {
        rng.random_range(min_len..=max_len)
    };
    (0..len).map(|_| rng.random::<u8>()).collect()
}

#[cfg(test)]
mod tests {
    use super::{
        contains_quote_trigger, generate_case, generate_fixture_blueprint_for_util,
        mutate_case_from_corpus, random_file_contents, random_quote_trigger_component,
        uniq_argv_is_supported,
    };
    use crate::fuzz::fixture::stage_iteration_dirs;
    use crate::fuzz::input::ls_argv_requires_followed_entry_metadata;
    use crate::fuzz::input::scenario_case;
    use crate::fuzz::GeneratedCase;
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use std::collections::BTreeSet;
    use std::fs;
    use std::path::PathBuf;

    fn materialized_fixture_has_dangling(
        root: &std::path::Path,
        iteration: usize,
        fixture: &crate::fuzz::FixtureBlueprint,
    ) -> bool {
        let (reference, _) = stage_iteration_dirs(root, None, iteration, fixture, false).unwrap();
        fixture
            .symlinks
            .iter()
            .any(|link| fs::metadata(reference.join(&link.relative_path)).is_err())
    }

    // Uniq support excludes a named output operand after the input operand.
    #[test]
    fn uniq_rejects_named_output_operand() {
        let argv = vec!["input".to_string(), "output".to_string()];

        assert!(!uniq_argv_is_supported(&argv));
    }

    // Uniq support permits standard output as the explicit output operand.
    #[test]
    fn uniq_accepts_standard_output_operand() {
        let argv = vec!["input".to_string(), "-".to_string()];

        assert!(uniq_argv_is_supported(&argv));
    }

    // Uniq support permits a single input operand.
    #[test]
    fn uniq_accepts_input_operand() {
        let argv = vec!["input".to_string()];

        assert!(uniq_argv_is_supported(&argv));
    }

    // Uniq support excludes a traditional skip-character operand.
    #[test]
    fn uniq_rejects_traditional_skip_operand() {
        let argv = vec!["+2000".to_string()];

        assert!(!uniq_argv_is_supported(&argv));
    }

    // Uniq support preserves the explicit extra-operand error path.
    #[test]
    fn uniq_accepts_three_operands() {
        let argv = vec![
            "input".to_string(),
            "output".to_string(),
            "extra".to_string(),
        ];

        assert!(uniq_argv_is_supported(&argv));
    }

    // Uniq help mode takes priority over a named output operand.
    #[test]
    fn uniq_accepts_help_with_named_output() {
        let argv = vec![
            "--help".to_string(),
            "input".to_string(),
            "output".to_string(),
        ];

        assert!(uniq_argv_is_supported(&argv));
    }

    // Uniq treats a help token after the option terminator as a named output operand.
    #[test]
    fn uniq_rejects_help_operand_with_named_output() {
        let argv = vec!["--".to_string(), "--help".to_string(), "input".to_string()];

        assert!(!uniq_argv_is_supported(&argv));
    }

    // Uniq version mode takes priority over a traditional skip operand.
    #[test]
    fn uniq_accepts_version_with_traditional_skip_operand() {
        let argv = vec!["--version".to_string(), "+2000".to_string()];

        assert!(uniq_argv_is_supported(&argv));
    }

    // Corpus mutation replaces a uniq case that gains a named output operand.
    #[test]
    fn uniq_corpus_mutation_stays_within_supported_operands() {
        let base = GeneratedCase {
            argv: vec!["input".to_string()],
            fixture: generate_fixture_blueprint_for_util("uniq", &mut StdRng::seed_from_u64(0), 4),
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };
        let mut rng = StdRng::seed_from_u64(118);
        let case = mutate_case_from_corpus("uniq", &[], &mut rng, 4, 4, &base);

        assert!(uniq_argv_is_supported(&case.argv), "{:?}", case.argv);
    }

    // Corpus mutation replaces every uniq case retaining a traditional skip operand.
    #[test]
    fn uniq_traditional_skip_corpus_mutation_stays_supported() {
        let base = GeneratedCase {
            argv: vec!["+2000".to_string()],
            fixture: generate_fixture_blueprint_for_util("uniq", &mut StdRng::seed_from_u64(0), 4),
            stdin: Vec::new(),
            cwd: PathBuf::from("."),
        };

        for seed in 0..1024 {
            let mut rng = StdRng::seed_from_u64(seed);
            let case = mutate_case_from_corpus("uniq", &[], &mut rng, 4, 4, &base);
            assert!(
                case.argv.iter().all(|arg| arg != "+2000") && uniq_argv_is_supported(&case.argv),
                "seed {seed}: {:?}",
                case.argv
            );
        }
    }

    // Metadata-producing -L cases receive a fixture whose symbolic-link targets all resolve.
    #[test]
    fn ls_followed_metadata_generation_uses_existing_symlink_targets() {
        let root = tempfile::tempdir().unwrap();
        let option_pool = ["-L", "-n", "-s", "-S", "-t", "-R"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let mut observed_followed_metadata = false;
        for seed in 0..256 {
            let mut rng = StdRng::seed_from_u64(seed);
            let case = generate_case("ls", &option_pool, &mut rng, 8, 8);
            if ls_argv_requires_followed_entry_metadata(&case.argv) {
                observed_followed_metadata = true;
                assert!(
                    !materialized_fixture_has_dangling(root.path(), seed as usize, &case.fixture),
                    "seed {seed}: {:?}",
                    case.argv
                );
            }
        }

        assert!(observed_followed_metadata);
    }

    // Name-only random ls generation retains dangling-link coverage outside the excluded slice.
    #[test]
    fn ls_name_only_generation_reaches_dangling_symlinks() {
        let root = tempfile::tempdir().unwrap();
        let reached = (0..256).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let case = generate_case("ls", &[], &mut rng, 8, 8);
            materialized_fixture_has_dangling(root.path(), seed as usize, &case.fixture)
        });

        assert!(reached);
    }

    // Corpus argv mutation never combines a known dangling fixture with metadata-producing -L.
    #[test]
    fn ls_dangling_corpus_mutation_stays_in_supported_slice() {
        let base = scenario_case("ls", 18).expect("name-only dangling ls scenario");
        let option_pool = ["-L", "-n", "-s", "-S", "-t", "-R"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();

        for seed in 0..1024 {
            let mut rng = StdRng::seed_from_u64(seed);
            let case = mutate_case_from_corpus("ls", &option_pool, &mut rng, 8, 8, &base);
            let retains_known_dangling = case.fixture.symlinks.iter().any(|link| {
                link.relative_path == PathBuf::from("dangling-link")
                    && link.target == PathBuf::from("missing-target")
            });
            assert!(
                !retains_known_dangling || !ls_argv_requires_followed_entry_metadata(&case.argv),
                "seed {seed}: {:?}",
                case.argv
            );
        }
    }

    // Random payloads cross a 4 KiB allocation boundary so block counts are not limited to 0 or 8.
    #[test]
    fn random_file_contents_reach_a_second_allocation_extent() {
        let reached = (0..512).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            random_file_contents(&mut rng).len() > 4096
        });

        assert!(reached);
    }

    // Random chmod fixtures reach nested directory trees.
    #[test]
    fn chmod_fixture_generation_reaches_nested_directories() {
        let reached = (0..1024).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            generate_fixture_blueprint_for_util("chmod", &mut rng, 12)
                .directories
                .iter()
                .any(|dir| dir.relative_path.components().count() > 1)
        });

        assert!(reached);
    }

    // Random chmod fixtures reach set-ID and sticky permission bits.
    #[test]
    fn chmod_fixture_generation_reaches_special_mode_bits() {
        let mut bits = 0;
        for seed in 0..1024 {
            let mut rng = StdRng::seed_from_u64(seed);
            let fixture = generate_fixture_blueprint_for_util("chmod", &mut rng, 12);
            bits |= fixture
                .files
                .iter()
                .map(|file| file.mode)
                .chain(fixture.directories.iter().map(|dir| dir.mode))
                .fold(0, |seen, mode| seen | mode);
        }

        assert_eq!(bits & 0o7000, 0o7000);
    }

    // Random chmod fixtures reach symlinks whose target is a regular file.
    #[test]
    fn chmod_fixture_generation_reaches_file_symlink() {
        let reached = (0..1024).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let fixture = generate_fixture_blueprint_for_util("chmod", &mut rng, 12);
            let files: BTreeSet<_> = fixture
                .files
                .iter()
                .map(|file| file.relative_path.as_path())
                .collect();
            fixture
                .symlinks
                .iter()
                .any(|link| files.contains(link.target.as_path()))
        });

        assert!(reached);
    }

    // Random chmod fixtures reach symlinks whose target is a directory.
    #[test]
    fn chmod_fixture_generation_reaches_directory_symlink() {
        let reached = (0..1024).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let fixture = generate_fixture_blueprint_for_util("chmod", &mut rng, 12);
            let directories: BTreeSet<_> = fixture
                .directories
                .iter()
                .map(|dir| dir.relative_path.as_path())
                .collect();
            fixture
                .symlinks
                .iter()
                .any(|link| directories.contains(link.target.as_path()))
        });

        assert!(reached);
    }

    // Random chmod fixtures reach dangling symlink targets.
    #[test]
    fn chmod_fixture_generation_reaches_dangling_symlink() {
        let reached = (0..1024).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let fixture = generate_fixture_blueprint_for_util("chmod", &mut rng, 12);
            let paths: BTreeSet<_> = fixture
                .files
                .iter()
                .map(|file| file.relative_path.as_path())
                .chain(
                    fixture
                        .directories
                        .iter()
                        .map(|dir| dir.relative_path.as_path()),
                )
                .chain(
                    fixture
                        .symlinks
                        .iter()
                        .map(|link| link.relative_path.as_path()),
                )
                .collect();
            fixture
                .symlinks
                .iter()
                .any(|link| !paths.contains(link.target.as_path()))
        });

        assert!(reached);
    }

    // Random chmod fixtures reach an explicit two-link cycle.
    #[test]
    fn chmod_fixture_generation_reaches_symlink_cycle() {
        let reached = (0..1024).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let fixture = generate_fixture_blueprint_for_util("chmod", &mut rng, 12);
            fixture.symlinks.iter().any(|left| {
                fixture.symlinks.iter().any(|right| {
                    left.relative_path == right.target
                        && right.relative_path == left.target
                        && left.relative_path != right.relative_path
                })
            })
        });

        assert!(reached);
    }

    // Generated trigger names stay legal POSIX filenames, or fixture staging breaks.
    #[test]
    fn quote_trigger_components_are_legal_filenames() {
        for seed in 0..256u64 {
            let mut rng = StdRng::seed_from_u64(seed);
            let name = random_quote_trigger_component(&mut rng, 3, 10);
            assert!(!name.is_empty());
            assert!(
                !name.contains('/'),
                "name must not contain a separator: {name:?}"
            );
            assert!(!name.contains('\0'), "name must not contain NUL: {name:?}");
            assert!(
                contains_quote_trigger(&name),
                "name must carry a trigger: {name:?}"
            );
        }
    }

    // The classifier's trigger test distinguishes triggering from plain operands.
    #[test]
    fn quote_trigger_detection_matches_operand_shape() {
        assert!(contains_quote_trigger("a'b"));
        assert!(contains_quote_trigger("next monday"));
        assert!(contains_quote_trigger("a\tb"));
        assert!(!contains_quote_trigger("plain-name_01.txt"));
    }

    // Ordinary generation still reaches plain names, so existing coverage survives.
    #[test]
    fn plain_name_components_are_still_generated() {
        let reached = (0..512u64).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let name = super::random_name_component(&mut rng, 4, 10);
            !contains_quote_trigger(&name)
        });
        assert!(reached);
    }
}
