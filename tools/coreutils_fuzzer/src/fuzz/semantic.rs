use super::{FsNodeSnapshot, FsSnapshot, GeneratedCase, RunResult};
use crate::utils::arg_semantics::path_operand_args;
use crate::utils::arg_semantics::should_consume_stdin_from_argv;
use std::collections::BTreeSet;
use std::path::{Component, Path, PathBuf};

const KNOWN_BUCKETS: &[&str] = &[
    "arg:empty",
    "arg:nonempty",
    "exit:success",
    "exit:error",
    "fixture:has-file",
    "fixture:has-dir",
    "fixture:has-symlink",
    "fs:unchanged",
    "fs:file-added",
    "fs:file-removed",
    "fs:file-content-changed",
    "fs:mode-changed",
    "fs:target-changed",
    "fs:time-changed",
    "operand:dash",
    "operand:existing-file",
    "operand:existing-dir",
    "operand:missing-path",
    "operand:quote-trigger",
    "operand:symlink",
    "stream:stderr-empty",
    "stream:stderr-nonempty",
    "stream:stdout-empty",
    "stream:stdout-nonempty",
    "stdin:empty",
    "stdin:provided",
    "stdin:consumed",
];

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct SemanticCoverage {
    seen: BTreeSet<String>,
}

impl SemanticCoverage {
    pub(crate) fn observe_case(
        &mut self,
        util: &str,
        case: &GeneratedCase,
        result: &RunResult,
        pre_fs: &FsSnapshot,
        post_fs: &FsSnapshot,
    ) -> bool {
        let buckets = classify_case(util, case, result, pre_fs, post_fs);
        let before = self.seen.len();
        self.seen.extend(buckets);
        self.seen.len() != before
    }

    pub(crate) fn render_report(&self) -> String {
        let known: BTreeSet<String> = KNOWN_BUCKETS
            .iter()
            .map(|bucket| bucket.to_string())
            .collect();
        let known_seen = self.seen.intersection(&known).count();
        let missing: Vec<String> = known
            .difference(&self.seen)
            .take(10)
            .map(|bucket| (*bucket).clone())
            .collect();
        let extra = self.seen.difference(&known).count();
        let missing_suffix = if missing.is_empty() {
            "none".to_string()
        } else {
            missing.join(", ")
        };
        format!(
            "Semantic coverage: buckets {}/{} ({:.1}%), extra={}, missing: {}",
            known_seen,
            known.len(),
            coverage_percent(known_seen, known.len()),
            extra,
            missing_suffix
        )
    }

    pub(crate) fn counts(&self) -> (usize, usize) {
        (self.seen.len(), KNOWN_BUCKETS.len())
    }
}

pub(crate) fn classify_case(
    util: &str,
    case: &GeneratedCase,
    result: &RunResult,
    pre_fs: &FsSnapshot,
    post_fs: &FsSnapshot,
) -> BTreeSet<String> {
    let mut buckets = BTreeSet::new();
    classify_args(util, case, pre_fs, &mut buckets);
    classify_fixture(case, &mut buckets);
    classify_result(util, case, result, &mut buckets);
    classify_fs_effects(util, pre_fs, post_fs, &mut buckets);
    buckets
}

fn classify_args(
    util: &str,
    case: &GeneratedCase,
    pre_fs: &FsSnapshot,
    buckets: &mut BTreeSet<String>,
) {
    if case.argv.is_empty() {
        buckets.insert("arg:empty".to_string());
    } else {
        buckets.insert("arg:nonempty".to_string());
    }

    for operand in path_operand_args(util, &case.argv) {
        if operand == "-" {
            buckets.insert("operand:dash".to_string());
            continue;
        }
        // Reaching the shell-quoting branches is the point of the trigger
        // generator, so record it rather than assuming it happened.
        if super::mutation::contains_quote_trigger(operand) {
            buckets.insert("operand:quote-trigger".to_string());
        }
        let key = path_key(&case.cwd, operand);
        match pre_fs.get(&key) {
            Some(node) if node.kind == "file" => {
                buckets.insert("operand:existing-file".to_string());
            }
            Some(node) if node.kind == "dir" => {
                buckets.insert("operand:existing-dir".to_string());
            }
            Some(node) if node.kind == "symlink" => {
                buckets.insert("operand:symlink".to_string());
            }
            Some(_) => {
                buckets.insert("operand:existing-other".to_string());
            }
            None => {
                buckets.insert("operand:missing-path".to_string());
            }
        }
    }
}

fn classify_fixture(case: &GeneratedCase, buckets: &mut BTreeSet<String>) {
    if !case.fixture.files.is_empty() {
        buckets.insert("fixture:has-file".to_string());
    }
    if !case.fixture.directories.is_empty() {
        buckets.insert("fixture:has-dir".to_string());
    }
    if !case.fixture.symlinks.is_empty() {
        buckets.insert("fixture:has-symlink".to_string());
    }
}

fn classify_result(
    util: &str,
    case: &GeneratedCase,
    result: &RunResult,
    buckets: &mut BTreeSet<String>,
) {
    if result.termination.is_success() {
        buckets.insert("exit:success".to_string());
    } else {
        buckets.insert("exit:error".to_string());
    }
    buckets.insert(
        if result.stdout.is_empty() {
            "stream:stdout-empty"
        } else {
            "stream:stdout-nonempty"
        }
        .to_string(),
    );
    buckets.insert(
        if result.stderr.is_empty() {
            "stream:stderr-empty"
        } else {
            "stream:stderr-nonempty"
        }
        .to_string(),
    );
    buckets.insert(
        if case.stdin.is_empty() {
            "stdin:empty"
        } else {
            "stdin:provided"
        }
        .to_string(),
    );
    if !case.stdin.is_empty() && should_consume_stdin_from_argv(util, &case.argv) {
        buckets.insert("stdin:consumed".to_string());
    }
}

fn classify_fs_effects(
    util: &str,
    pre_fs: &FsSnapshot,
    post_fs: &FsSnapshot,
    buckets: &mut BTreeSet<String>,
) {
    let pre_keys: BTreeSet<&String> = pre_fs.keys().collect();
    let post_keys: BTreeSet<&String> = post_fs.keys().collect();
    let mut changed = false;

    if post_keys
        .difference(&pre_keys)
        .any(|path| node_is_file(post_fs.get(*path)))
    {
        buckets.insert("fs:file-added".to_string());
        changed = true;
    }
    if pre_keys
        .difference(&post_keys)
        .any(|path| node_is_file(pre_fs.get(*path)))
    {
        buckets.insert("fs:file-removed".to_string());
        changed = true;
    }

    for key in pre_keys.intersection(&post_keys) {
        let before = pre_fs.get(*key).expect("pre key exists");
        let after = post_fs.get(*key).expect("post key exists");
        if before.kind != after.kind {
            buckets.insert("fs:kind-changed".to_string());
            changed = true;
        }
        if before.data != after.data {
            buckets.insert("fs:file-content-changed".to_string());
            changed = true;
        }
        if before.mode_octal != after.mode_octal {
            buckets.insert("fs:mode-changed".to_string());
            changed = true;
        }
        if before.target != after.target {
            buckets.insert("fs:target-changed".to_string());
            changed = true;
        }
        if semantic_timestamps_matter(util) && before.times != after.times {
            buckets.insert("fs:time-changed".to_string());
            changed = true;
        }
    }

    if !changed && pre_keys == post_keys {
        buckets.insert("fs:unchanged".to_string());
    }
}

fn semantic_timestamps_matter(util: &str) -> bool {
    matches!(util, "touch")
}

fn node_is_file(node: Option<&FsNodeSnapshot>) -> bool {
    matches!(node, Some(node) if node.kind == "file")
}

fn path_key(cwd: &Path, operand: &str) -> String {
    let path = if operand == "." {
        cwd.to_path_buf()
    } else {
        cwd.join(operand)
    };
    normalize_relative_path(&path)
        .display()
        .to_string()
        .if_empty_then_dot()
}

fn normalize_relative_path(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                out.pop();
            }
            Component::Normal(part) => out.push(part),
            Component::RootDir | Component::Prefix(_) => {}
        }
    }
    out
}

fn coverage_percent(numerator: usize, denominator: usize) -> f64 {
    if denominator == 0 {
        100.0
    } else {
        (numerator as f64 * 100.0) / denominator as f64
    }
}

trait EmptyPathLabel {
    fn if_empty_then_dot(self) -> String;
}

impl EmptyPathLabel for String {
    fn if_empty_then_dot(self) -> String {
        if self.is_empty() {
            ".".to_string()
        } else {
            self
        }
    }
}
