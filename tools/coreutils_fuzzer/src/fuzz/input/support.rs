use crate::fuzz::mutation::generate_missing_operands;
use crate::fuzz::{FixtureBlueprint, GeneratedCase};
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

pub(super) fn has_option(option_pool: &[String], option: &str) -> bool {
    option_pool.iter().any(|candidate| candidate == option)
}

pub(super) fn existing_file_operands(fixture: &FixtureBlueprint) -> Vec<String> {
    fixture
        .files
        .iter()
        .map(|file| file.relative_path.display().to_string())
        .collect()
}

pub(super) fn pick_target_operand(
    existing: &[String],
    missing: &[String],
    rng: &mut StdRng,
    prefer_existing: bool,
) -> String {
    if !existing.is_empty() && (prefer_existing || rng.random_bool(0.65)) {
        return pick_string(existing, rng);
    }
    if !missing.is_empty() {
        return pick_string(missing, rng);
    }
    ".".to_string()
}

pub(super) fn pick_string(values: &[String], rng: &mut StdRng) -> String {
    let idx = rng.random_range(0..values.len());
    values[idx].clone()
}

pub(super) fn pick_file_or_missing(files: &[String], rng: &mut StdRng) -> String {
    if !files.is_empty() && rng.random_bool(0.85) {
        pick_string(files, rng)
    } else {
        pick_string(&generate_missing_operands(rng), rng)
    }
}

pub(super) fn case(argv: Vec<&str>, fixture: FixtureBlueprint, stdin: &[u8]) -> GeneratedCase {
    GeneratedCase {
        argv: argv.into_iter().map(str::to_string).collect(),
        fixture,
        stdin: stdin.to_vec(),
        cwd: PathBuf::from("."),
    }
}
