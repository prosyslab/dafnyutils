use super::{generate_argv, generators, support};
use crate::fuzz::FixtureBlueprint;
use rand::prelude::SliceRandom;
use rand::rngs::StdRng;
use rand::Rng;

type OperandSource = fn(&FixtureBlueprint) -> Vec<String>;
type ReplacementGenerator = fn(&[String], usize, &mut StdRng) -> String;

pub(super) fn mutate_generic_argv(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
    argv: &mut Vec<String>,
) {
    if argv.is_empty() || rng.random_bool(0.35) {
        regenerate_argv(util, option_pool, rng, max_args, fixture, argv);
        return;
    }
    mutate_existing_argv(
        rng,
        max_args,
        fixture,
        argv,
        FixtureBlueprint::existing_operands,
        random_replacement_value,
    );
}

pub(in crate::fuzz::input) fn regenerate_argv(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
    argv: &mut Vec<String>,
) {
    *argv = generate_argv(
        util,
        &crate::fuzz::mutation::utility_profile(util),
        option_pool,
        rng,
        max_args,
        fixture,
    );
}

pub(in crate::fuzz::input) fn mutate_existing_argv(
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
    argv: &mut Vec<String>,
    operand_source: OperandSource,
    replacement: ReplacementGenerator,
) {
    match rng.random_range(0..4) {
        0 if argv.len() > 1 => {
            let idx = rng.random_range(0..argv.len());
            argv.remove(idx);
        }
        1 if argv.len() < max_args.max(1) => {
            let operands = operand_source(fixture);
            argv.push(support::pick_target_operand(
                &operands,
                &crate::fuzz::mutation::generate_missing_operands(rng),
                rng,
                true,
            ));
        }
        2 => {
            let idx = rng.random_range(0..argv.len());
            argv[idx] = replacement(argv, idx, rng);
        }
        _ => argv.shuffle(rng),
    }
}

pub(in crate::fuzz::input) fn random_argument_value(rng: &mut StdRng) -> String {
    match rng.random_range(0..4) {
        0 => "-".to_string(),
        1 => format!("fuzz-name-{}", rng.random_range(0..1000)),
        2 => generators::chmod::random_chmod_mode(rng),
        _ => generators::touch::random_date_string(rng),
    }
}

pub(in crate::fuzz::input) fn random_non_stdin_argument_value(rng: &mut StdRng) -> String {
    match rng.random_range(0..3) {
        0 => format!("fuzz-name-{}", rng.random_range(0..1000)),
        1 => generators::chmod::random_chmod_mode(rng),
        _ => generators::touch::random_date_string(rng),
    }
}

fn random_replacement_value(_argv: &[String], _idx: usize, rng: &mut StdRng) -> String {
    random_argument_value(rng)
}
