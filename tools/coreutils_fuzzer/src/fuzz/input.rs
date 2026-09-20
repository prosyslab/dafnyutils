use super::{FixtureBlueprint, GeneratedCase, UtilityProfile};
use crate::utils::capabilities::capability_for;
use rand::rngs::StdRng;
use std::fmt::Debug;

mod fixtures;
pub(crate) mod generators;
mod mutation;
mod pattern;
mod support;

type ScenarioFn = fn(usize) -> Option<GeneratedCase>;
type MutationFn = fn(&str, &[String], &mut StdRng, usize, &FixtureBlueprint, &mut Vec<String>);

pub(crate) trait InputGenerator: Debug + Sync {
    fn generate_argv(
        &self,
        profile: &UtilityProfile,
        option_pool: &[String],
        rng: &mut StdRng,
        max_args: usize,
        fixture: &FixtureBlueprint,
    ) -> Vec<String>;

    fn scenario_case(&self, iteration: usize) -> Option<GeneratedCase>;

    fn mutate_argv(
        &self,
        util: &str,
        option_pool: &[String],
        rng: &mut StdRng,
        max_args: usize,
        fixture: &FixtureBlueprint,
        argv: &mut Vec<String>,
    );

    fn has_utility_pattern(&self) -> bool;
}

#[derive(Debug)]
pub(crate) struct PatternInputGenerator {
    argv_pattern: Option<&'static pattern::ArgvPattern>,
    scenario: ScenarioFn,
    mutation: MutationFn,
}

impl PatternInputGenerator {
    const fn generic(scenario: ScenarioFn) -> Self {
        Self {
            argv_pattern: None,
            scenario,
            mutation: mutation::mutate_generic_argv,
        }
    }

    const fn patterned(argv_pattern: &'static pattern::ArgvPattern, scenario: ScenarioFn) -> Self {
        Self {
            argv_pattern: Some(argv_pattern),
            scenario,
            mutation: mutation::mutate_generic_argv,
        }
    }

    const fn with_mutator(mut self, mutation: MutationFn) -> Self {
        self.mutation = mutation;
        self
    }
}

impl InputGenerator for PatternInputGenerator {
    fn generate_argv(
        &self,
        profile: &UtilityProfile,
        option_pool: &[String],
        rng: &mut StdRng,
        max_args: usize,
        fixture: &FixtureBlueprint,
    ) -> Vec<String> {
        match self.argv_pattern {
            Some(argv_pattern) => {
                pattern::generate(argv_pattern, option_pool, rng, max_args, fixture)
            }
            None => pattern::generate_generic(profile, option_pool, rng, max_args, fixture),
        }
    }

    fn scenario_case(&self, iteration: usize) -> Option<GeneratedCase> {
        (self.scenario)(iteration)
    }

    fn mutate_argv(
        &self,
        util: &str,
        option_pool: &[String],
        rng: &mut StdRng,
        max_args: usize,
        fixture: &FixtureBlueprint,
        argv: &mut Vec<String>,
    ) {
        (self.mutation)(util, option_pool, rng, max_args, fixture, argv);
    }

    fn has_utility_pattern(&self) -> bool {
        self.argv_pattern.is_some()
    }
}

pub(crate) fn generate_argv(
    util: &str,
    profile: &UtilityProfile,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
) -> Vec<String> {
    match capability_for(util) {
        Some(capability) => {
            capability
                .input_generator
                .generate_argv(profile, option_pool, rng, max_args, fixture)
        }
        None => pattern::generate_generic(profile, option_pool, rng, max_args, fixture),
    }
}

pub(crate) fn scenario_case(util: &str, iteration: usize) -> Option<GeneratedCase> {
    capability_for(util)?
        .input_generator
        .scenario_case(iteration)
}

pub(crate) fn mutate_argv(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
    argv: &mut Vec<String>,
) {
    match capability_for(util) {
        Some(capability) => {
            capability
                .input_generator
                .mutate_argv(util, option_pool, rng, max_args, fixture, argv)
        }
        None => mutation::mutate_generic_argv(util, option_pool, rng, max_args, fixture, argv),
    }
}

pub(crate) use generators::ls::{
    ls_argv_requires_followed_entry_metadata, ls_argv_respects_mode_dependencies,
    ls_direct_ctime_case, ls_short_ctime_sort_case, LsDirectCtimeCase, LsDirectOperandFollow,
    LsShortCtimeSortCase,
};
#[cfg(test)]
pub(crate) fn generate_argv_for_test(
    util: &str,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
) -> Vec<String> {
    generate_argv(
        util,
        &super::mutation::utility_profile(util),
        option_pool,
        rng,
        max_args,
        fixture,
    )
}

#[cfg(test)]
pub(crate) fn random_chmod_mode_for_test(rng: &mut StdRng) -> String {
    generators::chmod::random_chmod_mode(rng)
}
