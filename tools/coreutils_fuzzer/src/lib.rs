mod fuzz;
mod utils;

pub const FUZZER_OUTCOME_MARKER_PREFIX: &str = "FUZZER_OUTCOME=";
pub const FUZZER_INFRASTRUCTURE_FAILURE: &str = "fuzzer_infrastructure_failure";
pub const FUZZER_BUILD_FAILURE: &str = "fuzzer_build_failure";
pub const FUZZER_TARGET_SPAWN_FAILURE: &str = "fuzzer_target_spawn_failure";
pub const FUZZER_DOTNET_RUNTIME_FAILURE: &str = "fuzzer_dotnet_runtime_failure";
pub const FUZZER_TIMEOUT: &str = "fuzzer_timeout";
pub const FUZZER_UNSUPPORTED_CAPABILITY: &str = "fuzzer_unsupported_capability";
pub const REPLAY_NOT_REPRODUCED: &str = "replay_not_reproduced";
pub const REGRESSION_FAILURE: &str = "regression_failure";
pub const INCOMPLETE_COVERAGE: &str = "incomplete_coverage";
pub const SEMANTIC_MISMATCH: &str = "semantic_mismatch";

pub use fuzz::run_fuzzer;
pub use utils::cli::{Cli, CliCommand, ExecKind, FuzzArgs, RegressionArgs, WorkdirMode};
pub use utils::world_json::{
    DirEntryJson, DirHandleJson, FileKindJson, FsNodeJson, InodeFileSystemJson, InodeNamespaceJson,
    InodeRecordJson, IoSnapshot, IoTransition, LinkCountJson, ObservationOutcome, OwnershipJson,
    ProcessCredentialsJson, StorageInfoJson, IO_SNAPSHOT_SCHEMA_VERSION,
};

pub fn run_cli(cli: Cli) -> Result<(), String> {
    match cli.command {
        CliCommand::Fuzz(args) => run_fuzzer(args),
        CliCommand::Capabilities(args) => utils::cli::run_capabilities(args),
        CliCommand::Replay(args) => fuzz::replay::run_replay(args),
        CliCommand::Regression(args) => fuzz::regression::run_regression(args),
        CliCommand::ChmodExecHelper(args) => fuzz::execution::run_chmod_exec_helper(args),
        CliCommand::StartupRun(args) => fuzz::startup::run_startup(args),
        CliCommand::ContainerRunCase(args) => fuzz::container::run_container_case(args),
    }
}

pub fn fuzzer_outcome_marker(outcome: &str) -> String {
    format!("{FUZZER_OUTCOME_MARKER_PREFIX}{outcome}")
}

pub fn fuzzer_infrastructure_failure(reason: impl std::fmt::Display) -> String {
    format!(
        "{}\n{reason}",
        fuzzer_outcome_marker(FUZZER_INFRASTRUCTURE_FAILURE)
    )
}

#[cfg(test)]
use rand::rngs::StdRng;
#[cfg(test)]
use rand::SeedableRng;

#[cfg(test)]
pub(crate) use fuzz::compare::{compare_results_with_roots, render_text_diff};
#[cfg(test)]
pub(crate) use fuzz::corpus::InterestingCorpus;
#[cfg(test)]
pub(crate) use fuzz::coverage::OptionCoverage;
#[cfg(test)]
pub(crate) use fuzz::execution::apply_deterministic_env;
#[cfg(test)]
pub(crate) use fuzz::fixture::{materialize_fixture, prepare_iteration_dirs, reset_dir};
#[cfg(test)]
pub(crate) use fuzz::input::scenario_case;
#[cfg(test)]
pub(crate) use fuzz::mutation::generate_case;
#[cfg(test)]
pub(crate) use fuzz::runtime::{resolve_fuzz_paths, work_root_for_util};
#[cfg(test)]
pub(crate) use fuzz::semantic::{classify_case, SemanticCoverage};
#[cfg(test)]
pub(crate) use utils::cli::parse_option_pool;

#[cfg(test)]
mod tests;
