use clap::Parser;
use coreutils_fuzzer::{
    fuzzer_outcome_marker, run_cli, Cli, FUZZER_BUILD_FAILURE, FUZZER_OUTCOME_MARKER_PREFIX,
};

fn main() {
    let cli = Cli::parse();
    if let Err(err) = run_cli(cli) {
        if !err.contains(FUZZER_OUTCOME_MARKER_PREFIX) {
            eprintln!("{}", fuzzer_outcome_marker(FUZZER_BUILD_FAILURE));
        }
        eprintln!("{err}");
        std::process::exit(2);
    }
}
