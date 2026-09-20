use clap::{Args, Parser, Subcommand, ValueEnum};
use std::path::PathBuf;

pub(crate) const DEFAULT_FUZZ_PROCESS_TIMEOUT_SECONDS: u64 = 10;
pub(crate) const DEFAULT_CONTAINER_IMAGE: &str = "dafnyutils-coreutils-fuzzer:latest";
pub(crate) const INTERNAL_TARGET_UID: u32 = 1000;
pub(crate) const INTERNAL_TARGET_GID: u32 = 1000;

fn parse_positive_iterations(value: &str) -> Result<usize, String> {
    let parsed = value
        .parse::<usize>()
        .map_err(|_| "iterations must be a positive integer".to_string())?;
    (parsed > 0)
        .then_some(parsed)
        .ok_or_else(|| "iterations must be a positive integer".to_string())
}

#[derive(Debug, Clone, Parser, PartialEq, Eq)]
#[command(
    name = "coreutils_fuzzer",
    version,
    about = "Oracle differential fuzzer for Dafny vs GNU coreutils"
)]
pub struct Cli {
    #[command(subcommand)]
    pub(crate) command: CliCommand,
}

#[derive(Debug, Clone, Subcommand, PartialEq, Eq)]
pub enum CliCommand {
    Fuzz(FuzzArgs),
    Capabilities(CapabilitiesArgs),
    Replay(ReplayArgs),
    Regression(RegressionArgs),
    #[command(name = "__chmod-exec-helper", hide = true)]
    ChmodExecHelper(ChmodExecHelperArgs),
    #[command(name = "__startup-run", hide = true)]
    StartupRun(StartupRunArgs),
    #[command(name = "__container-run-case", hide = true)]
    ContainerRunCase(ContainerRunCaseArgs),
}

#[derive(Debug, Clone, Args, PartialEq, Eq)]
pub struct ContainerRunCaseArgs {}

#[derive(Debug, Clone, Args, PartialEq, Eq)]
pub struct StartupRunArgs {
    #[arg(long)]
    pub(crate) target: PathBuf,
    #[arg(long, value_enum)]
    pub(crate) exec_kind: ExecKind,
    #[arg(long)]
    pub(crate) startup_library: PathBuf,
    #[arg(long, value_enum, default_value_t)]
    pub(crate) startup_profile: super::startup_protocol::StartupProfile,
    #[arg(long)]
    pub(crate) stdin_file: PathBuf,
    #[arg(long)]
    pub(crate) result_dir: PathBuf,
    #[arg(long, default_value_t = DEFAULT_FUZZ_PROCESS_TIMEOUT_SECONDS, value_parser = clap::value_parser!(u64).range(1..))]
    pub(crate) process_timeout_seconds: u64,
    /// Requested target disposition; the calling thread's blocked mask is inherited.
    #[arg(long, value_enum, default_value = "default")]
    pub(crate) sigpipe: super::startup_protocol::PipeDisposition,
    #[arg(last = true, allow_hyphen_values = true)]
    pub(crate) argv: Vec<std::ffi::OsString>,
}

#[derive(Debug, Clone, Args, PartialEq, Eq)]
pub struct RegressionArgs {
    #[arg(long)]
    pub(crate) suite: PathBuf,

    #[arg(long)]
    pub(crate) ref_bin: Option<PathBuf>,

    #[arg(long, value_enum, default_value_t = ExecKind::Native)]
    pub(crate) ref_kind: ExecKind,

    #[arg(long)]
    pub(crate) dut_bin: Option<PathBuf>,

    #[arg(long, value_enum, default_value_t = ExecKind::DotnetDll)]
    pub(crate) dut_kind: ExecKind,

    #[arg(long, default_value_t = DEFAULT_FUZZ_PROCESS_TIMEOUT_SECONDS, value_parser = clap::value_parser!(u64).range(1..))]
    pub(crate) process_timeout_seconds: u64,

    #[arg(long, default_value_t = false)]
    pub(crate) ignore_stderr: bool,

    #[arg(long)]
    pub(crate) metrics_out: Option<PathBuf>,

    #[arg(skip)]
    pub(crate) work_root: Option<PathBuf>,

    #[arg(long, default_value = DEFAULT_CONTAINER_IMAGE)]
    pub(crate) container_image: String,

    #[arg(skip = INTERNAL_TARGET_UID)]
    pub(crate) target_uid: u32,

    #[arg(skip = INTERNAL_TARGET_GID)]
    pub(crate) target_gid: u32,
}

#[derive(Debug, Clone, Args, PartialEq, Eq)]
pub struct CapabilitiesArgs {
    #[arg(long, value_enum, default_value_t = CapabilityFormat::Text)]
    pub(crate) format: CapabilityFormat,
}

#[derive(Debug, Clone, Copy, ValueEnum, PartialEq, Eq)]
pub(crate) enum CapabilityFormat {
    Text,
    Json,
}

#[derive(Debug, Clone, Args, PartialEq, Eq)]
pub struct ReplayArgs {
    #[arg(long)]
    pub(crate) repro: PathBuf,

    #[arg(long)]
    pub(crate) ref_bin: Option<PathBuf>,

    #[arg(long)]
    pub(crate) dut_bin: Option<PathBuf>,

    #[arg(long, value_enum)]
    pub(crate) ref_kind: Option<ExecKind>,

    #[arg(long, value_enum)]
    pub(crate) dut_kind: Option<ExecKind>,

    #[arg(long, value_parser = clap::value_parser!(u64).range(1..))]
    pub(crate) process_timeout_seconds: Option<u64>,

    #[arg(skip)]
    pub(crate) work_root: Option<PathBuf>,

    #[arg(long)]
    pub(crate) container_image: Option<String>,
}

pub(crate) fn run_capabilities(args: CapabilitiesArgs) -> Result<(), String> {
    let rendered = match args.format {
        CapabilityFormat::Text => super::capabilities::render_capabilities_text(),
        CapabilityFormat::Json => super::capabilities::render_capabilities_json()?,
    };
    println!("{rendered}");
    Ok(())
}

#[derive(Debug, Clone, Args, PartialEq, Eq)]
pub struct ChmodExecHelperArgs {
    #[arg(long, value_enum)]
    pub(crate) exec_kind: ExecKind,

    #[arg(long)]
    pub(crate) target: PathBuf,

    #[arg(long)]
    pub(crate) native_argv0: String,

    #[arg(long)]
    pub(crate) ready_fd: i32,

    #[arg(long)]
    pub(crate) go_fd: i32,

    #[arg(long)]
    pub(crate) status_fd: i32,

    #[arg(long, requires = "target_gid")]
    pub(crate) target_uid: Option<u32>,

    #[arg(long, requires = "target_uid")]
    pub(crate) target_gid: Option<u32>,

    #[arg(last = true, allow_hyphen_values = true)]
    pub(crate) argv: Vec<String>,
}

#[derive(Debug, Clone, Args, PartialEq, Eq)]
pub struct CampaignArgs {
    #[arg(long)]
    pub(crate) util: String,

    #[arg(long)]
    pub(crate) ref_bin: Option<PathBuf>,

    #[arg(long, value_enum, default_value_t = ExecKind::Native)]
    pub(crate) ref_kind: ExecKind,

    #[arg(long, allow_hyphen_values = true)]
    pub(crate) opts: Option<String>,

    #[arg(long, default_value_t = 100, value_parser = parse_positive_iterations)]
    pub(crate) iterations: usize,

    #[arg(long)]
    pub(crate) seed: Option<u64>,

    #[arg(long, default_value_t = 8)]
    pub(crate) max_args: usize,

    #[arg(long, default_value_t = 12)]
    pub(crate) max_fs_entries: usize,

    #[arg(long, value_enum, default_value_t = WorkdirMode::PerIteration)]
    pub(crate) workdir_mode: WorkdirMode,

    #[arg(long)]
    pub(crate) case_set: Option<PathBuf>,

    #[arg(long)]
    pub(crate) metrics_out: Option<PathBuf>,

    #[arg(skip)]
    pub(crate) work_root: Option<PathBuf>,

    #[arg(long, default_value = DEFAULT_CONTAINER_IMAGE)]
    pub(crate) container_image: String,

    #[arg(skip = INTERNAL_TARGET_UID)]
    pub(crate) target_uid: u32,

    #[arg(skip = INTERNAL_TARGET_GID)]
    pub(crate) target_gid: u32,
}

#[derive(Debug, Clone, Args, PartialEq, Eq)]
pub struct FuzzArgs {
    #[command(flatten)]
    pub(crate) common: CampaignArgs,

    #[arg(long)]
    #[arg(alias = "dafny-bin")]
    pub(crate) dut_bin: Option<PathBuf>,

    #[arg(long, value_enum, default_value_t = ExecKind::DotnetDll)]
    pub(crate) dut_kind: ExecKind,

    #[arg(long, default_value_t = 250)]
    pub(crate) shrink_attempts: usize,

    #[arg(long, default_value_t = DEFAULT_FUZZ_PROCESS_TIMEOUT_SECONDS, value_parser = clap::value_parser!(u64).range(1..))]
    pub(crate) process_timeout_seconds: u64,

    #[arg(long, default_value_t = false)]
    pub(crate) ignore_stderr: bool,

    #[arg(skip)]
    pub(crate) read_only_time_anchor_seconds: Option<i64>,

    #[arg(skip)]
    pub(crate) process_umask: Option<u32>,

    #[arg(skip)]
    pub(crate) container_image_id: Option<String>,
}

#[derive(Debug, Clone, Copy, ValueEnum, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExecKind {
    Native,
    DotnetDll,
}

#[derive(Debug, Clone, Copy, ValueEnum, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WorkdirMode {
    PerIteration,
    Shared,
}

pub(crate) fn parse_option_pool(opts: Option<&str>) -> Vec<String> {
    match opts {
        Some(raw) => raw
            .replace(',', " ")
            .split_whitespace()
            .map(ToString::to_string)
            .collect(),
        None => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::{Cli, CliCommand};
    use crate::utils::startup_protocol::StartupProfile;
    use clap::Parser;

    // Fuzz exposes the selected image while choosing the numeric target identity internally.
    #[test]
    fn fuzz_accepts_container_configuration() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "cat",
            "--container-image",
            "fuzz-image@sha256:abc",
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            unreachable!()
        };
        assert_eq!(args.common.container_image, "fuzz-image@sha256:abc");
        assert_eq!(args.common.target_uid, super::INTERNAL_TARGET_UID);
        assert_eq!(args.common.target_gid, super::INTERNAL_TARGET_GID);
    }

    // Regression uses the same internally selected identity as a fuzz campaign.
    #[test]
    fn regression_accepts_container_configuration() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "regression",
            "--suite",
            "/tmp/suite.json",
            "--container-image",
            "fuzz-image:tested",
        ])
        .unwrap();
        let CliCommand::Regression(args) = cli.command else {
            unreachable!()
        };
        assert_eq!(args.container_image, "fuzz-image:tested");
        assert_eq!(args.target_uid, super::INTERNAL_TARGET_UID);
        assert_eq!(args.target_gid, super::INTERNAL_TARGET_GID);
    }

    // Replay leaves container provenance unset and has no target-identity override.
    #[test]
    fn replay_defaults_to_saved_container_configuration() {
        let cli =
            Cli::try_parse_from(["coreutils_fuzzer", "replay", "--repro", "/tmp/repro"]).unwrap();
        let CliCommand::Replay(args) = cli.command else {
            unreachable!()
        };
        assert_eq!(args.container_image, None);
    }

    // Target identity is an internal isolation detail and cannot be supplied to public commands.
    #[test]
    fn public_commands_reject_target_identity_options() {
        for command in ["fuzz", "regression", "replay"] {
            let mut argv = vec!["coreutils_fuzzer", command];
            match command {
                "fuzz" => argv.extend(["--util", "cat"]),
                "regression" => argv.extend(["--suite", "/tmp/suite.json"]),
                "replay" => argv.extend(["--repro", "/tmp/repro"]),
                _ => unreachable!(),
            }
            argv.extend(["--target-uid", "2001"]);
            assert!(Cli::try_parse_from(argv).is_err(), "command={command}");
        }
    }

    // The hidden controller keeps managed transfer as its explicit compatibility default.
    #[test]
    fn startup_defaults_to_managed_transfer_profile() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "__startup-run",
            "--target",
            "/bin/true",
            "--exec-kind",
            "native",
            "--startup-library",
            "/tmp/startup.so",
            "--stdin-file",
            "/tmp/input",
            "--result-dir",
            "/tmp/result",
        ])
        .unwrap();
        let CliCommand::StartupRun(args) = cli.command else {
            unreachable!()
        };
        assert_eq!(args.startup_profile, StartupProfile::ManagedTransfer);
    }

    // Native-reference startup is selected only through the dedicated CLI option.
    #[test]
    fn startup_accepts_explicit_native_reference_profile() {
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "__startup-run",
            "--target",
            "/bin/true",
            "--exec-kind",
            "native",
            "--startup-library",
            "/tmp/reference.so",
            "--startup-profile",
            "native-reference",
            "--stdin-file",
            "/tmp/input",
            "--result-dir",
            "/tmp/result",
        ])
        .unwrap();
        let CliCommand::StartupRun(args) = cli.command else {
            unreachable!()
        };
        assert_eq!(args.startup_profile, StartupProfile::NativeReference);
    }
}
