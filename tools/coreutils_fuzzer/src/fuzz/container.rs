// Unit tests use the daemon-free local executor, so production-only Docker items are dormant there.
#![cfg_attr(test, allow(dead_code))]

use super::shrink::{execute_case_in_work_dir, CaseExecutor, RawCaseObservation};
use super::{GeneratedCase, ResolvedPaths, ResolvedTarget};
use crate::utils::cli::{CampaignArgs, ContainerRunCaseArgs, ExecKind, FuzzArgs, WorkdirMode};
use crate::utils::process::run_command_with_timeout_and_input;
use crate::{fuzzer_outcome_marker, FUZZER_TARGET_SPAWN_FAILURE};
use serde::{Deserialize, Serialize};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

const CONTAINER_PROTOCOL_VERSION: u32 = 1;
const COMPOSE_FILE: &str = "tools/coreutils_fuzzer/docker-compose.yaml";
const COMPOSE_SERVICE: &str = "coreutils-fuzzer";
const CONTAINER_RUNNER_PATH: &str = "/opt/coreutils-fuzzer-staging/coreutils_fuzzer";
const CONTAINER_WORK_ROOT: &str = "/fuzz/work";
const CONTAINER_SHARED_ROOT: &str = "/fuzz/shared";
static CONTAINER_SEQUENCE: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ContainerCaseRequest {
    protocol_version: u32,
    util: String,
    reference: ContainerTarget,
    dut: ContainerTarget,
    case: GeneratedCase,
    seed: u64,
    child_iteration: usize,
    work_iteration: usize,
    workdir_mode: WorkdirMode,
    process_timeout_seconds: u64,
    read_only_time_anchor_seconds: Option<i64>,
    process_umask: u32,
    target_uid: u32,
    target_gid: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ContainerTarget {
    kind: ExecKind,
    path: PathBuf,
}

pub(crate) struct DockerCaseExecutor {
    container_id: String,
    image_id: String,
    target_identity: String,
    reference: ContainerTarget,
    dut: ContainerTarget,
}

pub(crate) enum CommandCaseExecutor {
    Docker(DockerCaseExecutor),
    #[cfg(test)]
    Local(TestLocalCaseExecutor),
}

#[cfg(test)]
pub(crate) struct TestLocalCaseExecutor {
    paths: ResolvedPaths,
    work_root: super::runtime::OwnedWorkRoot,
    shared_root: Option<PathBuf>,
}

impl CommandCaseExecutor {
    pub(crate) fn create(args: &FuzzArgs, paths: &ResolvedPaths) -> Result<Self, String> {
        #[cfg(test)]
        {
            let work_root = super::runtime::temporary_work_root(
                "coreutils-fuzzer-test-local-",
                args.common.work_root.as_deref(),
            )?;
            let shared_root = super::runtime::prepare_shared_root(
                work_root.path(),
                args.common.workdir_mode,
                args.common.seed.unwrap_or_default(),
            )?;
            Ok(Self::Local(TestLocalCaseExecutor {
                paths: paths.clone(),
                work_root,
                shared_root,
            }))
        }
        #[cfg(not(test))]
        {
            DockerCaseExecutor::create(args, paths).map(Self::Docker)
        }
    }

    pub(crate) fn backend_name(&self) -> &'static str {
        match self {
            Self::Docker(_) => "docker-compose",
            #[cfg(test)]
            Self::Local(_) => "local-test",
        }
    }

    pub(crate) fn image_id(&self) -> Option<&str> {
        match self {
            Self::Docker(executor) => Some(executor.image_id()),
            #[cfg(test)]
            Self::Local(_) => None,
        }
    }

    pub(crate) fn work_root_base(&self) -> &Path {
        match self {
            Self::Docker(_) => Path::new("/fuzz"),
            #[cfg(test)]
            Self::Local(executor) => executor.work_root.effective_base(),
        }
    }

    pub(crate) fn work_root_path(&self) -> &Path {
        match self {
            Self::Docker(_) => Path::new(CONTAINER_WORK_ROOT),
            #[cfg(test)]
            Self::Local(executor) => executor.work_root.path(),
        }
    }

    pub(crate) fn work_root_source(&self) -> &'static str {
        match self {
            Self::Docker(_) => "container",
            #[cfg(test)]
            Self::Local(executor) => executor.work_root.source().as_str(),
        }
    }

    pub(crate) fn discover_common_options(
        &mut self,
        timeout: Duration,
    ) -> Result<Vec<String>, String> {
        match self {
            Self::Docker(executor) => executor.discover_common_options(timeout),
            #[cfg(test)]
            Self::Local(_) => Ok(Vec::new()),
        }
    }
}

impl CaseExecutor for CommandCaseExecutor {
    fn execute(
        &mut self,
        args: &FuzzArgs,
        seed: u64,
        child_iteration: usize,
        work_iteration: usize,
        case: &GeneratedCase,
    ) -> Result<RawCaseObservation, String> {
        match self {
            Self::Docker(executor) => {
                executor.execute(args, seed, child_iteration, work_iteration, case)
            }
            #[cfg(test)]
            Self::Local(executor) => execute_case_in_work_dir(
                args,
                &executor.paths,
                executor.work_root.path(),
                executor.shared_root.as_deref(),
                seed,
                child_iteration,
                work_iteration,
                case,
                None,
            ),
        }
    }
}

impl DockerCaseExecutor {
    pub(crate) fn create(args: &FuzzArgs, paths: &ResolvedPaths) -> Result<Self, String> {
        if args.common.container_image.trim().is_empty() {
            return Err("container image must not be empty".to_string());
        }
        let sequence = CONTAINER_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let default_name = format!(
            "dafnyutils-fuzzer-{}-{}-{sequence}",
            crate::utils::paths::sanitize_util_name(&args.common.util),
            std::process::id()
        );
        let name = std::env::var("FUZZ_CONTAINER_NAME").unwrap_or(default_name);
        let mut compose = Command::new("docker");
        compose
            .args([
                "compose",
                "-f",
                COMPOSE_FILE,
                "run",
                "--detach",
                "--no-deps",
                "--name",
                &name,
                COMPOSE_SERVICE,
            ])
            .env("COREUTILS_FUZZER_IMAGE", &args.common.container_image);
        let output = docker_output(&mut compose, "create and start fuzz Compose service")?;
        let container_id = output.trim().to_string();
        if container_id.is_empty() {
            return Err("docker compose run returned an empty container id".to_string());
        }
        let mut executor = Self {
            container_id,
            image_id: String::new(),
            target_identity: format!("{}:{}", args.common.target_uid, args.common.target_gid),
            reference: ContainerTarget {
                kind: paths.reference.kind,
                path: PathBuf::new(),
            },
            dut: ContainerTarget {
                kind: paths.dut.kind,
                path: PathBuf::new(),
            },
        };
        executor.stage_runner()?;
        executor.reference =
            executor.stage_target(&paths.reference, "reference", &args.common.util)?;
        executor.dut = executor.stage_target(&paths.dut, "dut", &args.common.util)?;
        executor.image_id = docker_output(
            Command::new("docker").args([
                "inspect",
                "--format",
                "{{.Image}}",
                executor.container_id.as_str(),
            ]),
            "inspect fuzz container image",
        )?
        .trim()
        .to_string();
        Ok(executor)
    }

    pub(crate) fn image_id(&self) -> &str {
        &self.image_id
    }

    fn discover_common_options(&mut self, timeout: Duration) -> Result<Vec<String>, String> {
        let reference = self.target_help(&self.reference, timeout)?;
        let dut = self.target_help(&self.dut, timeout)?;
        let reference = collect_options(&reference);
        let dut = collect_options(&dut);
        Ok(reference.intersection(&dut).cloned().collect())
    }

    fn target_help(&self, target: &ContainerTarget, timeout: Duration) -> Result<Vec<u8>, String> {
        let mut command = Command::new("docker");
        command.args([
            "exec",
            "-i",
            "--user",
            self.target_identity.as_str(),
            self.container_id.as_str(),
        ]);
        match target.kind {
            ExecKind::Native => {
                command.arg(&target.path);
            }
            ExecKind::DotnetDll => {
                command.arg("dotnet").arg(&target.path);
            }
        }
        command.arg("--help");
        let output = run_command_with_timeout_and_input(&mut command, &[], timeout)
            .map_err(|error| format!("failed to collect container target help: {error:?}"))?;
        if !output.status.success() {
            return Err(container_child_failure(
                &output,
                "container target --help",
                false,
            ));
        }
        let mut bytes = output.stdout;
        bytes.extend(output.stderr);
        Ok(bytes)
    }

    fn stage_runner(&self) -> Result<(), String> {
        let executable = std::env::current_exe()
            .map_err(|error| format!("failed to resolve current fuzzer executable: {error}"))?;
        docker_copy_file(
            &executable,
            &self.container_id,
            "/opt/coreutils-fuzzer-staging",
            "fuzzer runner",
        )
    }

    fn stage_target(
        &self,
        target: &ResolvedTarget,
        role: &str,
        utility: &str,
    ) -> Result<ContainerTarget, String> {
        let container_path = match target.kind {
            ExecKind::Native => {
                let destination = format!("/opt/coreutils-fuzzer-staging/{role}");
                docker_copy_file(&target.path, &self.container_id, &destination, role)?;
                PathBuf::from(destination).join(target.path.file_name().ok_or_else(|| {
                    format!(
                        "{role} native target has no file name: `{}`",
                        target.path.display()
                    )
                })?)
            }
            ExecKind::DotnetDll => {
                let file_name = target.path.file_name().ok_or_else(|| {
                    format!(
                        "{role} .NET target has no file name: `{}`",
                        target.path.display()
                    )
                })?;
                let destination = format!("/opt/coreutils-fuzzer-staging/{role}-runtime");
                for file in runtime_files(target, utility == "touch")? {
                    docker_copy_file(&file, &self.container_id, &destination, role)?;
                }
                PathBuf::from(destination).join(file_name)
            }
        };
        Ok(ContainerTarget {
            kind: target.kind,
            path: container_path,
        })
    }

    fn execute_request(
        &mut self,
        args: &FuzzArgs,
        seed: u64,
        child_iteration: usize,
        work_iteration: usize,
        case: &GeneratedCase,
    ) -> Result<RawCaseObservation, String> {
        let request = ContainerCaseRequest {
            protocol_version: CONTAINER_PROTOCOL_VERSION,
            util: args.common.util.clone(),
            reference: self.reference.clone(),
            dut: self.dut.clone(),
            case: case.clone(),
            seed,
            child_iteration,
            work_iteration,
            workdir_mode: args.common.workdir_mode,
            process_timeout_seconds: args.process_timeout_seconds,
            read_only_time_anchor_seconds: args.read_only_time_anchor_seconds,
            process_umask: args.process_umask.ok_or_else(|| {
                "container execution requires an explicit process umask".to_string()
            })?,
            target_uid: args.common.target_uid,
            target_gid: args.common.target_gid,
        };
        let bytes = serde_json::to_vec(&request)
            .map_err(|error| format!("failed to encode container case request: {error}"))?;
        let mut command = Command::new("docker");
        command.args([
            "exec",
            "-i",
            self.container_id.as_str(),
            CONTAINER_RUNNER_PATH,
            "__container-run-case",
        ]);
        let timeout = Duration::from_secs(
            args.process_timeout_seconds
                .saturating_mul(2)
                .saturating_add(10),
        );
        let output = run_command_with_timeout_and_input(&mut command, &bytes, timeout)
            .map_err(|error| format!("failed to execute container case runner: {error:?}"))?;
        if !output.status.success() {
            return Err(container_child_failure(
                &output,
                "container case runner",
                true,
            ));
        }
        serde_json::from_slice(&output.stdout).map_err(|error| {
            format!(
                "container case runner returned invalid JSON: {error}; stderr={}",
                String::from_utf8_lossy(&output.stderr)
            )
        })
    }
}

impl CaseExecutor for DockerCaseExecutor {
    fn execute(
        &mut self,
        args: &FuzzArgs,
        seed: u64,
        child_iteration: usize,
        work_iteration: usize,
        case: &GeneratedCase,
    ) -> Result<RawCaseObservation, String> {
        self.execute_request(args, seed, child_iteration, work_iteration, case)
    }
}

impl Drop for DockerCaseExecutor {
    fn drop(&mut self) {
        if self.container_id.is_empty() {
            return;
        }
        let _ = Command::new("docker")
            .args(["rm", "--force", self.container_id.as_str()])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status();
    }
}

pub(crate) fn run_container_case(_args: ContainerRunCaseArgs) -> Result<(), String> {
    let mut bytes = Vec::new();
    std::io::stdin()
        .read_to_end(&mut bytes)
        .map_err(|error| format!("failed to read container case request: {error}"))?;
    let request: ContainerCaseRequest = serde_json::from_slice(&bytes)
        .map_err(|error| format!("failed to decode container case request: {error}"))?;
    if request.protocol_version != CONTAINER_PROTOCOL_VERSION {
        return Err(format!(
            "unsupported container protocol version {}; expected {CONTAINER_PROTOCOL_VERSION}",
            request.protocol_version
        ));
    }
    // The trusted runner prepares fixtures as root; both targets run directly
    // with the configured non-root identity in this Docker container.
    let paths = ResolvedPaths {
        reference: ResolvedTarget {
            kind: request.reference.kind,
            path: request.reference.path,
            label: "reference",
        },
        dut: ResolvedTarget {
            kind: request.dut.kind,
            path: request.dut.path,
            label: "dut",
        },
    };
    let args = FuzzArgs {
        common: CampaignArgs {
            util: request.util,
            ref_bin: Some(paths.reference.path.clone()),
            ref_kind: paths.reference.kind,
            opts: None,
            iterations: 1,
            seed: Some(request.seed),
            max_args: request.case.argv.len(),
            max_fs_entries: request.case.fixture.directories.len()
                + request.case.fixture.files.len()
                + request.case.fixture.symlinks.len()
                + request.case.fixture.hardlinks.len(),
            workdir_mode: request.workdir_mode,
            case_set: None,
            metrics_out: None,
            work_root: None,
            container_image: String::new(),
            target_uid: request.target_uid,
            target_gid: request.target_gid,
        },
        dut_bin: Some(paths.dut.path.clone()),
        dut_kind: paths.dut.kind,
        shrink_attempts: 0,
        process_timeout_seconds: request.process_timeout_seconds,
        ignore_stderr: false,
        read_only_time_anchor_seconds: request.read_only_time_anchor_seconds,
        process_umask: Some(request.process_umask),
        container_image_id: None,
    };
    let work_root = Path::new(CONTAINER_WORK_ROOT);
    std::fs::create_dir_all(work_root).map_err(|error| {
        format!("failed to create container work root `{CONTAINER_WORK_ROOT}`: {error}")
    })?;
    let shared_root =
        (request.workdir_mode == WorkdirMode::Shared).then_some(Path::new(CONTAINER_SHARED_ROOT));
    let observation = execute_case_in_work_dir(
        &args,
        &paths,
        work_root,
        shared_root,
        request.seed,
        request.child_iteration,
        request.work_iteration,
        &request.case,
        Some((request.target_uid, request.target_gid)),
    )?;
    serde_json::to_writer(std::io::stdout(), &observation)
        .map_err(|error| format!("failed to encode container case response: {error}"))?;
    Ok(())
}

fn runtime_files(target: &ResolvedTarget, touch_parser: bool) -> Result<Vec<PathBuf>, String> {
    let mut files = vec![target.path.clone()];
    if target.kind == ExecKind::DotnetDll {
        files.push(target.path.with_extension("deps.json"));
        files.push(target.path.with_extension("runtimeconfig.json"));
        if touch_parser {
            files.push(target.path.with_file_name("touch_time_parser"));
        }
    }
    for path in &files {
        let metadata = std::fs::symlink_metadata(path).map_err(|error| {
            format!(
                "candidate runtime file `{}` is unavailable: {error}",
                path.display()
            )
        })?;
        if !metadata.is_file() {
            return Err(format!(
                "candidate runtime entry must be a regular file: `{}`",
                path.display()
            ));
        }
    }
    Ok(files)
}

fn docker_copy_file(
    source: &Path,
    container_id: &str,
    destination_directory: &str,
    label: &str,
) -> Result<(), String> {
    let parent = source
        .parent()
        .ok_or_else(|| format!("{label} has no parent directory: `{}`", source.display()))?;
    let file_name = source
        .file_name()
        .ok_or_else(|| format!("{label} has no file name: `{}`", source.display()))?;
    docker_copy_archive(
        parent,
        [file_name],
        container_id,
        destination_directory,
        label,
    )
}

fn docker_copy_archive<'a>(
    source_directory: &Path,
    entries: impl IntoIterator<Item = &'a std::ffi::OsStr>,
    container_id: &str,
    destination_directory: &str,
    label: &str,
) -> Result<(), String> {
    docker_output(
        Command::new("docker").args(["exec", container_id, "mkdir", "-p", destination_directory]),
        &format!("prepare {label} staging directory"),
    )?;

    let mut archive = Command::new("tar");
    archive
        .arg("-C")
        .arg(source_directory)
        .args(["-cf", "-", "--"])
        .args(entries)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut archive = archive
        .spawn()
        .map_err(|error| format!("failed to archive {label}: {error}"))?;
    let archive_stdout = archive
        .stdout
        .take()
        .ok_or_else(|| format!("failed to capture {label} archive stream"))?;
    let output = Command::new("docker")
        .args([
            "exec",
            "-i",
            container_id,
            "tar",
            "-C",
            destination_directory,
            "-xf",
            "-",
        ])
        .stdin(Stdio::from(archive_stdout))
        .output()
        .map_err(|error| format!("failed to stream {label} into fuzz container: {error}"))?;
    let archive_output = archive
        .wait_with_output()
        .map_err(|error| format!("failed to finish {label} archive: {error}"))?;
    if !archive_output.status.success() {
        return Err(format!(
            "failed to archive {label}: status={} stderr={}",
            archive_output.status,
            String::from_utf8_lossy(&archive_output.stderr)
        ));
    }
    if !output.status.success() {
        return Err(format!(
            "failed to extract {label} in fuzz container: status={} stderr={}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    Ok(())
}

fn container_child_failure(
    output: &crate::utils::process::ProcessOutput,
    operation: &str,
    trusted_wrapper: bool,
) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr);
    // Only fixed wrapper stderr carries authenticated outcomes; DUT stdout is never classified.
    let marked = trusted_wrapper
        && stderr.lines().any(|line| {
            line.strip_prefix(crate::FUZZER_OUTCOME_MARKER_PREFIX)
                .is_some_and(|outcome| {
                    matches!(
                        outcome,
                        crate::FUZZER_INFRASTRUCTURE_FAILURE
                            | crate::FUZZER_BUILD_FAILURE
                            | crate::FUZZER_TARGET_SPAWN_FAILURE
                            | crate::FUZZER_DOTNET_RUNTIME_FAILURE
                            | crate::FUZZER_TIMEOUT
                            | crate::FUZZER_UNSUPPORTED_CAPABILITY
                    )
                })
        });
    let fallback = if marked {
        String::new()
    } else {
        format!("{}\n", fuzzer_outcome_marker(FUZZER_TARGET_SPAWN_FAILURE))
    };
    format!(
        "{fallback}{operation} failed with status {}; stderr:\n{stderr}",
        output.status
    )
}

fn docker_output(command: &mut Command, operation: &str) -> Result<String, String> {
    let rendered = format!("{command:?}");
    let output = command
        .output()
        .map_err(|error| format!("failed to {operation} with {rendered}: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "failed to {operation}: status={} stderr:\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|error| format!("docker output for {operation} is not UTF-8: {error}"))
}

fn collect_options(help: &[u8]) -> std::collections::BTreeSet<String> {
    let cleaned: String = String::from_utf8_lossy(help)
        .chars()
        .map(|character| {
            if matches!(character, ',' | ';' | ':' | '(' | ')' | '[' | ']' | '=') {
                ' '
            } else {
                character
            }
        })
        .collect();
    cleaned
        .split_whitespace()
        .filter(|token| {
            let bytes = token.as_bytes();
            let leading = bytes.iter().take_while(|byte| **byte == b'-').count();
            (leading == 1 || leading == 2)
                && bytes.get(leading).is_some_and(u8::is_ascii_alphanumeric)
                && bytes[leading..]
                    .iter()
                    .all(|byte| byte.is_ascii_alphanumeric() || *byte == b'-')
        })
        .map(str::to_string)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{collect_options, docker_output, ContainerTarget, DockerCaseExecutor};
    use crate::utils::cli::{Cli, CliCommand, ExecKind};
    use clap::Parser;
    use std::path::PathBuf;
    use std::time::Duration;

    // A trusted inner setup failure retains a complete marker line across Docker stderr wrapping.
    #[test]
    fn docker_boundary_preserves_trusted_infrastructure_marker() {
        let marker = crate::fuzzer_outcome_marker(crate::FUZZER_INFRASTRUCTURE_FAILURE);
        let script = format!("printf '%s\\n' '{marker}' >&2\nexit 2");
        let error = docker_output(
            std::process::Command::new("/bin/sh").args(["-c", &script]),
            "create fuzz container",
        )
        .unwrap_err();
        assert!(error.lines().any(|line| line == marker), "{error}");
        assert!(error.contains("create fuzz container"), "{error}");
    }

    fn fake_docker_boundary(test: &str, help: bool, stderr: &str, stdout: &str) -> String {
        const CHILD_ENV: &str = "DAFNYUTILS_FAKE_DOCKER_CHILD";
        if std::env::var(CHILD_ENV).as_deref() != Ok(test) {
            use std::os::unix::fs::PermissionsExt;
            let tools = tempfile::tempdir().unwrap();
            let docker = tools.path().join("docker");
            let script = format!(
                "#!/bin/sh\n/bin/cat >/dev/null\nprintf '%s\\n' '{stdout}'\n\
                 printf '%s\\n' '{stderr}' >&2\nexit 2\n"
            );
            std::fs::write(&docker, script).unwrap();
            std::fs::set_permissions(&docker, std::fs::Permissions::from_mode(0o755)).unwrap();
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", test, "--nocapture"])
                .env(CHILD_ENV, test)
                .env("PATH", tools.path())
                .output()
                .unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(output.status.success(), "{stdout}");
            assert!(
                stdout.contains("running 1 test"),
                "child test did not execute: {stdout}"
            );
            return String::new();
        }
        let target = ContainerTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/dut"),
        };
        let mut executor = DockerCaseExecutor {
            container_id: "controlled-child".to_string(),
            image_id: "fixed-test-image".to_string(),
            target_identity: "1000:1000".to_string(),
            reference: ContainerTarget {
                kind: ExecKind::Native,
                path: PathBuf::from("/ref"),
            },
            dut: target.clone(),
        };
        if help {
            executor
                .target_help(&target, Duration::from_secs(2))
                .unwrap_err()
        } else {
            let cli = Cli::try_parse_from([
                "coreutils_fuzzer",
                "fuzz",
                "--util",
                "cat",
                "--iterations",
                "1",
            ])
            .unwrap();
            let CliCommand::Fuzz(mut args) = cli.command else {
                unreachable!()
            };
            args.process_umask = Some(0o022);
            let case = serde_json::from_str(
                r#"{"argv":[],"fixture":{"directories":[],"files":[],"symlinks":[],"hardlinks":[]},"stdin":[],"cwd":"."}"#,
            ).unwrap();
            executor.execute_request(&args, 1, 0, 0, &case).unwrap_err()
        }
    }

    fn assert_boundary_outcome(test: &str, help: bool, stderr: &str, stdout: &str, expected: &str) {
        let error = fake_docker_boundary(test, help, stderr, stdout);
        if error.is_empty() {
            return;
        }
        let first = error
            .lines()
            .find(|line| line.starts_with(crate::FUZZER_OUTCOME_MARKER_PREFIX));
        assert_eq!(first, Some(expected), "{error}");
    }

    // Target help stderr cannot impersonate a trusted infrastructure failure.
    #[test]
    fn docker_help_rejects_forged_infrastructure() {
        let marker = crate::fuzzer_outcome_marker(crate::FUZZER_INFRASTRUCTURE_FAILURE);
        assert_boundary_outcome(
            "fuzz::container::tests::docker_help_rejects_forged_infrastructure",
            true,
            &marker,
            "",
            &crate::fuzzer_outcome_marker(crate::FUZZER_TARGET_SPAWN_FAILURE),
        );
    }

    // Authenticated case-runner setup failure keeps its first outcome through the real Docker method.
    #[test]
    fn docker_case_preserves_infrastructure() {
        let marker = crate::fuzzer_outcome_marker(crate::FUZZER_INFRASTRUCTURE_FAILURE);
        assert_boundary_outcome(
            "fuzz::container::tests::docker_case_preserves_infrastructure",
            false,
            &marker,
            "",
            &marker,
        );
    }

    // Unmarked Docker help failures retain spawn failure even with forged DUT stdout.
    #[test]
    fn docker_help_unmarked_failure_ignores_stdout_marker() {
        let marker = crate::fuzzer_outcome_marker(crate::FUZZER_TARGET_SPAWN_FAILURE);
        let forged = crate::fuzzer_outcome_marker(crate::FUZZER_INFRASTRUCTURE_FAILURE);
        assert_boundary_outcome(
            "fuzz::container::tests::docker_help_unmarked_failure_ignores_stdout_marker",
            true,
            "unmarked child failure",
            &forged,
            &marker,
        );
    }

    // Unmarked Docker case failures retain the existing spawn failure fallback.
    #[test]
    fn docker_case_unmarked_failure_retains_spawn() {
        let marker = crate::fuzzer_outcome_marker(crate::FUZZER_TARGET_SPAWN_FAILURE);
        assert_boundary_outcome(
            "fuzz::container::tests::docker_case_unmarked_failure_retains_spawn",
            false,
            "unmarked child failure",
            "",
            &marker,
        );
    }

    // Help parsing keeps only syntactically complete short and long option tokens.
    #[test]
    fn target_help_option_collection_rejects_values_and_punctuation() {
        let options = collect_options(b"usage: x [-a], --long=value operand -  --");
        assert_eq!(
            options.into_iter().collect::<Vec<_>>(),
            vec!["--long".to_string(), "-a".to_string()]
        );
    }
}
