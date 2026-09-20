use super::{
    FsNodeSnapshot, FsSnapshot, FsTimes, HostInodeKeySnapshot, ResolvedPaths, ResolvedTarget,
    RunResult, VariantKind,
};
use crate::utils::chmod_campaign::{
    canonical_environment_config, canonical_process_environment, validate_process_umask,
};
use crate::utils::cli::{ChmodExecHelperArgs, ExecKind};
use crate::utils::paths::format_path_error;
use crate::utils::process::{
    run_command_with_timeout_and_input, PreparedProcess, ProcessError, ProcessOutput,
};
use crate::{
    fuzzer_outcome_marker, FUZZER_DOTNET_RUNTIME_FAILURE, FUZZER_TARGET_SPAWN_FAILURE,
    FUZZER_TIMEOUT,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{self, Read, Seek, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

#[cfg(unix)]
use std::os::fd::{AsRawFd, FromRawFd};

pub(crate) const CONTROLLED_FIXTURE_ATIME_SEC: i64 = 4_102_444_800;
pub(crate) const CONTROLLED_FIXTURE_MTIME_SEC: i64 = 2_000_000_000;
pub(crate) const CONTROLLED_FIXTURE_TIME_NSEC: i64 = 0;

#[cfg(unix)]
#[repr(C)]
struct SnapshotTimespec {
    tv_sec: i64,
    tv_nsec: i64,
}

#[cfg(unix)]
unsafe extern "C" {
    fn utimensat(
        dirfd: i32,
        pathname: *const std::os::raw::c_char,
        times: *const SnapshotTimespec,
        flags: i32,
    ) -> i32;
}

#[cfg(unix)]
pub(crate) fn restore_path_times(
    path: &Path,
    times: FsTimes,
    is_symlink: bool,
) -> Result<(), String> {
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;

    const AT_FDCWD: i32 = -100;
    const AT_SYMLINK_NOFOLLOW: i32 = 0x100;
    let display = path.display().to_string();
    let path = CString::new(path.as_os_str().as_bytes()).map_err(|_| {
        format!("filesystem snapshot path contains an unsupported NUL byte: `{display}`")
    })?;
    let values = [
        SnapshotTimespec {
            tv_sec: times.atime_sec,
            tv_nsec: times.atime_nsec,
        },
        SnapshotTimespec {
            tv_sec: times.mtime_sec,
            tv_nsec: times.mtime_nsec,
        },
    ];
    let flags = if is_symlink { AT_SYMLINK_NOFOLLOW } else { 0 };
    let status = unsafe { utimensat(AT_FDCWD, path.as_ptr(), values.as_ptr(), flags) };
    if status == 0 {
        Ok(())
    } else {
        Err(format!(
            "failed to restore snapshot times on `{display}`: {}",
            io::Error::last_os_error()
        ))
    }
}

pub(crate) fn control_chmod_fixture_node(path: &Path, is_symlink: bool) -> Result<(), String> {
    suppress_fixture_atime_updates_for_node(path, is_symlink)?;

    #[cfg(unix)]
    return restore_path_times(
        path,
        FsTimes {
            atime_sec: CONTROLLED_FIXTURE_ATIME_SEC,
            atime_nsec: CONTROLLED_FIXTURE_TIME_NSEC,
            mtime_sec: CONTROLLED_FIXTURE_MTIME_SEC,
            mtime_nsec: CONTROLLED_FIXTURE_TIME_NSEC,
            ctime_sec: 0,
            ctime_nsec: 0,
        },
        is_symlink,
    );
    #[cfg(not(unix))]
    Err(format!(
        "strict chmod fixture control requires Unix timestamp support for `{}`",
        path.display()
    ))
}

pub(crate) fn suppress_fixture_atime_updates_for_node(
    path: &Path,
    is_symlink: bool,
) -> Result<(), String> {
    #[cfg(target_os = "linux")]
    if !is_symlink {
        set_linux_noatime(path)?;
    }
    #[cfg(not(target_os = "linux"))]
    if !is_symlink {
        return Err(format!(
            "strict read fixture control requires Linux FS_NOATIME_FL for `{}`",
            path.display()
        ));
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn set_linux_noatime(path: &Path) -> Result<(), String> {
    use std::fs::OpenOptions;
    use std::os::fd::AsRawFd;
    use std::os::raw::{c_int, c_long, c_ulong};

    const IOC_NRBITS: c_ulong = 8;
    const IOC_TYPEBITS: c_ulong = 8;
    const IOC_SIZEBITS: c_ulong = 14;
    const IOC_NRSHIFT: c_ulong = 0;
    const IOC_TYPESHIFT: c_ulong = IOC_NRSHIFT + IOC_NRBITS;
    const IOC_SIZESHIFT: c_ulong = IOC_TYPESHIFT + IOC_TYPEBITS;
    const IOC_DIRSHIFT: c_ulong = IOC_SIZESHIFT + IOC_SIZEBITS;
    const IOC_WRITE: c_ulong = 1;
    const IOC_READ: c_ulong = 2;
    const FS_IOC_GETFLAGS: c_ulong = (IOC_READ << IOC_DIRSHIFT)
        | ((b'f' as c_ulong) << IOC_TYPESHIFT)
        | (1 << IOC_NRSHIFT)
        | ((std::mem::size_of::<c_long>() as c_ulong) << IOC_SIZESHIFT);
    const FS_IOC_SETFLAGS: c_ulong = (IOC_WRITE << IOC_DIRSHIFT)
        | ((b'f' as c_ulong) << IOC_TYPESHIFT)
        | (2 << IOC_NRSHIFT)
        | ((std::mem::size_of::<c_long>() as c_ulong) << IOC_SIZESHIFT);
    const FS_NOATIME_FL: c_long = 0x0000_0080;

    unsafe extern "C" {
        fn ioctl(fd: c_int, request: c_ulong, argument: *mut c_long) -> c_int;
    }

    let file = OpenOptions::new()
        .read(true)
        .open(path)
        .map_err(|error| format_path_error("open fixture node for FS_NOATIME_FL", path, error))?;
    let mut flags: c_long = 0;
    if unsafe { ioctl(file.as_raw_fd(), FS_IOC_GETFLAGS, &mut flags) } != 0 {
        return Err(format!(
            "failed to read inode flags on `{}`: {}",
            path.display(),
            io::Error::last_os_error()
        ));
    }
    flags |= FS_NOATIME_FL;
    if unsafe { ioctl(file.as_raw_fd(), FS_IOC_SETFLAGS, &mut flags) } != 0 {
        return Err(format!(
            "failed to set FS_NOATIME_FL on `{}`: {}",
            path.display(),
            io::Error::last_os_error()
        ));
    }
    Ok(())
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ControlledUmaskProbe {
    pub(crate) observed_umask: u32,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
    pub(crate) exit_code: i32,
}

pub(crate) fn apply_deterministic_env(cmd: &mut Command) {
    cmd.env_clear();
    for (key, value) in canonical_process_environment() {
        cmd.env(key, value);
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_variant(
    kind: VariantKind,
    paths: &ResolvedPaths,
    argv: &[String],
    stdin: &[u8],
    cwd: &Path,
    root: &Path,
    umask: u32,
    identity: Option<(u32, u32)>,
    timeout: Duration,
) -> Result<RunResult, String> {
    let target = match kind {
        VariantKind::Ref => &paths.reference,
        VariantKind::Dut => &paths.dut,
    };
    run_target(target, argv, stdin, cwd, root, umask, identity, timeout)
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn run_controlled_chmod_variant(
    kind: VariantKind,
    paths: &ResolvedPaths,
    argv: &[String],
    stdin: &[u8],
    cwd: &Path,
    root: &Path,
    env: &BTreeMap<String, String>,
    umask: u32,
    timeout: Duration,
) -> Result<RunResult, String> {
    let target = match kind {
        VariantKind::Ref => &paths.reference,
        VariantKind::Dut => &paths.dut,
    };
    run_controlled_chmod_target(target, argv, stdin, cwd, root, env, umask, timeout)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn prepare_controlled_chmod_variant(
    kind: VariantKind,
    paths: &ResolvedPaths,
    argv: &[String],
    cwd: &Path,
    root: &Path,
    env: &BTreeMap<String, String>,
    umask: u32,
    identity: Option<(u32, u32)>,
) -> Result<PreparedChmodTarget, String> {
    let target = match kind {
        VariantKind::Ref => &paths.reference,
        VariantKind::Dut => &paths.dut,
    };
    prepare_controlled_chmod_target(target, argv, cwd, root, env, umask, identity)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_target(
    target: &ResolvedTarget,
    argv: &[String],
    stdin: &[u8],
    cwd: &Path,
    root: &Path,
    umask: u32,
    identity: Option<(u32, u32)>,
    timeout: Duration,
) -> Result<RunResult, String> {
    let mut cmd = match target.kind {
        ExecKind::Native => {
            let mut c = Command::new(&target.path);
            #[cfg(unix)]
            {
                use std::os::unix::process::CommandExt;
                if let Some(name) = target.path.file_name() {
                    c.arg0(name);
                }
            }
            c.args(argv);
            c
        }
        ExecKind::DotnetDll => {
            let mut c = Command::new("dotnet");
            c.arg(&target.path).args(argv);
            c
        }
    };
    cmd.current_dir(root.join(cwd));
    apply_deterministic_env(&mut cmd);
    apply_process_umask(&mut cmd, umask)?;
    apply_process_identity(&mut cmd, identity)?;

    let output = run_command_with_timeout_and_input(&mut cmd, stdin, timeout)
        .map_err(|err| format_target_process_error(target, argv, cwd, timeout, err))?;

    Ok(RunResult {
        termination: super::process_outcome::Termination::from_status(output.status),
        stdout: output.stdout,
        stderr: output.stderr,
    })
}

fn apply_process_umask(command: &mut Command, requested_umask: u32) -> Result<(), String> {
    validate_process_umask(requested_umask)?;
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;

        unsafe extern "C" {
            fn umask(mask: u32) -> u32;
        }
        unsafe {
            command.pre_exec(move || {
                umask(requested_umask);
                Ok(())
            });
        }
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let _ = requested_umask;
        Err("controlled child umask requires Unix".to_string())
    }
}

fn apply_process_identity(
    command: &mut Command,
    identity: Option<(u32, u32)>,
) -> Result<(), String> {
    let Some((uid, gid)) = identity else {
        return Ok(());
    };
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;

        unsafe extern "C" {
            fn setgroups(size: usize, groups: *const u32) -> i32;
            fn setgid(gid: u32) -> i32;
            fn setuid(uid: u32) -> i32;
        }
        unsafe {
            command.pre_exec(move || {
                if setgroups(0, std::ptr::null()) != 0 {
                    return Err(io::Error::last_os_error());
                }
                if setgid(gid) != 0 {
                    return Err(io::Error::last_os_error());
                }
                if setuid(uid) != 0 {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            });
        }
        Ok(())
    }
    #[cfg(not(unix))]
    {
        let _ = (command, uid, gid);
        Err("numeric process identity requires Unix".to_string())
    }
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn run_controlled_chmod_target(
    target: &ResolvedTarget,
    argv: &[String],
    stdin: &[u8],
    cwd: &Path,
    root: &Path,
    env: &BTreeMap<String, String>,
    umask: u32,
    timeout: Duration,
) -> Result<RunResult, String> {
    prepare_controlled_chmod_target(target, argv, cwd, root, env, umask, None)?
        .go_and_collect(stdin, timeout)
}

pub(crate) struct PreparedChmodTarget {
    target: ResolvedTarget,
    argv: Vec<String>,
    cwd: PathBuf,
    #[cfg(unix)]
    go: Option<File>,
    #[cfg(unix)]
    status: File,
    process: PreparedProcess,
}

impl PreparedChmodTarget {
    pub(crate) fn go_and_collect(
        mut self,
        stdin: &[u8],
        timeout: Duration,
    ) -> Result<RunResult, String> {
        #[cfg(unix)]
        {
            let started = Instant::now();
            self.go
                .as_mut()
                .expect("live GO writer")
                .write_all(b"GO")
                .map_err(|error| self.phase_error("send GO", error))?;
            self.go.take();
            let exec_error =
                read_exec_status(&mut self.status, remaining_timeout(started, timeout))
                    .map_err(|error| self.phase_error("read exec status", error))?;
            let remaining = remaining_timeout(started, timeout);
            if let Some(error) = exec_error {
                let output = self
                    .process
                    .collect(&[], remaining)
                    .map_err(|process_error| {
                        format_target_process_error(
                            &self.target,
                            &self.argv,
                            &self.cwd,
                            timeout,
                            process_error,
                        )
                    })?;
                return Err(format!(
                    "failed to exec {} variant argv={:?} cwd=`{}`:\n{error}\nstdout={:?} stderr={:?}",
                    self.target.label,
                    self.argv,
                    self.cwd.display(),
                    output.stdout,
                    output.stderr
                ));
            }
            let output = self
                .process
                .collect(stdin, remaining)
                .map_err(|process_error| {
                    format_target_process_error(
                        &self.target,
                        &self.argv,
                        &self.cwd,
                        timeout,
                        process_error,
                    )
                })?;
            Ok(run_result(output))
        }
        #[cfg(not(unix))]
        {
            let _ = (stdin, timeout);
            Err("controlled chmod helper requires Unix".to_string())
        }
    }

    fn phase_error(&self, phase: &str, error: io::Error) -> String {
        format!(
            "failed to {phase} for {} variant argv={:?} cwd=`{}`: {error}",
            self.target.label,
            self.argv,
            self.cwd.display()
        )
    }
}

fn run_result(output: ProcessOutput) -> RunResult {
    RunResult {
        termination: super::process_outcome::Termination::from_status(output.status),
        stdout: output.stdout,
        stderr: output.stderr,
    }
}

fn remaining_timeout(started: Instant, timeout: Duration) -> Duration {
    timeout.saturating_sub(started.elapsed())
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn prepare_controlled_chmod_target(
    target: &ResolvedTarget,
    argv: &[String],
    cwd: &Path,
    root: &Path,
    env: &BTreeMap<String, String>,
    umask: u32,
    identity: Option<(u32, u32)>,
) -> Result<PreparedChmodTarget, String> {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;

        const READY_TIMEOUT: Duration = Duration::from_secs(10);
        let (mut parent_ready, child_ready) = pipe_cloexec()
            .map_err(|error| format!("failed to create chmod READY channel: {error}"))?;
        let (child_go, parent_go) = pipe_cloexec()
            .map_err(|error| format!("failed to create chmod GO channel: {error}"))?;
        let (parent_status, child_status) = pipe_cloexec()
            .map_err(|error| format!("failed to create chmod status channel: {error}"))?;
        let ready_fd = child_ready.as_raw_fd();
        let go_fd = child_go.as_raw_fd();
        let status_fd = child_status.as_raw_fd();
        let mut command = Command::new(helper_executable()?);
        command
            .arg("__chmod-exec-helper")
            .arg("--exec-kind")
            .arg(match target.kind {
                ExecKind::Native => "native",
                ExecKind::DotnetDll => "dotnet-dll",
            })
            .arg("--target")
            .arg(&target.path)
            .arg("--native-argv0")
            .arg("chmod")
            .arg("--ready-fd")
            .arg(ready_fd.to_string())
            .arg("--go-fd")
            .arg(go_fd.to_string())
            .arg("--status-fd")
            .arg(status_fd.to_string());
        if let Some((uid, gid)) = identity {
            command
                .arg("--target-uid")
                .arg(uid.to_string())
                .arg("--target-gid")
                .arg(gid.to_string());
        }
        command.arg("--").args(argv);
        command.current_dir(root.join(cwd));
        configure_controlled_child(&mut command, env, umask)?;
        unsafe {
            command.pre_exec(move || {
                set_cloexec_io(ready_fd, false)?;
                set_cloexec_io(go_fd, false)?;
                set_cloexec_io(status_fd, false)?;
                Ok(())
            });
        }
        let process = PreparedProcess::spawn(&mut command).map_err(|error| {
            format_target_process_error(target, argv, cwd, READY_TIMEOUT, error)
        })?;
        drop(child_ready);
        drop(child_go);
        drop(child_status);
        let ready = read_to_end_bounded(&mut parent_ready, READY_TIMEOUT).map_err(|error| {
            format!(
                "failed to receive READY for {} variant argv={argv:?} cwd=`{}`: {error}",
                target.label,
                cwd.display()
            )
        })?;
        if ready != b"READY" {
            return Err(format!(
                "malformed READY for {} variant argv={argv:?} cwd=`{}`: {ready:?}",
                target.label,
                cwd.display()
            ));
        }
        Ok(PreparedChmodTarget {
            target: target.clone(),
            argv: argv.to_vec(),
            cwd: cwd.to_path_buf(),
            go: Some(parent_go),
            status: parent_status,
            process,
        })
    }
    #[cfg(not(unix))]
    {
        let _ = (target, argv, cwd, root, env, umask, identity);
        Err("controlled chmod helper requires Unix".to_string())
    }
}

#[cfg(test)]
pub(crate) fn run_controlled_umask_probe(
    env: &BTreeMap<String, String>,
    umask: u32,
    cwd: &Path,
) -> Result<ControlledUmaskProbe, String> {
    let mut command = Command::new("/bin/sh");
    command.arg("-c").arg("umask").current_dir(cwd);
    configure_controlled_child(&mut command, env, umask)?;
    let output = run_command_with_timeout_and_input(&mut command, &[], Duration::from_secs(10))
        .map_err(|err| format!("controlled umask probe failed: {err:?}"))?;
    let termination = super::process_outcome::Termination::from_status(output.status);
    let exit_code = termination
        .exit_code()
        .ok_or_else(|| format!("controlled umask probe terminated by signal: {termination:?}"))?;
    if exit_code != 0 || !output.stderr.is_empty() {
        return Err(format!(
            "controlled umask probe rejected: exit={exit_code} stderr={:?}",
            output.stderr
        ));
    }
    let text = std::str::from_utf8(&output.stdout)
        .map_err(|err| format!("controlled umask probe output is not UTF-8: {err}"))?;
    let digits = text.trim();
    let observed_umask = u32::from_str_radix(digits, 8)
        .map_err(|_| format!("controlled umask probe returned invalid octal `{digits}`"))?;
    Ok(ControlledUmaskProbe {
        observed_umask,
        stdout: output.stdout,
        stderr: output.stderr,
        exit_code,
    })
}

fn configure_controlled_child(
    command: &mut Command,
    env: &BTreeMap<String, String>,
    requested_umask: u32,
) -> Result<(), String> {
    let expected = canonical_environment_config(requested_umask)?;
    if env != &expected {
        return Err("controlled chmod environment is not canonical".to_string());
    }
    command.env_clear();
    for (key, value) in env {
        command.env(key, value);
    }
    apply_process_umask(command, requested_umask)
}

#[cfg(unix)]
fn helper_executable() -> Result<PathBuf, String> {
    #[cfg(test)]
    {
        use std::sync::OnceLock;

        static HELPER: OnceLock<Result<PathBuf, String>> = OnceLock::new();
        HELPER
            .get_or_init(|| {
                let manifest = Path::new(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
                let status = Command::new("cargo")
                    .arg("build")
                    .arg("--quiet")
                    .arg("--manifest-path")
                    .arg(&manifest)
                    .arg("--bin")
                    .arg("coreutils_fuzzer")
                    .status()
                    .map_err(|error| format!("failed to build chmod helper executable: {error}"))?;
                if !status.success() {
                    return Err(format!(
                        "failed to build chmod helper executable: status {:?}",
                        status.code()
                    ));
                }
                Ok(Path::new(env!("CARGO_MANIFEST_DIR")).join("target/debug/coreutils_fuzzer"))
            })
            .clone()
    }
    #[cfg(not(test))]
    std::env::current_exe()
        .map_err(|error| format!("failed to resolve chmod helper executable: {error}"))
}

#[cfg(unix)]
pub(super) fn pipe_cloexec() -> io::Result<(File, File)> {
    #[cfg(target_os = "linux")]
    {
        const O_CLOEXEC: i32 = 0o2_000_000;
        unsafe extern "C" {
            fn pipe2(fds: *mut i32, flags: i32) -> i32;
        }

        let mut fds = [-1, -1];
        if unsafe { pipe2(fds.as_mut_ptr(), O_CLOEXEC) } < 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(unsafe { (File::from_raw_fd(fds[0]), File::from_raw_fd(fds[1])) })
    }
    #[cfg(not(target_os = "linux"))]
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "controlled chmod helper requires Linux close-on-exec pipes",
    ))
}

#[cfg(unix)]
pub(super) fn set_cloexec_io(fd: i32, enabled: bool) -> io::Result<()> {
    const F_GETFD: i32 = 1;
    const F_SETFD: i32 = 2;
    const FD_CLOEXEC: i32 = 1;
    unsafe extern "C" {
        fn fcntl(fd: i32, command: i32, ...) -> i32;
    }

    let flags = unsafe { fcntl(fd, F_GETFD) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    let updated = if enabled {
        flags | FD_CLOEXEC
    } else {
        flags & !FD_CLOEXEC
    };
    if unsafe { fcntl(fd, F_SETFD, updated) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn set_nonblocking(fd: i32, enabled: bool) -> io::Result<i32> {
    const F_GETFL: i32 = 3;
    const O_NONBLOCK: i32 = 0o4_000;
    let flags = get_file_status_flags(fd, F_GETFL)?;
    set_file_status_flags(
        fd,
        if enabled {
            flags | O_NONBLOCK
        } else {
            flags & !O_NONBLOCK
        },
    )?;
    Ok(flags)
}

#[cfg(not(target_os = "linux"))]
fn set_nonblocking(_fd: i32, _enabled: bool) -> io::Result<i32> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "controlled chmod helper requires Linux nonblocking pipes",
    ))
}

#[cfg(target_os = "linux")]
fn get_file_status_flags(fd: i32, command: i32) -> io::Result<i32> {
    unsafe extern "C" {
        fn fcntl(fd: i32, command: i32, ...) -> i32;
    }

    let flags = unsafe { fcntl(fd, command) };
    if flags < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(flags)
    }
}

#[cfg(target_os = "linux")]
fn set_file_status_flags(fd: i32, flags: i32) -> io::Result<()> {
    const F_SETFL: i32 = 4;
    unsafe extern "C" {
        fn fcntl(fd: i32, command: i32, ...) -> i32;
    }

    if unsafe { fcntl(fd, F_SETFL, flags) } < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

#[cfg(not(target_os = "linux"))]
fn set_file_status_flags(_fd: i32, _flags: i32) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "controlled chmod helper requires Linux nonblocking pipes",
    ))
}

#[cfg(unix)]
fn read_exec_status(status: &mut File, timeout: Duration) -> io::Result<Option<String>> {
    let frame = read_to_end_bounded(status, timeout)?;
    if frame.is_empty() {
        return Ok(None);
    }
    if frame.len() < 4 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "truncated exec status frame",
        ));
    }
    let mut length = [0_u8; 4];
    length.copy_from_slice(&frame[..4]);
    let length = u32::from_be_bytes(length) as usize;
    if length > 1024 * 1024 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "exec status frame is too large",
        ));
    }
    if frame.len() != length + 4 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "malformed exec status frame length",
        ));
    }
    Ok(Some(String::from_utf8_lossy(&frame[4..]).into_owned()))
}

#[cfg(unix)]
fn read_to_end_bounded(stream: &mut File, timeout: Duration) -> io::Result<Vec<u8>> {
    if timeout.is_zero() {
        return Err(io::Error::new(io::ErrorKind::TimedOut, "channel timed out"));
    }
    let flags = set_nonblocking(stream.as_raw_fd(), true)?;
    let deadline = Instant::now() + timeout;
    let mut bytes = Vec::new();
    loop {
        match stream.read_to_end(&mut bytes) {
            Ok(_) => {
                set_file_status_flags(stream.as_raw_fd(), flags)?;
                return Ok(bytes);
            }
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                if Instant::now() >= deadline {
                    set_file_status_flags(stream.as_raw_fd(), flags)?;
                    return Err(io::Error::new(io::ErrorKind::TimedOut, "channel timed out"));
                }
                std::thread::sleep(Duration::from_millis(1));
            }
            Err(error) => return Err(error),
        }
    }
}

#[cfg(unix)]
fn write_exec_error(status: &mut File, message: &str) -> io::Result<()> {
    let bytes = message.as_bytes();
    let length = u32::try_from(bytes.len())
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "exec error is too large"))?;
    status.write_all(&length.to_be_bytes())?;
    status.write_all(bytes)
}

#[cfg(unix)]
pub(crate) fn run_chmod_exec_helper(args: ChmodExecHelperArgs) -> ! {
    use std::os::unix::process::CommandExt;

    let mut ready = unsafe { File::from_raw_fd(args.ready_fd) };
    let mut go_reader = unsafe { File::from_raw_fd(args.go_fd) };
    let mut status = unsafe { File::from_raw_fd(args.status_fd) };
    let fail = |status: &mut File, message: String| -> ! {
        let _ = write_exec_error(status, &message);
        std::process::exit(127);
    };
    if let Err(error) = set_cloexec_io(args.status_fd, true) {
        fail(
            &mut status,
            format!("failed to restore exec-status close-on-exec: {error}"),
        );
    }
    if let Err(error) = ready.write_all(b"READY") {
        fail(&mut status, format!("failed to send READY: {error}"));
    }
    drop(ready);
    let mut go = Vec::new();
    if let Err(error) = go_reader.read_to_end(&mut go) {
        fail(&mut status, format!("failed to receive GO: {error}"));
    }
    if go != b"GO" {
        fail(&mut status, format!("malformed GO: {go:?}"));
    }
    drop(go_reader);

    let mut command = match args.exec_kind {
        ExecKind::Native => {
            let mut command = Command::new(&args.target);
            command.arg0(&args.native_argv0).args(&args.argv);
            command
        }
        ExecKind::DotnetDll => {
            let mut command = Command::new("dotnet");
            command.arg(&args.target).args(&args.argv);
            command
        }
    };
    if let (Some(uid), Some(gid)) = (args.target_uid, args.target_gid) {
        if let Err(error) = set_current_process_identity(uid, gid) {
            fail(&mut status, error);
        }
    }
    let error = command.exec();
    fail(&mut status, error.to_string())
}

#[cfg(unix)]
fn set_current_process_identity(uid: u32, gid: u32) -> Result<(), String> {
    unsafe extern "C" {
        fn setgroups(size: usize, groups: *const u32) -> i32;
        fn setgid(gid: u32) -> i32;
        fn setuid(uid: u32) -> i32;
    }
    if unsafe { setgroups(0, std::ptr::null()) } != 0 {
        return Err(format!(
            "failed to clear supplementary groups: {}",
            io::Error::last_os_error()
        ));
    }
    if unsafe { setgid(gid) } != 0 {
        return Err(format!(
            "failed to set target gid {gid}: {}",
            io::Error::last_os_error()
        ));
    }
    if unsafe { setuid(uid) } != 0 {
        return Err(format!(
            "failed to set target uid {uid}: {}",
            io::Error::last_os_error()
        ));
    }
    Ok(())
}

#[cfg(not(unix))]
pub(crate) fn run_chmod_exec_helper(_args: ChmodExecHelperArgs) -> ! {
    eprintln!("controlled chmod helper requires Unix");
    std::process::exit(127)
}

fn format_target_process_error(
    target: &ResolvedTarget,
    argv: &[String],
    cwd: &Path,
    timeout: Duration,
    err: ProcessError,
) -> String {
    let context = format!(
        "{} variant argv={argv:?} cwd=`{}`",
        target.label,
        cwd.display()
    );
    let outcome = if matches!(&err, ProcessError::Timeout) {
        FUZZER_TIMEOUT
    } else if target.kind == ExecKind::DotnetDll {
        FUZZER_DOTNET_RUNTIME_FAILURE
    } else {
        FUZZER_TARGET_SPAWN_FAILURE
    };
    let message = match err {
        ProcessError::Spawn(message) => format!("failed to run {context}: {message}"),
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StdinUnavailable => format!("stdin pipe unavailable for {context}"),
        ProcessError::StdinWrite(message) => {
            format!("failed to write stdin for {context}: {message}")
        }
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StdinThreadPanic => format!("stdin writer thread panicked for {context}"),
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StdoutUnavailable => format!("stdout pipe unavailable for {context}"),
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StderrUnavailable => format!("stderr pipe unavailable for {context}"),
        ProcessError::StdoutRead(message) => {
            format!("failed to read stdout for {context}: {message}")
        }
        ProcessError::StderrRead(message) => {
            format!("failed to read stderr for {context}: {message}")
        }
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StdoutThreadPanic => format!("stdout reader thread panicked for {context}"),
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        ProcessError::StderrThreadPanic => format!("stderr reader thread panicked for {context}"),
        ProcessError::Wait(message) => format!("failed while waiting for {context}: {message}"),
        ProcessError::Timeout => format!("{context} timed out after {timeout:?}"),
        ProcessError::InvalidTimeout => {
            format!("timeout for {context} exceeds the platform clock range")
        }
        ProcessError::Channel { name, message } => {
            format!("{name} channel failed for {context}: {message}")
        }
    };
    format!("{}\n{message}", fuzzer_outcome_marker(outcome))
}

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
#[allow(deprecated)] // The convenience block-size getter is unsigned; this ABI field is signed.
fn raw_stat_metadata_from_metadata(
    metadata: &fs::Metadata,
) -> crate::utils::world_json::RawStatMetadataJson {
    use std::os::linux::fs::MetadataExt;
    let raw = metadata.as_raw_stat();
    let device_number: u64 = raw.st_rdev;
    let io_block_bytes: i64 = raw.st_blksize;
    crate::utils::world_json::RawStatMetadataJson::Known {
        device_number,
        io_block_bytes,
    }
}

#[cfg(not(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu")))]
fn raw_stat_metadata_from_metadata(
    _metadata: &fs::Metadata,
) -> crate::utils::world_json::RawStatMetadataJson {
    crate::utils::world_json::RawStatMetadataJson::Unknown
}

#[cfg(test)]
pub(crate) fn snapshot_fs(root: &Path) -> Result<FsSnapshot, String> {
    snapshot_fs_checked(root).map_err(|error| error.to_string())
}

#[cfg(test)]
pub(crate) fn snapshot_fs_without_restore(root: &Path) -> Result<FsSnapshot, String> {
    snapshot_fs_with_observer_restore(root, false, None, false).map_err(|error| error.to_string())
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum FsCaptureError {
    Encoding { field: &'static str },
    Other(String),
}

impl std::fmt::Display for FsCaptureError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Encoding { field } => {
                write!(formatter, "filesystem snapshot {field} is not UTF-8")
            }
            Self::Other(message) => formatter.write_str(message),
        }
    }
}

impl From<String> for FsCaptureError {
    fn from(message: String) -> Self {
        Self::Other(message)
    }
}

#[cfg(test)]
pub(crate) fn snapshot_fs_checked(root: &Path) -> Result<FsSnapshot, FsCaptureError> {
    snapshot_fs_with_observer_restore(root, true, None, false)
}

struct ChmodFileHandle {
    file: fs::File,
    #[cfg(unix)]
    dev: u64,
    #[cfg(unix)]
    ino: u64,
}

pub(crate) type IdentityTransitionEvidence = BTreeSet<(String, String)>;

struct IdentityHandle {
    file: fs::File,
    pre_paths: Vec<String>,
}

#[derive(Default)]
pub(crate) struct ChmodSnapshotObserver {
    files: BTreeMap<HostInodeKeySnapshot, ChmodFileHandle>,
    identities: BTreeMap<HostInodeKeySnapshot, IdentityHandle>,
}

pub(crate) fn chmod_snapshot_pre(
    root: &Path,
) -> Result<(FsSnapshot, ChmodSnapshotObserver), String> {
    let mut observer = ChmodSnapshotObserver::default();
    let snapshot = snapshot_fs_with_observer_restore(root, false, Some(&mut observer), true)
        .map_err(|error| error.to_string())?;
    Ok((snapshot, observer))
}

pub(crate) fn chmod_snapshot_post(
    root: &Path,
    observer: &mut ChmodSnapshotObserver,
) -> Result<(FsSnapshot, IdentityTransitionEvidence), String> {
    snapshot_fs_post_with_restore(root, observer, false)
}

pub(crate) fn snapshot_fs_pre(root: &Path) -> Result<(FsSnapshot, ChmodSnapshotObserver), String> {
    snapshot_fs_pre_checked(root).map_err(|error| error.to_string())
}

pub(crate) fn snapshot_fs_pre_checked(
    root: &Path,
) -> Result<(FsSnapshot, ChmodSnapshotObserver), FsCaptureError> {
    let mut observer = ChmodSnapshotObserver::default();
    let snapshot = snapshot_fs_with_observer_restore(root, true, Some(&mut observer), true)?;
    Ok((snapshot, observer))
}

pub(crate) fn snapshot_fs_post(
    root: &Path,
    observer: &mut ChmodSnapshotObserver,
) -> Result<(FsSnapshot, IdentityTransitionEvidence), String> {
    snapshot_fs_post_checked(root, observer).map_err(|error| error.to_string())
}

pub(crate) fn snapshot_fs_post_checked(
    root: &Path,
    observer: &mut ChmodSnapshotObserver,
) -> Result<(FsSnapshot, IdentityTransitionEvidence), FsCaptureError> {
    // This is the terminal observation for an iteration. Avoid restoring atime here:
    // utimensat would itself advance ctime and obscure whether the utility changed it.
    snapshot_fs_post_with_restore_checked(root, observer, false)
}

fn snapshot_fs_post_with_restore(
    root: &Path,
    observer: &mut ChmodSnapshotObserver,
    restore_observer_times: bool,
) -> Result<(FsSnapshot, IdentityTransitionEvidence), String> {
    snapshot_fs_post_with_restore_checked(root, observer, restore_observer_times)
        .map_err(|error| error.to_string())
}

fn snapshot_fs_post_with_restore_checked(
    root: &Path,
    observer: &mut ChmodSnapshotObserver,
    restore_observer_times: bool,
) -> Result<(FsSnapshot, IdentityTransitionEvidence), FsCaptureError> {
    let snapshot =
        snapshot_fs_with_observer_restore(root, restore_observer_times, Some(observer), false)?;
    let evidence =
        identity_transition_evidence(observer, &snapshot).map_err(FsCaptureError::from)?;
    Ok((snapshot, evidence))
}

#[cfg(target_os = "linux")]
fn observe_identity(
    observer: &mut ChmodSnapshotObserver,
    path: &Path,
    relative_path: &str,
    expected_key: HostInodeKeySnapshot,
) -> Result<(), String> {
    use std::ffi::CString;
    use std::os::raw::{c_char, c_int};
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::MetadataExt;

    if let Some(handle) = observer.identities.get_mut(&expected_key) {
        handle.pre_paths.push(relative_path.to_string());
        return Ok(());
    }

    unsafe extern "C" {
        fn open(pathname: *const c_char, flags: c_int, ...) -> c_int;
    }
    const O_NOFOLLOW: i32 = 0o400_000;
    const O_CLOEXEC: i32 = 0o2_000_000;
    const O_PATH: i32 = 0o10_000_000;
    let raw_path = CString::new(path.as_os_str().as_bytes()).map_err(|_| {
        format!(
            "filesystem identity path contains an unsupported NUL byte: `{}`",
            path.display()
        )
    })?;
    let descriptor = unsafe { open(raw_path.as_ptr(), O_PATH | O_NOFOLLOW | O_CLOEXEC) };
    if descriptor < 0 {
        return Err(format_path_error(
            "open identity handle",
            path,
            io::Error::last_os_error(),
        ));
    }
    let file = unsafe { File::from_raw_fd(descriptor) };
    let metadata = file
        .metadata()
        .map_err(|error| format_path_error("read identity handle metadata", path, error))?;
    let actual_key = HostInodeKeySnapshot {
        device: metadata.dev(),
        inode: metadata.ino(),
    };
    if actual_key != expected_key {
        return Err(format!(
            "filesystem node changed while opening identity handle `{}`",
            path.display()
        ));
    }
    observer.identities.insert(
        expected_key,
        IdentityHandle {
            file,
            pre_paths: vec![relative_path.to_string()],
        },
    );
    Ok(())
}

#[cfg(not(target_os = "linux"))]
fn observe_identity(
    _observer: &mut ChmodSnapshotObserver,
    path: &Path,
    _relative_path: &str,
    _expected_key: HostInodeKeySnapshot,
) -> Result<(), String> {
    Err(format!(
        "filesystem identity transition observation requires Linux O_PATH for `{}`",
        path.display()
    ))
}

fn identity_transition_evidence(
    observer: &ChmodSnapshotObserver,
    post: &FsSnapshot,
) -> Result<IdentityTransitionEvidence, String> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;

        let mut post_paths = BTreeMap::<HostInodeKeySnapshot, Vec<&String>>::new();
        for (path, node) in post {
            let key = node
                .host_key
                .ok_or_else(|| format!("fs.identity unsupported: post-state path `{path}`"))?;
            post_paths.entry(key).or_default().push(path);
        }

        let mut evidence = BTreeSet::new();
        for (expected_key, handle) in &observer.identities {
            let metadata = handle.file.metadata().map_err(|error| {
                format!("failed to read retained identity handle metadata: {error}")
            })?;
            let retained_key = HostInodeKeySnapshot {
                device: metadata.dev(),
                inode: metadata.ino(),
            };
            if retained_key != *expected_key {
                return Err("retained filesystem identity changed unexpectedly".to_string());
            }
            if let Some(paths) = post_paths.get(&retained_key) {
                for pre_path in &handle.pre_paths {
                    for post_path in paths {
                        evidence.insert((pre_path.clone(), (*post_path).clone()));
                    }
                }
            }
        }
        Ok(evidence)
    }
    #[cfg(not(unix))]
    {
        let _ = (observer, post);
        Err("filesystem identity transition observation requires Unix metadata".to_string())
    }
}

fn open_chmod_file(path: &Path) -> Result<ChmodFileHandle, String> {
    let file = fs::File::open(path).map_err(|error| format_path_error("read file", path, error))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;

        let path_metadata = fs::symlink_metadata(path)
            .map_err(|error| format_path_error("read metadata", path, error))?;
        let handle_metadata = file
            .metadata()
            .map_err(|error| format_path_error("read file metadata", path, error))?;
        if !path_metadata.is_file()
            || (path_metadata.dev(), path_metadata.ino())
                != (handle_metadata.dev(), handle_metadata.ino())
        {
            return Err(format!(
                "filesystem node changed while opening `{}`",
                path.display()
            ));
        }
        Ok(ChmodFileHandle {
            file,
            dev: handle_metadata.dev(),
            ino: handle_metadata.ino(),
        })
    }
    #[cfg(not(unix))]
    {
        let _ = file;
        Err("chmod snapshot observer requires Unix filesystem identity".to_string())
    }
}

fn chmod_handle_matches(handle: &ChmodFileHandle, metadata: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;

        (handle.dev, handle.ino) == (metadata.dev(), metadata.ino())
    }
    #[cfg(not(unix))]
    {
        let _ = (handle, metadata);
        false
    }
}

fn read_chmod_handle(handle: &mut ChmodFileHandle, path: &Path) -> Result<Vec<u8>, String> {
    handle
        .file
        .rewind()
        .map_err(|error| format_path_error("read file", path, error))?;
    let mut data = Vec::new();
    handle
        .file
        .read_to_end(&mut data)
        .map_err(|error| format_path_error("read file", path, error))?;
    Ok(data)
}

fn snapshot_fs_with_observer_restore(
    root: &Path,
    restore_observer_times: bool,
    observer: Option<&mut ChmodSnapshotObserver>,
    capture_handles: bool,
) -> Result<FsSnapshot, FsCaptureError> {
    fn utf8_field(value: &std::ffi::OsStr, field: &'static str) -> Result<String, FsCaptureError> {
        value
            .to_str()
            .map(str::to_owned)
            .ok_or(FsCaptureError::Encoding { field })
    }

    fn record_inaccessible(
        out: &mut FsSnapshot,
        rel: String,
        host_key: Option<HostInodeKeySnapshot>,
    ) {
        out.insert(
            rel,
            FsNodeSnapshot {
                raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
                kind: "inaccessible".to_string(),
                mode_octal: String::new(),
                times: FsTimes::default(),
                uid: None,
                gid: None,
                logical_size: None,
                allocated_512_blocks: None,
                preferred_io_block_bytes: None,
                target: String::new(),
                data: Vec::new(),
                host_key,
                link_count: None,
            },
        );
    }

    fn walk(
        base: &Path,
        current: &Path,
        out: &mut FsSnapshot,
        restore_observer_times: bool,
        observer: &mut Option<&mut ChmodSnapshotObserver>,
        capture_handles: bool,
    ) -> Result<(), FsCaptureError> {
        let rel = if current == base {
            ".".to_string()
        } else {
            let relative = current
                .strip_prefix(base)
                .map_err(|e| format!("failed to relativize `{}`: {e}", current.display()))?;
            utf8_field(relative.as_os_str(), "relative path")?
        };

        let metadata = match fs::symlink_metadata(current) {
            Ok(meta) => meta,
            Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {
                record_inaccessible(out, rel, None);
                return Ok(());
            }
            Err(e) => return Err(format_path_error("read metadata", current, e).into()),
        };
        #[cfg(unix)]
        let host_key = {
            use std::os::unix::fs::MetadataExt;
            Some(HostInodeKeySnapshot {
                device: metadata.dev(),
                inode: metadata.ino(),
            })
        };
        #[cfg(not(unix))]
        let host_key = None;
        if capture_handles {
            let key = host_key.ok_or_else(|| {
                format!(
                    "filesystem identity transition observation is unsupported for `{}`",
                    current.display()
                )
            })?;
            let observer = observer
                .as_deref_mut()
                .ok_or_else(|| "filesystem identity transition observer is missing".to_string())?;
            observe_identity(observer, current, &rel, key)?;
        }
        let file_type = metadata.file_type();

        let (kind, target, data) = if file_type.is_symlink() {
            let target = match fs::read_link(current) {
                Ok(target) => utf8_field(target.as_os_str(), "symlink target")?,
                Err(e) => return Err(format_path_error("read symlink", current, e).into()),
            };
            ("symlink", target, Vec::new())
        } else if file_type.is_dir() {
            let entries = match fs::read_dir(current) {
                Ok(entries) => entries,
                Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {
                    record_inaccessible(out, rel, host_key);
                    return Ok(());
                }
                Err(e) => return Err(format_path_error("read directory", current, e).into()),
            };
            let mut children = Vec::new();
            for entry in entries {
                match entry {
                    Ok(entry) => children.push(entry.path()),
                    Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {
                        record_inaccessible(out, rel, host_key);
                        return Ok(());
                    }
                    Err(e) => {
                        return Err(format_path_error("read directory entry", current, e).into())
                    }
                }
            }
            children.sort();
            for child in children {
                walk(
                    base,
                    &child,
                    out,
                    restore_observer_times,
                    observer,
                    capture_handles,
                )?;
            }
            ("dir", String::new(), Vec::new())
        } else if file_type.is_file() {
            let data = match observer.as_deref_mut() {
                Some(observer) if capture_handles => {
                    let key = host_key.ok_or_else(|| {
                        format!(
                            "filesystem file identity is unsupported for `{}`",
                            current.display()
                        )
                    })?;
                    match observer.files.get_mut(&key) {
                        Some(handle) => read_chmod_handle(handle, current)?,
                        None => {
                            let mut handle = open_chmod_file(current)?;
                            let data = read_chmod_handle(&mut handle, current)?;
                            observer.files.insert(key, handle);
                            data
                        }
                    }
                }
                Some(observer) => match host_key.and_then(|key| observer.files.get_mut(&key)) {
                    Some(handle) if chmod_handle_matches(handle, &metadata) => {
                        read_chmod_handle(handle, current)?
                    }
                    _ => fs::read(current)
                        .map_err(|error| format_path_error("read file", current, error))?,
                },
                None => fs::read(current)
                    .map_err(|error| format_path_error("read file", current, error))?,
            };
            ("file", String::new(), data)
        } else {
            return Err(format!("unsupported filesystem node `{}`", current.display()).into());
        };
        let original_times = times_from_metadata(&metadata);
        #[cfg(unix)]
        let (uid, gid, logical_size, allocated_512_blocks, preferred_io_block_bytes) = {
            use std::os::unix::fs::MetadataExt;
            (
                Some(metadata.uid()),
                Some(metadata.gid()),
                Some(metadata.size()),
                Some(metadata.blocks()),
                Some(metadata.blksize()),
            )
        };
        #[cfg(not(unix))]
        let (uid, gid, logical_size, allocated_512_blocks, preferred_io_block_bytes) =
            (None, None, None, None, None);
        #[cfg(unix)]
        let link_count = {
            use std::os::unix::fs::MetadataExt;
            Some(metadata.nlink())
        };
        #[cfg(not(unix))]
        let link_count = None;
        #[cfg(unix)]
        if restore_observer_times {
            restore_path_times(current, original_times, file_type.is_symlink())?;
        }
        out.insert(
            rel,
            FsNodeSnapshot {
                raw_stat_metadata: raw_stat_metadata_from_metadata(&metadata),
                kind: kind.to_string(),
                mode_octal: mode_octal_string_from_metadata(&metadata),
                times: original_times,
                uid,
                gid,
                logical_size,
                allocated_512_blocks,
                preferred_io_block_bytes,
                target,
                data,
                host_key,
                link_count,
            },
        );

        Ok(())
    }

    let mut snapshot = BTreeMap::new();
    let mut observer = observer;
    walk(
        root,
        root,
        &mut snapshot,
        restore_observer_times,
        &mut observer,
        capture_handles,
    )?;
    if restore_observer_times {
        // Restoring atime/mtime advances ctime. Re-observe metadata only after the
        // complete traversal so hard-link aliases all capture the same final ctime.
        for (relative_path, node) in &mut snapshot {
            if node.kind == "inaccessible" {
                continue;
            }
            let path = if relative_path == "." {
                root.to_path_buf()
            } else {
                root.join(relative_path)
            };
            let metadata = fs::symlink_metadata(&path)
                .map_err(|error| format_path_error("re-observe restored metadata", &path, error))?;
            node.times = times_from_metadata(&metadata);
        }
    }
    Ok(snapshot)
}

pub(crate) fn times_from_metadata(metadata: &fs::Metadata) -> FsTimes {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        FsTimes {
            atime_sec: metadata.atime(),
            atime_nsec: metadata.atime_nsec(),
            mtime_sec: metadata.mtime(),
            mtime_nsec: metadata.mtime_nsec(),
            ctime_sec: metadata.ctime(),
            ctime_nsec: metadata.ctime_nsec(),
        }
    }
    #[cfg(not(unix))]
    {
        FsTimes::default()
    }
}

fn mode_octal_string_from_metadata(metadata: &fs::Metadata) -> String {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        format!("{:04o}", metadata.permissions().mode() & 0o7777)
    }
    #[cfg(not(unix))]
    {
        if metadata.is_dir() {
            "0755".to_string()
        } else {
            "0644".to_string()
        }
    }
}

#[cfg(test)]
mod controlled_chmod_tests {
    use super::{
        canonical_environment_config, chmod_snapshot_post, chmod_snapshot_pre,
        format_target_process_error, prepare_controlled_chmod_target, read_exec_status,
        run_controlled_chmod_target, run_controlled_chmod_variant, run_controlled_umask_probe,
        snapshot_fs, snapshot_fs_checked, snapshot_fs_post, snapshot_fs_pre, FsCaptureError,
    };
    use crate::fuzz::fixture::materialize_fixture;
    use crate::fuzz::input::scenario_case;
    use crate::fuzz::{
        GeneratedCase, HostInodeKeySnapshot, ResolvedPaths, ResolvedTarget, RunResult, VariantKind,
    };
    use crate::utils::cli::ExecKind;
    use crate::utils::process::ProcessError;
    use crate::{
        FUZZER_DOTNET_RUNTIME_FAILURE, FUZZER_OUTCOME_MARKER_PREFIX, FUZZER_TARGET_SPAWN_FAILURE,
        FUZZER_TIMEOUT,
    };
    use std::fs;
    use std::io::{self, Write};
    use std::path::{Path, PathBuf};
    use std::time::Duration;

    // A native target spawn error must carry the stable target-spawn outcome marker.
    #[test]
    fn native_target_spawn_error_has_target_spawn_marker() {
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/missing/native-target"),
            label: "dut",
        };

        let error = format_target_process_error(
            &target,
            &[],
            Path::new("."),
            Duration::from_secs(1),
            ProcessError::Spawn("not found".to_string()),
        );

        assert!(error.starts_with(&format!(
            "{FUZZER_OUTCOME_MARKER_PREFIX}{FUZZER_TARGET_SPAWN_FAILURE}"
        )));
    }

    // A .NET host spawn error must carry the stable runtime outcome marker.
    #[test]
    fn dotnet_target_spawn_error_has_runtime_marker() {
        let target = ResolvedTarget {
            kind: ExecKind::DotnetDll,
            path: PathBuf::from("/tmp/dut.dll"),
            label: "dut",
        };

        let error = format_target_process_error(
            &target,
            &[],
            Path::new("."),
            Duration::from_secs(1),
            ProcessError::Spawn("dotnet missing".to_string()),
        );

        assert!(error.starts_with(&format!(
            "{FUZZER_OUTCOME_MARKER_PREFIX}{FUZZER_DOTNET_RUNTIME_FAILURE}"
        )));
    }

    // A target process timeout must carry the stable fuzzer-timeout outcome marker.
    #[test]
    fn target_timeout_error_has_timeout_marker() {
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/true"),
            label: "reference",
        };

        let error = format_target_process_error(
            &target,
            &[],
            Path::new("."),
            Duration::from_secs(1),
            ProcessError::Timeout,
        );

        assert!(error.starts_with(&format!("{FUZZER_OUTCOME_MARKER_PREFIX}{FUZZER_TIMEOUT}")));
    }

    #[cfg(target_os = "linux")]
    fn helper_pid_for_target(target: &Path) -> u32 {
        use std::os::unix::ffi::OsStrExt;

        let target = target.as_os_str().as_bytes();
        std::fs::read_dir("/proc")
            .unwrap()
            .filter_map(Result::ok)
            .filter_map(|entry| entry.file_name().to_str()?.parse::<u32>().ok())
            .find(|pid| {
                std::fs::read(format!("/proc/{pid}/cmdline"))
                    .is_ok_and(|cmdline| cmdline.split(|byte| *byte == 0).any(|arg| arg == target))
            })
            .expect("live chmod exec helper")
    }

    #[cfg(target_os = "linux")]
    fn assert_process_reaped(pid: u32) {
        let process = PathBuf::from(format!("/proc/{pid}"));
        let deadline = std::time::Instant::now() + Duration::from_secs(1);
        while process.exists() && std::time::Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(5));
        }
        assert!(!process.exists(), "process {pid} was not reaped");
    }

    fn run_pinned_gnu_chmod(case: &GeneratedCase, root: &Path) -> RunResult {
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join("_build/coreutils/src/chmod"),
            label: "reference",
        };
        let environment = canonical_environment_config(0o022).unwrap();
        run_controlled_chmod_target(
            &target,
            &case.argv,
            &case.stdin,
            &case.cwd,
            root,
            &environment,
            0o022,
            Duration::from_secs(10),
        )
        .unwrap()
    }

    // The separately executed probe observes the selected implementation-campaign umask.
    #[test]
    fn controlled_child_observes_selected_umask() {
        let environment = canonical_environment_config(0o027).unwrap();
        let probe =
            run_controlled_umask_probe(&environment, 0o027, PathBuf::from(".").as_path()).unwrap();

        assert_eq!(probe.observed_umask, 0o027);
    }

    // Reference and DUT roles receive the same cwd, environment, umask, stdin, streams, and argv0.
    #[cfg(unix)]
    #[test]
    fn controlled_chmod_roles_share_exact_child_configuration() {
        let target = |label| ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label,
        };
        let paths = ResolvedPaths {
            reference: target("reference"),
            dut: target("dut"),
        };
        let env = canonical_environment_config(0o027).unwrap();
        let argv = vec![
            "-c".to_string(),
            "read input; printf 'cwd=%s\\nstdin=%s\\n' \"$PWD\" \"$input\"; \
             tr '\\0' '\\n' </proc/$$/environ | sort; \
             printf 'argv0=%s umask=' \"$0\"; umask; printf 'stderr=%s\\n' \"$input\" >&2"
                .to_string(),
        ];
        let root = tempfile::tempdir().unwrap();
        std::fs::create_dir(root.path().join("work")).unwrap();
        let run = |kind| {
            run_controlled_chmod_variant(
                kind,
                &paths,
                &argv,
                b"payload\n",
                Path::new("work"),
                root.path(),
                &env,
                0o027,
                Duration::from_secs(10),
            )
            .unwrap()
        };

        let reference = run(VariantKind::Ref);
        let dut = run(VariantKind::Dut);
        let expected = format!(
            "cwd={}\nstdin=payload\nLANG=C\nLC_ALL=C\nPATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin\nQUOTING_STYLE=literal\nTERM=dumb\nTZ=UTC0\nargv0=chmod umask=0027\n",
            root.path().join("work").display()
        );
        assert_eq!(reference, dut);
        assert_eq!(reference.termination.exit_code(), Some(0));
        assert_eq!(reference.stdout, expected.as_bytes());
        assert_eq!(reference.stderr, b"stderr=payload\n");
    }

    // A READY helper must not execute its target or expose target stdout before GO.
    #[cfg(unix)]
    #[test]
    fn controlled_chmod_target_waits_for_go_before_target_effects() {
        let root = tempfile::tempdir().unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "reference",
        };
        let argv = vec![
            "-c".to_string(),
            "printf target-stdout; printf target-effect > marker".to_string(),
        ];
        let env = canonical_environment_config(0o022).unwrap();
        let prepared = prepare_controlled_chmod_target(
            &target,
            &argv,
            Path::new("."),
            root.path(),
            &env,
            0o022,
            None,
        )
        .unwrap();

        assert!(!root.path().join("marker").exists());

        let result = prepared
            .go_and_collect(&[], Duration::from_secs(10))
            .unwrap();
        assert_eq!(result.stdout, b"target-stdout");
        assert_eq!(
            std::fs::read(root.path().join("marker")).unwrap(),
            b"target-effect"
        );
    }

    // A successful exec closes the status channel without altering target stdout or stderr.
    #[cfg(unix)]
    #[test]
    fn controlled_chmod_success_reports_status_eof_and_untouched_streams() {
        let root = tempfile::tempdir().unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: PathBuf::from("/bin/sh"),
            label: "dut",
        };
        let argv = vec![
            "-c".to_string(),
            "printf 'READY GO stdout'; printf 'READY GO stderr' >&2".to_string(),
        ];
        let env = canonical_environment_config(0o022).unwrap();

        let result = run_controlled_chmod_target(
            &target,
            &argv,
            &[],
            Path::new("."),
            root.path(),
            &env,
            0o022,
            Duration::from_secs(10),
        )
        .unwrap();

        assert_eq!(result.termination.exit_code(), Some(0));
        assert_eq!(result.stdout, b"READY GO stdout");
        assert_eq!(result.stderr, b"READY GO stderr");
    }

    // An invalid target returns one contextual exec frame without leaking protocol bytes.
    #[cfg(unix)]
    #[test]
    fn controlled_chmod_invalid_target_returns_one_contextual_exec_error() {
        let root = tempfile::tempdir().unwrap();
        std::fs::create_dir(root.path().join("work")).unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: root.path().join("missing-chmod"),
            label: "reference",
        };
        let env = canonical_environment_config(0o022).unwrap();

        let error = run_controlled_chmod_target(
            &target,
            &[],
            &[],
            Path::new("work"),
            root.path(),
            &env,
            0o022,
            Duration::from_secs(10),
        )
        .unwrap_err();

        assert_eq!(error.matches("failed to exec reference variant").count(), 1);
        assert!(error.contains("cwd=`work`"));
        assert!(error.contains("stdout=[] stderr=[]"));
        assert!(!error.contains("READY"));
        assert!(!error.contains(" GO"));
    }

    // Dropping a READY helper before GO kills and reaps the blocked child.
    #[cfg(target_os = "linux")]
    #[test]
    fn controlled_chmod_drop_before_go_kills_and_reaps_helper() {
        let root = tempfile::tempdir().unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: root.path().join("never-exec-drop"),
            label: "reference",
        };
        let env = canonical_environment_config(0o022).unwrap();
        let prepared = prepare_controlled_chmod_target(
            &target,
            &[],
            Path::new("."),
            root.path(),
            &env,
            0o022,
            None,
        )
        .unwrap();
        let pid = helper_pid_for_target(&target.path);

        drop(prepared);

        assert_process_reaped(pid);
    }

    // A malformed control message fails closed and the helper is reaped.
    #[cfg(target_os = "linux")]
    #[test]
    fn controlled_chmod_malformed_go_fails_closed_and_reaps_helper() {
        let root = tempfile::tempdir().unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: root.path().join("never-exec-malformed"),
            label: "dut",
        };
        let env = canonical_environment_config(0o022).unwrap();
        let mut prepared = prepare_controlled_chmod_target(
            &target,
            &[],
            Path::new("."),
            root.path(),
            &env,
            0o022,
            None,
        )
        .unwrap();
        let pid = helper_pid_for_target(&target.path);

        prepared.go.as_mut().unwrap().write_all(b"NO").unwrap();
        prepared.go.take();
        let error = read_exec_status(&mut prepared.status, Duration::from_secs(10))
            .unwrap()
            .unwrap();
        let output = prepared
            .process
            .collect(&[], Duration::from_secs(10))
            .unwrap();

        assert_eq!(error, "malformed GO: [78, 79]");
        assert_eq!(
            super::super::process_outcome::Termination::from_status(output.status).exit_code(),
            Some(127)
        );
        assert!(output.stdout.is_empty());
        assert!(output.stderr.is_empty());
        assert_process_reaped(pid);
    }

    // An EOF control message fails closed and the helper is reaped.
    #[cfg(target_os = "linux")]
    #[test]
    fn controlled_chmod_go_eof_fails_closed_and_reaps_helper() {
        let root = tempfile::tempdir().unwrap();
        let target = ResolvedTarget {
            kind: ExecKind::Native,
            path: root.path().join("never-exec-eof"),
            label: "dut",
        };
        let env = canonical_environment_config(0o022).unwrap();
        let mut prepared = prepare_controlled_chmod_target(
            &target,
            &[],
            Path::new("."),
            root.path(),
            &env,
            0o022,
            None,
        )
        .unwrap();
        let pid = helper_pid_for_target(&target.path);

        prepared.go.take();
        let error = read_exec_status(&mut prepared.status, Duration::from_secs(10))
            .unwrap()
            .unwrap();
        let output = prepared
            .process
            .collect(&[], Duration::from_secs(10))
            .unwrap();

        assert_eq!(error, "malformed GO: []");
        assert_eq!(
            super::super::process_outcome::Termination::from_status(output.status).exit_code(),
            Some(127)
        );
        assert!(output.stdout.is_empty());
        assert!(output.stderr.is_empty());
        assert_process_reaped(pid);
    }

    // An observed directory-read denial is retained as a modeled inaccessible filesystem node.
    #[cfg(unix)]
    #[test]
    fn snapshot_records_unreadable_directory_as_inaccessible() {
        use std::fs;
        use std::os::unix::fs::MetadataExt;
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let blocked = root.path().join("blocked");
        fs::create_dir(&blocked).unwrap();
        let metadata = fs::symlink_metadata(&blocked).unwrap();
        fs::set_permissions(&blocked, fs::Permissions::from_mode(0o0)).unwrap();

        match fs::read_dir(&blocked) {
            Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {}
            _ => {
                fs::set_permissions(&blocked, fs::Permissions::from_mode(0o700)).unwrap();
                return;
            }
        }

        let snapshot = snapshot_fs(root.path());
        fs::set_permissions(&blocked, fs::Permissions::from_mode(0o700)).unwrap();

        let snapshot = snapshot.unwrap();
        let node = snapshot.get("blocked").unwrap();
        assert_eq!(node.kind, "inaccessible");
        assert_eq!(
            node.host_key,
            Some(HostInodeKeySnapshot {
                device: metadata.dev(),
                inode: metadata.ino()
            })
        );
    }

    // A non-UTF-8 relative path must stop capture instead of entering a replacement path.
    #[cfg(unix)]
    #[test]
    fn snapshot_rejects_non_utf8_relative_path() {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt;

        let root = tempfile::tempdir().unwrap();
        std::fs::write(
            root.path().join(OsString::from_vec(vec![b'f', 0xff])),
            b"data",
        )
        .unwrap();

        assert_eq!(
            snapshot_fs_checked(root.path()).unwrap_err(),
            FsCaptureError::Encoding {
                field: "relative path"
            }
        );
    }

    // A non-UTF-8 symlink target must stop capture instead of recording replacement text.
    #[cfg(unix)]
    #[test]
    fn snapshot_rejects_non_utf8_symlink_target() {
        use std::ffi::OsString;
        use std::os::unix::ffi::OsStringExt;
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().unwrap();
        symlink(
            OsString::from_vec(vec![b't', 0xff]),
            root.path().join("link"),
        )
        .unwrap();

        assert_eq!(
            snapshot_fs_checked(root.path()).unwrap_err(),
            FsCaptureError::Encoding {
                field: "symlink target"
            }
        );
    }

    // A pre-opened handle must preserve exact bytes when chmod makes the same file unreadable.
    #[cfg(unix)]
    #[test]
    fn chmod_snapshot_reads_mode_zero_file_through_preopened_handle() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("file");
        fs::write(&path, b"payload").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
        let (_, mut observer) = chmod_snapshot_pre(root.path()).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o0)).unwrap();

        let (snapshot, _) = chmod_snapshot_post(root.path(), &mut observer).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();

        assert_eq!(snapshot["file"].kind, "file");
        assert_eq!(snapshot["file"].mode_octal, "0000");
        assert_eq!(snapshot["file"].data, b"payload");
    }

    // A live handle must observe same-inode truncation and rewrite rather than cached pre-state bytes.
    #[cfg(unix)]
    #[test]
    fn chmod_snapshot_handle_observes_same_inode_content_mutation() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("file");
        fs::write(&path, b"before").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
        let (_, mut observer) = chmod_snapshot_pre(root.path()).unwrap();
        fs::write(&path, b"after").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o0)).unwrap();

        let (snapshot, _) = chmod_snapshot_post(root.path(), &mut observer).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();

        assert_eq!(snapshot["file"].data, b"after");
    }

    // An open handle must not resurrect a path deleted before post-state traversal.
    #[cfg(unix)]
    #[test]
    fn chmod_snapshot_does_not_resurrect_deleted_file() {
        use std::fs;

        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("file");
        fs::write(&path, b"payload").unwrap();
        let (_, mut observer) = chmod_snapshot_pre(root.path()).unwrap();
        fs::remove_file(&path).unwrap();

        let (snapshot, _) = chmod_snapshot_post(root.path(), &mut observer).unwrap();

        assert!(!snapshot.contains_key("file"));
    }

    // A regular-file rename preserves the exact pre-path to post-path object relation.
    #[cfg(target_os = "linux")]
    #[test]
    fn snapshot_identity_tracks_regular_file_rename() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("before"), b"x").unwrap();
        let (_, mut observer) = snapshot_fs_pre(root.path()).unwrap();

        fs::rename(root.path().join("before"), root.path().join("after")).unwrap();
        let (_, evidence) = snapshot_fs_post(root.path(), &mut observer).unwrap();

        assert!(evidence.contains(&("before".to_string(), "after".to_string())));
    }

    // Deleting and recreating equal bytes at one path does not preserve object identity.
    #[cfg(target_os = "linux")]
    #[test]
    fn snapshot_identity_rejects_delete_and_recreate() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("file"), b"same").unwrap();
        let (_, mut observer) = snapshot_fs_pre(root.path()).unwrap();

        fs::remove_file(root.path().join("file")).unwrap();
        fs::write(root.path().join("file"), b"same").unwrap();
        let (_, evidence) = snapshot_fs_post(root.path(), &mut observer).unwrap();

        assert!(!evidence.contains(&("file".to_string(), "file".to_string())));
    }

    // Every pre hardlink name relates to every surviving post name for its shared object.
    #[cfg(target_os = "linux")]
    #[test]
    fn snapshot_identity_tracks_hardlink_aliases() {
        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("a"), b"x").unwrap();
        fs::hard_link(root.path().join("a"), root.path().join("b")).unwrap();
        let (_, mut observer) = snapshot_fs_pre(root.path()).unwrap();

        fs::rename(root.path().join("a"), root.path().join("c")).unwrap();
        let (_, evidence) = snapshot_fs_post(root.path(), &mut observer).unwrap();

        for before in ["a", "b"] {
            for after in ["b", "c"] {
                assert!(evidence.contains(&(before.to_string(), after.to_string())));
            }
        }
    }

    // A no-follow handle tracks the symlink object rather than its target.
    #[cfg(target_os = "linux")]
    #[test]
    fn snapshot_identity_tracks_symlink_without_following() {
        use std::os::unix::fs::symlink;

        let root = tempfile::tempdir().unwrap();
        fs::write(root.path().join("target"), b"x").unwrap();
        symlink("target", root.path().join("link")).unwrap();
        let (_, mut observer) = snapshot_fs_pre(root.path()).unwrap();

        fs::rename(root.path().join("link"), root.path().join("renamed")).unwrap();
        let (_, evidence) = snapshot_fs_post(root.path(), &mut observer).unwrap();

        assert!(evidence.contains(&("link".to_string(), "renamed".to_string())));
        assert!(!evidence.contains(&("link".to_string(), "target".to_string())));
    }

    // An O_PATH handle tracks an empty directory across a rename.
    #[cfg(target_os = "linux")]
    #[test]
    fn snapshot_identity_tracks_empty_directory_rename() {
        let root = tempfile::tempdir().unwrap();
        fs::create_dir(root.path().join("before")).unwrap();
        let (_, mut observer) = snapshot_fs_pre(root.path()).unwrap();

        fs::rename(root.path().join("before"), root.path().join("after")).unwrap();
        let (_, evidence) = snapshot_fs_post(root.path(), &mut observer).unwrap();

        assert!(evidence.contains(&("before".to_string(), "after".to_string())));
    }

    // A replacement inode must fail closed when its current path cannot be read.
    #[cfg(unix)]
    #[test]
    fn chmod_snapshot_rejects_unreadable_replacement_inode() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("file");
        fs::write(&path, b"old").unwrap();
        let (_, mut observer) = chmod_snapshot_pre(root.path()).unwrap();
        fs::remove_file(&path).unwrap();
        fs::write(&path, b"new").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o0)).unwrap();

        let error = chmod_snapshot_post(root.path(), &mut observer).unwrap_err();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();

        assert!(error.contains("failed to read file"));
        assert!(error.contains("Permission denied"));
    }

    // A new unreadable file without a pre-opened handle must fail closed.
    #[cfg(unix)]
    #[test]
    fn chmod_snapshot_rejects_unreadable_new_file() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let (_, mut observer) = chmod_snapshot_pre(root.path()).unwrap();
        let path = root.path().join("file");
        fs::write(&path, b"new").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o0)).unwrap();

        let error = chmod_snapshot_post(root.path(), &mut observer).unwrap_err();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();

        assert!(error.contains("failed to read file"));
        assert!(error.contains("Permission denied"));
    }

    // The pinned GNU chmod must process the parent operand before the inaccessible nested operand.
    #[cfg(unix)]
    #[test]
    fn pinned_gnu_chmod_restores_access_in_operand_order() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let case = scenario_case("chmod", 40).unwrap();
        let root = tempfile::tempdir().unwrap();
        materialize_fixture(root.path(), &case.fixture).unwrap();
        let parent = root.path().join("d");
        let child = parent.join("e");
        match fs::symlink_metadata(&child) {
            Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {}
            _ => {
                fs::set_permissions(&parent, fs::Permissions::from_mode(0o700)).unwrap();
                fs::set_permissions(&child, fs::Permissions::from_mode(0o700)).unwrap();
                return;
            }
        }
        assert_eq!(
            snapshot_fs(root.path()).unwrap().get("d").unwrap().kind,
            "inaccessible"
        );

        let result = run_pinned_gnu_chmod(&case, root.path());
        let snapshot = snapshot_fs(root.path()).unwrap();

        assert_eq!(result.termination.exit_code(), Some(0));
        assert!(result.stdout.is_empty());
        assert!(result.stderr.is_empty());
        assert_eq!(snapshot.get("d").unwrap().mode_octal, "0700");
        assert_eq!(snapshot.get("d/e").unwrap().mode_octal, "0700");
    }

    // An observed access denial must not prevent pinned GNU chmod from changing a later operand.
    #[cfg(unix)]
    #[test]
    fn pinned_gnu_chmod_continues_after_observed_inaccessible_operand() {
        use std::fs;
        use std::os::unix::fs::PermissionsExt;

        let case = scenario_case("chmod", 41).unwrap();
        let root = tempfile::tempdir().unwrap();
        materialize_fixture(root.path(), &case.fixture).unwrap();
        let blocked = root.path().join("blocked");
        match fs::symlink_metadata(blocked.join("child")) {
            Err(e) if e.kind() == io::ErrorKind::PermissionDenied => {}
            _ => {
                fs::set_permissions(&blocked, fs::Permissions::from_mode(0o700)).unwrap();
                return;
            }
        }
        assert_eq!(
            snapshot_fs(root.path())
                .unwrap()
                .get("blocked")
                .unwrap()
                .kind,
            "inaccessible"
        );

        let result = run_pinned_gnu_chmod(&case, root.path());
        let snapshot = snapshot_fs(root.path()).unwrap();
        fs::set_permissions(&blocked, fs::Permissions::from_mode(0o700)).unwrap();

        assert_eq!(result.termination.exit_code(), Some(1));
        assert!(result.stdout.is_empty());
        assert_eq!(snapshot.get("tree/root-file").unwrap().mode_octal, "0600");
    }
}

#[cfg(all(test, target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
mod raw_stat_tests {
    use super::raw_stat_metadata_from_metadata;
    use crate::utils::world_json::RawStatMetadataJson;

    // A real character-device stat yields Known rdev and its actual signed block-size field.
    #[test]
    #[allow(deprecated)]
    fn raw_metadata_native_device() {
        use std::os::linux::fs::MetadataExt;
        let metadata = std::fs::metadata("/dev/null").unwrap();
        let raw = metadata.as_raw_stat();
        assert_eq!(
            raw_stat_metadata_from_metadata(&metadata),
            RawStatMetadataJson::Known {
                device_number: raw.st_rdev,
                io_block_bytes: raw.st_blksize
            }
        );
        assert_ne!(raw.st_rdev, 0);
    }

    // Real filesystem capture preserves raw metadata with hardlink identity and arbitrary content bytes.
    #[test]
    fn raw_metadata_native_filesystem_capture() {
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("a");
        let bytes = b"raw bytes\x00\xff";
        std::fs::write(&path, bytes).unwrap();
        std::fs::hard_link(&path, directory.path().join("b")).unwrap();
        let expected = raw_stat_metadata_from_metadata(&std::fs::metadata(path).unwrap());
        assert!(matches!(expected, RawStatMetadataJson::Known { .. }));
        let snapshot = super::snapshot_fs(directory.path()).unwrap();
        assert_eq!(snapshot["a"].raw_stat_metadata, expected);
        assert_eq!(snapshot["b"].raw_stat_metadata, expected);
        assert_eq!(snapshot["a"].host_key, snapshot["b"].host_key);
        assert_eq!(snapshot["a"].data, bytes);
        let encoded = serde_json::to_value(&snapshot).unwrap();
        assert_eq!(
            encoded["a"]["raw_stat_metadata"],
            serde_json::to_value(expected).unwrap()
        );
    }

    // A controlled libc interposer can expose raw signed endpoints through the actual capture projection.
    #[test]
    fn raw_metadata_native_injection_probe() {
        let fixture = tempfile::NamedTempFile::new().unwrap();
        let path = std::env::var_os("RAW_STAT_PROBE_PATH")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(|| fixture.path().to_path_buf());
        let metadata = std::fs::metadata(path).unwrap();
        let value = raw_stat_metadata_from_metadata(&metadata);
        println!("RAW_STAT_JSON={}", serde_json::to_string(&value).unwrap());
        let (default_device, default_block) = match value {
            RawStatMetadataJson::Known {
                device_number,
                io_block_bytes,
            } => (device_number, io_block_bytes),
            RawStatMetadataJson::Unknown => panic!("Linux raw-stat capture returned Unknown"),
        };
        let device: u64 = std::env::var("RAW_STAT_DEVICE")
            .map(|text| text.parse().unwrap())
            .unwrap_or(default_device);
        let block: i64 = std::env::var("RAW_STAT_BLOCK")
            .map(|text| text.parse().unwrap())
            .unwrap_or(default_block);
        assert_eq!(
            value,
            RawStatMetadataJson::Known {
                device_number: device,
                io_block_bytes: block
            }
        );
    }
}
