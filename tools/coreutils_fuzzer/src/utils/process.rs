use std::io::{ErrorKind, Read, Write};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::thread;
use std::time::{Duration, Instant};

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
use std::fs::File;

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[repr(C)]
struct PollDescriptor {
    fd: i32,
    events: i16,
    revents: i16,
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
unsafe extern "C" {
    fn syscall(number: std::os::raw::c_long, ...) -> std::os::raw::c_long;
    fn poll(fds: *mut PollDescriptor, count: std::os::raw::c_ulong, timeout: i32) -> i32;
    fn fcntl(fd: i32, command: i32, ...) -> i32;
}

struct ExitNotification {
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    fd: Option<OwnedFd>,
}

impl ExitNotification {
    fn for_child(child: &Child) -> Self {
        #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
        {
            // This unreaped Child owns the PID. pidfd_open also sets CLOEXEC.
            const SYS_PIDFD_OPEN: std::os::raw::c_long = 434;
            let raw = unsafe { syscall(SYS_PIDFD_OPEN, child.id() as i32, 0u32) };
            if raw >= 0 {
                return Self {
                    fd: Some(unsafe { OwnedFd::from_raw_fd(raw as i32) }),
                };
            }
            // Optional notification may be unavailable through kernel support,
            // execution policy or resource limits; Child still owns the wait.
            Self { fd: None }
        }
        #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
        {
            let _ = child;
            Self {}
        }
    }

    fn wait(&mut self, remaining: Duration) {
        #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
        if let Some(fd) = &self.fd {
            let mut descriptor = PollDescriptor {
                fd: fd.as_raw_fd(),
                events: 1, // POLLIN: the child has exited.
                revents: 0,
            };
            let timeout = remaining
                .as_nanos()
                .div_ceil(1_000_000)
                .min(i32::MAX as u128) as i32;
            let result = unsafe { poll(&mut descriptor, 1, timeout) };
            if result < 0 {
                let error = std::io::Error::last_os_error();
                // The caller rechecks both Child status and the same deadline.
                if error.kind() != ErrorKind::Interrupted {
                    self.fd = None;
                }
            } else if descriptor.revents & (8 | 32) != 0 {
                self.fd = None;
            }
            return;
        }
        thread::sleep(remaining.min(Duration::from_millis(100)));
    }
}

#[derive(Debug)]
pub(crate) struct ProcessOutput {
    pub(crate) status: ExitStatus,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
}

#[derive(Debug, serde::Serialize)]
#[serde(tag = "kind", content = "detail", rename_all = "snake_case")]
pub(crate) enum ProcessError {
    Spawn(String),
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    StdinUnavailable,
    StdinWrite(String),
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    StdinThreadPanic,
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    StdoutUnavailable,
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    StderrUnavailable,
    StdoutRead(String),
    StderrRead(String),
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    StdoutThreadPanic,
    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    StderrThreadPanic,
    Wait(String),
    Timeout,
    InvalidTimeout,
    Channel {
        name: String,
        message: String,
    },
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub(crate) struct ProcessChannel {
    pub(crate) name: String,
    pub(crate) file: File,
    /// None collects output; Some writes the complete input and closes the endpoint.
    pub(crate) input: Option<Vec<u8>>,
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[derive(Debug)]
pub(crate) struct ChannelOutput {
    pub(crate) name: String,
    pub(crate) bytes: Vec<u8>,
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
#[derive(Debug, Default)]
pub(crate) struct ProcessCollection {
    pub(crate) status: Option<ExitStatus>,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
    pub(crate) channels: Vec<ChannelOutput>,
    pub(crate) errors: Vec<ProcessError>,
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
struct ActiveChannel {
    name: String,
    file: Option<File>,
    input: Option<Vec<u8>>,
    written: usize,
    output: Vec<u8>,
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
impl ActiveChannel {
    fn new(channel: ProcessChannel) -> Self {
        Self {
            name: channel.name,
            file: Some(channel.file),
            input: channel.input,
            written: 0,
            output: Vec::new(),
        }
    }

    fn fail(&mut self, error: std::io::Error, result: &mut ProcessCollection) {
        self.file.take();
        let message = error.to_string();
        let error = match self.name.as_str() {
            "stdin" if error.kind() == ErrorKind::BrokenPipe => return,
            "stdin" => ProcessError::StdinWrite(message),
            "stdout" => ProcessError::StdoutRead(message),
            "stderr" => ProcessError::StderrRead(message),
            _ => ProcessError::Channel {
                name: self.name.clone(),
                message,
            },
        };
        result.errors.push(error);
    }

    fn prepare(&mut self, result: &mut ProcessCollection) {
        if self.input.as_ref().is_some_and(Vec::is_empty) {
            self.file.take();
            return;
        }
        let fd = self.file.as_ref().expect("new channel").as_raw_fd();
        let flags = unsafe { fcntl(fd, 3) }; // F_GETFL
        if flags < 0 || unsafe { fcntl(fd, 4, flags | 0x800) } < 0 {
            // F_SETFL, O_NONBLOCK
            self.fail(std::io::Error::last_os_error(), result);
        }
    }

    fn transfer(&mut self, result: &mut ProcessCollection) {
        let Some(file) = &mut self.file else { return };
        // Bound each transfer so a continuously ready stream cannot starve another
        // channel or the single process deadline.
        let operation = if let Some(input) = &self.input {
            let end = input.len().min(self.written.saturating_add(65_536));
            file.write(&input[self.written..end]).inspect(|count| {
                self.written += *count;
            })
        } else {
            let mut buffer = [0; 65_536];
            file.read(&mut buffer).inspect(|count| {
                self.output.extend_from_slice(&buffer[..*count]);
            })
        };
        match operation {
            Ok(0) if self.input.is_some() => {
                self.fail(std::io::Error::from(ErrorKind::WriteZero), result);
            }
            Ok(0) => {
                self.file.take();
            }
            Ok(_) => {
                if self
                    .input
                    .as_ref()
                    .is_some_and(|input| self.written == input.len())
                {
                    self.file.take();
                }
            }
            Err(error)
                if matches!(error.kind(), ErrorKind::WouldBlock | ErrorKind::Interrupted) => {}
            Err(error) => self.fail(error, result),
        }
    }
}

pub(crate) fn run_command_with_timeout_and_input(
    cmd: &mut Command,
    stdin: &[u8],
    timeout: Duration,
) -> Result<ProcessOutput, ProcessError> {
    validate_timeout(timeout)?;
    PreparedProcess::spawn(cmd)?.collect(stdin, timeout)
}

pub(crate) fn validate_timeout(timeout: Duration) -> Result<(), ProcessError> {
    Instant::now()
        .checked_add(timeout)
        .map(|_| ())
        .ok_or(ProcessError::InvalidTimeout)
}

pub(crate) struct PreparedProcess {
    child: Option<Child>,
    exit_notification: ExitNotification,
}

impl PreparedProcess {
    pub(crate) fn spawn(cmd: &mut Command) -> Result<Self, ProcessError> {
        cmd.stdin(Stdio::piped());
        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());

        let child = cmd
            .spawn()
            .map_err(|err| ProcessError::Spawn(err.to_string()))?;
        let exit_notification = ExitNotification::for_child(&child);
        Ok(Self {
            child: Some(child),
            exit_notification,
        })
    }

    pub(crate) fn id(&self) -> u32 {
        self.child.as_ref().expect("live child").id()
    }

    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    pub(crate) fn collect(
        self,
        stdin: &[u8],
        timeout: Duration,
    ) -> Result<ProcessOutput, ProcessError> {
        let result = self.collect_with_channels(stdin, timeout, Vec::new());
        if let Some(error) = result.errors.into_iter().next() {
            return Err(error);
        }
        Ok(ProcessOutput {
            status: result
                .status
                .expect("successful collection reaped the child"),
            stdout: result.stdout,
            stderr: result.stderr,
        })
    }

    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    pub(crate) fn collect_with_channels(
        mut self,
        stdin: &[u8],
        timeout: Duration,
        extra: Vec<ProcessChannel>,
    ) -> ProcessCollection {
        let mut result = ProcessCollection::default();
        let Some(deadline) = Instant::now().checked_add(timeout) else {
            result.errors.push(ProcessError::InvalidTimeout);
            if let Some(mut child) = self.child.take() {
                let _ = child.kill();
                match child.wait() {
                    Ok(status) => result.status = Some(status),
                    Err(error) => result.errors.push(ProcessError::Wait(error.to_string())),
                }
            }
            return result;
        };
        let child = self.child.as_mut().expect("live child");
        let mut channels = vec![
            ProcessChannel {
                name: "stdin".into(),
                file: File::from(OwnedFd::from(child.stdin.take().expect("piped stdin"))),
                input: Some(stdin.to_vec()),
            },
            ProcessChannel {
                name: "stdout".into(),
                file: File::from(OwnedFd::from(child.stdout.take().expect("piped stdout"))),
                input: None,
            },
            ProcessChannel {
                name: "stderr".into(),
                file: File::from(OwnedFd::from(child.stderr.take().expect("piped stderr"))),
                input: None,
            },
        ]
        .into_iter()
        .chain(extra)
        .map(ActiveChannel::new)
        .collect::<Vec<_>>();
        for channel in &mut channels {
            channel.prepare(&mut result);
        }

        loop {
            if let Some(child) = &mut self.child {
                match child.try_wait() {
                    Ok(Some(status)) => {
                        result.status = Some(status);
                        self.child.take();
                    }
                    Ok(None) => {}
                    Err(error) => {
                        result.errors.push(ProcessError::Wait(error.to_string()));
                        break;
                    }
                }
            }
            if result.status.is_some() && channels.iter().all(|channel| channel.file.is_none()) {
                break;
            }
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                result.errors.push(ProcessError::Timeout);
                break;
            }
            let mut pollfds = Vec::new();
            let mut indices = Vec::new();
            for (index, channel) in channels.iter().enumerate() {
                if let Some(file) = &channel.file {
                    pollfds.push(PollDescriptor {
                        fd: file.as_raw_fd(),
                        events: if channel.input.is_some() { 4 } else { 1 },
                        revents: 0,
                    });
                    indices.push(index);
                }
            }
            if pollfds.is_empty() && self.child.is_some() {
                self.exit_notification.wait(remaining);
                continue;
            }
            let pidfd = if self.child.is_some() {
                self.exit_notification.fd.as_ref()
            } else {
                None
            };
            if let Some(fd) = pidfd {
                pollfds.push(PollDescriptor {
                    fd: fd.as_raw_fd(),
                    events: 1,
                    revents: 0,
                });
            }
            // Keep the existing portable wait fallback when pidfd is unavailable.
            let wait = if self.child.is_some() && pidfd.is_none() {
                remaining.min(Duration::from_millis(100))
            } else {
                remaining
            };
            let millis = wait.as_nanos().div_ceil(1_000_000).min(i32::MAX as u128) as i32;
            let ready = unsafe { poll(pollfds.as_mut_ptr(), pollfds.len() as _, millis) };
            if ready < 0 {
                let error = std::io::Error::last_os_error();
                if error.kind() == ErrorKind::Interrupted {
                    continue;
                }
                result.errors.push(ProcessError::Wait(error.to_string()));
                break;
            }
            for (descriptor, index) in pollfds.iter().zip(indices) {
                if descriptor.revents != 0 {
                    channels[index].transfer(&mut result);
                }
            }
        }
        if let Some(mut child) = self.child.take() {
            let _ = child.kill();
            match child.wait() {
                Ok(status) => result.status = Some(status),
                Err(error) => result.errors.push(ProcessError::Wait(error.to_string())),
            }
        }
        for (index, channel) in channels.into_iter().enumerate() {
            match index {
                0 => {}
                1 => result.stdout = channel.output,
                2 => result.stderr = channel.output,
                _ => result.channels.push(ChannelOutput {
                    name: channel.name,
                    bytes: channel.output,
                }),
            }
        }
        result
    }

    #[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
    pub(crate) fn collect(
        mut self,
        stdin: &[u8],
        timeout: Duration,
    ) -> Result<ProcessOutput, ProcessError> {
        let deadline = Instant::now()
            .checked_add(timeout)
            .ok_or(ProcessError::InvalidTimeout)?;
        let child = self.child.as_mut().expect("live child");
        let mut child_stdin = child.stdin.take().ok_or(ProcessError::StdinUnavailable)?;
        let stdin_data = stdin.to_vec();
        let stdin_writer = thread::spawn(move || -> Result<(), (ErrorKind, String)> {
            child_stdin.write_all(&stdin_data).map_err(|err| {
                let kind = err.kind();
                (kind, err.to_string())
            })?;
            Ok(())
        });

        let mut child_stdout = child.stdout.take().ok_or(ProcessError::StdoutUnavailable)?;
        let stdout_reader = thread::spawn(move || -> Result<Vec<u8>, String> {
            let mut buf = Vec::new();
            child_stdout
                .read_to_end(&mut buf)
                .map_err(|err| err.to_string())?;
            Ok(buf)
        });

        let mut child_stderr = child.stderr.take().ok_or(ProcessError::StderrUnavailable)?;
        let stderr_reader = thread::spawn(move || -> Result<Vec<u8>, String> {
            let mut buf = Vec::new();
            child_stderr
                .read_to_end(&mut buf)
                .map_err(|err| err.to_string())?;
            Ok(buf)
        });

        let status = loop {
            match child.try_wait() {
                Ok(Some(status)) => break status,
                Ok(None) => {
                    if Instant::now() >= deadline {
                        self.terminate();
                        let _ = stdin_writer.join();
                        let _ = stdout_reader.join();
                        let _ = stderr_reader.join();
                        return Err(ProcessError::Timeout);
                    }
                    self.exit_notification
                        .wait(deadline.saturating_duration_since(Instant::now()));
                }
                Err(err) => {
                    self.terminate();
                    let _ = stdin_writer.join();
                    let _ = stdout_reader.join();
                    let _ = stderr_reader.join();
                    return Err(ProcessError::Wait(err.to_string()));
                }
            }
        };

        match stdin_writer.join() {
            Ok(Ok(())) => {}
            Ok(Err((ErrorKind::BrokenPipe, _))) => {}
            Ok(Err((_, err))) => return Err(ProcessError::StdinWrite(err)),
            Err(_) => return Err(ProcessError::StdinThreadPanic),
        }
        let stdout = match stdout_reader.join() {
            Ok(Ok(buf)) => buf,
            Ok(Err(err)) => return Err(ProcessError::StdoutRead(err)),
            Err(_) => return Err(ProcessError::StdoutThreadPanic),
        };
        let stderr = match stderr_reader.join() {
            Ok(Ok(buf)) => buf,
            Ok(Err(err)) => return Err(ProcessError::StderrRead(err)),
            Err(_) => return Err(ProcessError::StderrThreadPanic),
        };
        self.child.take();

        Ok(ProcessOutput {
            status,
            stdout,
            stderr,
        })
    }

    fn terminate(&mut self) {
        if let Some(mut child) = self.child.take() {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

impl Drop for PreparedProcess {
    fn drop(&mut self) {
        self.terminate();
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::{run_command_with_timeout_and_input, PreparedProcess, ProcessError};
    use std::process::Command;
    use std::time::{Duration, Instant};

    // A normal binary stream larger than pipe capacity is collected byte-for-byte.
    #[test]
    fn large_binary_stream_is_preserved() {
        let input: Vec<u8> = (0..262_144).map(|index| (index % 256) as u8).collect();
        let output = run_command_with_timeout_and_input(
            &mut Command::new("/bin/cat"),
            &input,
            Duration::from_secs(5),
        )
        .unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, input);
        assert!(output.stderr.is_empty());
    }

    // A failing child retains its real diagnostic bytes and nonzero exit status.
    #[test]
    fn error_output_and_exit_are_preserved() {
        let output = run_command_with_timeout_and_input(
            Command::new("/bin/sh").args(["-c", "printf diagnostic >&2; exit 7"]),
            &[],
            Duration::from_secs(5),
        )
        .unwrap();
        assert_eq!(output.status.code(), Some(7));
        assert_eq!(output.stderr, b"diagnostic");
        assert!(output.stdout.is_empty());
    }

    // A child that exits before consuming a large input still reports its successful status.
    #[test]
    fn early_exit_does_not_turn_broken_pipe_into_failure() {
        let output = run_command_with_timeout_and_input(
            &mut Command::new("/bin/true"),
            &vec![255; 262_144],
            Duration::from_secs(5),
        )
        .unwrap();
        assert!(output.status.success());
        assert!(output.stdout.is_empty());
        assert!(output.stderr.is_empty());
    }

    // A child exceeding its deadline is terminated and reaped instead of reported as completed.
    #[test]
    fn deadline_terminates_and_reaps_child() {
        let child = PreparedProcess::spawn(Command::new("/bin/sleep").arg("10")).unwrap();
        let started = Instant::now();
        let result = child.collect(&[], Duration::from_millis(30));
        assert!(matches!(result, Err(ProcessError::Timeout)));
        assert!(started.elapsed() >= Duration::from_millis(30));
        assert!(started.elapsed() < Duration::from_secs(5));
    }

    // A descendant retaining stdout cannot extend collection past the direct child's deadline.
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    #[test]
    fn descendant_writer_does_not_block_collection_after_child_exit() {
        let child = PreparedProcess::spawn(
            Command::new("/bin/sh").args(["-c", "sleep 2 & printf ready; exit 0"]),
        )
        .unwrap();
        let started = Instant::now();
        let result = child.collect_with_channels(&[], Duration::from_millis(100), Vec::new());
        assert_eq!(result.status.unwrap().code(), Some(0));
        assert_eq!(result.stdout, b"ready");
        assert!(result
            .errors
            .iter()
            .any(|error| matches!(error, ProcessError::Timeout)));
        assert!(started.elapsed() < Duration::from_secs(1));
    }

    // A descendant retaining stdin cannot trap a large write after the direct child exits.
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    #[test]
    fn descendant_reader_does_not_block_input_after_child_exit() {
        let child = PreparedProcess::spawn(Command::new("python3").args([
            "-c",
            "import os,time\nif os.fork(): os._exit(0)\nos.close(1)\nos.close(2)\ntime.sleep(2)\nos._exit(0)",
        ]))
        .unwrap();
        let started = Instant::now();
        let result =
            child.collect_with_channels(&vec![7; 262_144], Duration::from_millis(100), Vec::new());
        assert_eq!(result.status.unwrap().code(), Some(0));
        assert!(result
            .errors
            .iter()
            .any(|error| matches!(error, ProcessError::Timeout)));
        assert!(started.elapsed() < Duration::from_secs(1));
    }

    // An already-spawned child is reaped with a structured error for an unrepresentable deadline.
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    #[test]
    fn invalid_deadline_retains_cleanup_status() {
        use std::os::unix::process::ExitStatusExt;
        let child = PreparedProcess::spawn(Command::new("/bin/sleep").arg("10")).unwrap();
        let result = child.collect_with_channels(&[], Duration::from_secs(u64::MAX), Vec::new());
        assert_eq!(result.errors.len(), 1);
        assert!(matches!(result.errors[0], ProcessError::InvalidTimeout));
        assert_eq!(result.status.unwrap().signal(), Some(9));
    }

    // A failed additional-channel write retains its channel identity and the child's real exit.
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    #[test]
    fn additional_write_error_retains_child_status() {
        let sink = std::fs::OpenOptions::new()
            .write(true)
            .open("/dev/full")
            .unwrap();
        let child = PreparedProcess::spawn(&mut Command::new("/bin/true")).unwrap();
        let result = child.collect_with_channels(
            &[],
            Duration::from_secs(5),
            vec![super::ProcessChannel {
                name: "control".into(),
                file: sink,
                input: Some(vec![1]),
            }],
        );
        assert_eq!(result.status.unwrap().code(), Some(0));
        assert_eq!(result.errors.len(), 1);
        assert!(
            matches!(&result.errors[0], ProcessError::Channel { name, message }
            if name == "control" && message.contains("os error 28"))
        );
    }

    // Independent child notifications never exchange outputs or exit statuses.
    #[test]
    fn concurrent_children_keep_their_own_outputs() {
        let workers: Vec<_> = (0..8)
            .map(|index| {
                std::thread::spawn(move || {
                    let input = vec![index; 8_192];
                    let output = run_command_with_timeout_and_input(
                        &mut Command::new("/bin/cat"),
                        &input,
                        Duration::from_secs(5),
                    )
                    .unwrap();
                    assert!(output.status.success());
                    assert_eq!(output.stdout, input);
                    assert!(output.stderr.is_empty());
                })
            })
            .collect();
        for worker in workers {
            worker.join().unwrap();
        }
    }
}
