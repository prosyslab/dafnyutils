use crate::utils::cli::StartupRunArgs;

#[cfg(not(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu")))]
pub(crate) fn run_startup(_args: StartupRunArgs) -> Result<(), String> {
    Err("native startup capabilities require Linux x86_64/glibc".into())
}

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
pub(crate) use linux::run_startup;

#[cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
mod linux {
    use super::StartupRunArgs;
    use crate::fuzz::execution::{pipe_cloexec, set_cloexec_io};
    use crate::fuzz::process_outcome::Termination;
    use crate::utils::cli::ExecKind;
    use crate::utils::process::{
        validate_timeout, PreparedProcess, ProcessChannel, ProcessCollection,
    };
    use crate::utils::startup_protocol::{
        decode_events, ObservedPipeDisposition, PipeDisposition, StartupControl, StartupEvent,
        StartupProfile, CONTROL_ENV,
    };
    use serde::Serialize;
    use std::ffi::OsString;
    use std::fs::{self, File};
    use std::io;
    use std::os::fd::{AsRawFd, OwnedFd};
    use std::os::unix::ffi::{OsStrExt, OsStringExt};
    use std::os::unix::net::UnixStream;
    use std::os::unix::process::CommandExt;
    use std::process::Command;
    use std::time::Duration;

    unsafe extern "C" {
        fn fcntl(fd: i32, command: i32, ...) -> i32;
        fn dup3(old: i32, new: i32, flags: i32) -> i32;
        fn dup2(old: i32, new: i32) -> i32;
        fn close(fd: i32) -> i32;
        fn write(fd: i32, bytes: *const u8, count: usize) -> isize;
        fn sigaction(signal: i32, action: *const SignalAction, previous: *mut SignalAction) -> i32;
    }

    // glibc Linux x86_64 struct sigaction from bits/sigaction.h and
    // bits/types/__sigset_t.h. This module is gated to that ABI.
    #[repr(C)]
    struct SignalAction {
        handler: usize,
        mask: [usize; 16],
        flags: i32,
        restorer: usize,
    }

    impl SignalAction {
        fn for_pipe(disposition: PipeDisposition) -> Self {
            Self {
                handler: match disposition {
                    PipeDisposition::Default => 0, // SIG_DFL
                    PipeDisposition::Ignored => 1, // SIG_IGN
                },
                mask: [0; 16],
                flags: 0,
                restorer: 0,
            }
        }

        // sigaction is async-signal-safe and does not change the thread's mask.
        fn install_pipe(&self) -> io::Result<()> {
            if unsafe { sigaction(13, self, std::ptr::null_mut()) } < 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        }
    }

    struct EarlyTransfer {
        profile: StartupProfile,
        launch_id: u64,
        slots: [i32; 3],
        runtime: [i32; 3],
        writer: i32,
        inherited: [i32; 5],
    }

    impl EarlyTransfer {
        /// Called only in the prepared child before exec. No allocation, locking,
        /// environment processing or runtime-owned descriptor discovery occurs here.
        fn prepare(&self) -> io::Result<()> {
            let mut record = [0u8; 64];
            record[..8].copy_from_slice(b"DFYSEAR2");
            record[8..12].copy_from_slice(&2u32.to_le_bytes());
            record[12..16].copy_from_slice(&64u32.to_le_bytes());
            record[16..24].copy_from_slice(&self.launch_id.to_le_bytes());
            record[60..64].copy_from_slice(&self.profile.wire().to_le_bytes());
            for (role, slot) in self.slots.iter().enumerate() {
                let flags = unsafe { fcntl(role as i32, 1) }; // F_GETFD
                let state = if flags < 0 {
                    let error = io::Error::last_os_error();
                    if error.raw_os_error() != Some(9) {
                        return Err(error);
                    }
                    0u32
                } else if flags & 1 != 0 {
                    // FD_CLOEXEC does not survive the intended exec.
                    2
                } else {
                    1
                };
                let fd = match (self.profile, state) {
                    (StartupProfile::ManagedTransfer, 1) => {
                        if unsafe { dup3(role as i32, *slot, 0) } < 0 {
                            return Err(io::Error::last_os_error());
                        }
                        *slot
                    }
                    (StartupProfile::ManagedTransfer, _) => {
                        if unsafe { close(*slot) } < 0 {
                            return Err(io::Error::last_os_error());
                        }
                        -1
                    }
                    (StartupProfile::NativeReference, 1) => role as i32,
                    (StartupProfile::NativeReference, _) => -1,
                };
                let offset = 24 + role * 12;
                record[offset..offset + 4].copy_from_slice(&state.to_le_bytes());
                record[offset + 4..offset + 8].copy_from_slice(&fd.to_le_bytes());
                record[offset + 8..offset + 12]
                    .copy_from_slice(&(if state == 1 { 0u32 } else { 9 }).to_le_bytes());
            }
            for fd in self.inherited {
                set_cloexec_io(fd, false)?;
            }
            let mut written = 0;
            while written < record.len() {
                let count = unsafe {
                    write(
                        self.writer,
                        record[written..].as_ptr(),
                        record.len() - written,
                    )
                };
                if count < 0 {
                    let error = io::Error::last_os_error();
                    if error.kind() == io::ErrorKind::Interrupted {
                        continue;
                    }
                    return Err(error);
                }
                if count == 0 {
                    return Err(io::Error::from(io::ErrorKind::WriteZero));
                }
                written += count as usize;
            }
            if unsafe { close(self.writer) } < 0 {
                return Err(io::Error::last_os_error());
            }
            if self.profile == StartupProfile::ManagedTransfer {
                for (role, fd) in self.runtime.iter().enumerate() {
                    if unsafe { dup2(*fd, role as i32) } < 0 {
                        return Err(io::Error::last_os_error());
                    }
                }
            }
            Ok(())
        }
    }

    #[derive(Serialize)]
    #[serde(rename_all = "snake_case")]
    enum CapturePhase {
        BeforeExec,
        AfterLoaderBeforeRuntimeMain,
        AfterSharedObjectInitializersBeforeExecutableInitializers,
        AfterExecutableInitializersBeforeNativeMain,
    }

    #[derive(Serialize)]
    #[serde(rename_all = "snake_case")]
    enum StreamScope {
        WholeTargetProcess,
    }

    #[derive(Serialize)]
    #[serde(rename_all = "snake_case")]
    enum PhaseAttribution {
        Unavailable,
    }

    #[derive(Serialize)]
    #[serde(rename_all = "snake_case")]
    enum RuntimeChannelRole {
        PrivateStartupTransport,
    }

    #[derive(Serialize)]
    struct StartupProtocolProfile {
        version: u32,
        standard_availability_phase: CapturePhase,
        status_signal_resource_phase: CapturePhase,
        requested_sigpipe: PipeDisposition,
        #[serde(skip_serializing_if = "Option::is_none")]
        profile: Option<StartupProfile>,
        #[serde(skip_serializing_if = "Option::is_none")]
        standard_source_phase: Option<CapturePhase>,
        #[serde(skip_serializing_if = "Option::is_none")]
        utility_entry_phase: Option<CapturePhase>,
        #[serde(skip_serializing_if = "Option::is_none")]
        reference_stream_scope: Option<StreamScope>,
        #[serde(skip_serializing_if = "Option::is_none")]
        reference_stream_phase_attribution: Option<PhaseAttribution>,
        #[serde(skip_serializing_if = "Option::is_none")]
        runtime_channel_role: Option<RuntimeChannelRole>,
    }

    #[derive(Serialize)]
    struct StartupReport<'a> {
        schema_version: u32,
        startup_protocol: StartupProtocolProfile,
        launch_id: u64,
        process_id: Option<u32>,
        target_bytes: &'a [u8],
        #[serde(skip_serializing_if = "Option::is_none")]
        argv0_bytes: Option<&'a [u8]>,
        exec_kind: ExecKind,
        argv_bytes: Vec<&'a [u8]>,
        termination: Option<Termination>,
        collection_errors: &'a [crate::utils::process::ProcessError],
        events: Option<Vec<StartupEvent>>,
        protocol_error: Option<String>,
        startup_complete: bool,
    }

    fn validate_lifecycle(
        events: &[StartupEvent],
        pid: u32,
        requested_sigpipe: PipeDisposition,
        profile: StartupProfile,
    ) -> Result<(), String> {
        match events {
            [StartupEvent::BootstrapReady(ready), StartupEvent::UtilityEntered(entry)] => {
                if ready.process_id != pid || entry.process_id != pid {
                    return Err(
                        "startup event process identity differs from the owned child".into(),
                    );
                }
                let requested = match requested_sigpipe {
                    PipeDisposition::Default => ObservedPipeDisposition::Default,
                    PipeDisposition::Ignored => ObservedPipeDisposition::Ignored,
                };
                if profile == StartupProfile::ManagedTransfer
                    && (ready.sigpipe != requested || entry.sigpipe != requested)
                {
                    return Err(
                        "observed SIGPIPE disposition differs from the requested target policy"
                            .into(),
                    );
                }
                if profile == StartupProfile::ManagedTransfer
                    && (entry.sigpipe != ready.sigpipe
                        || entry.sigpipe_blocked != ready.sigpipe_blocked)
                {
                    return Err("utility entry did not restore the captured SIGPIPE policy".into());
                }
                match (profile, entry.standards.as_ref()) {
                    (StartupProfile::ManagedTransfer, None) => {}
                    (StartupProfile::NativeReference, Some(standards))
                        if standards.len() == 3
                            && standards
                                .iter()
                                .enumerate()
                                .all(|(role, standard)| standard.role == role as u32) => {}
                    _ => return Err("utility entry payload does not match startup profile".into()),
                }
                Ok(())
            }
            [StartupEvent::BootstrapError(error)] => {
                Err(format!("native bootstrap failed: {error:?}"))
            }
            [StartupEvent::BootstrapReady(_), StartupEvent::UtilityEntryError(error)] => {
                Err(format!("native utility entry failed: {error:?}"))
            }
            [] => Err("native bootstrap readiness is missing".into()),
            [StartupEvent::BootstrapReady(_)] => Err("explicit utility entry is missing".into()),
            _ => Err("invalid startup event order or duplicate lifecycle event".into()),
        }
    }

    pub(crate) fn run_startup(args: StartupRunArgs) -> Result<(), String> {
        let timeout = Duration::from_secs(args.process_timeout_seconds);
        validate_timeout(timeout)
            .map_err(|_| "startup timeout exceeds the platform clock range")?;
        if args.startup_profile == StartupProfile::NativeReference
            && args.exec_kind != ExecKind::Native
        {
            return Err("native-reference startup requires a native target".into());
        }
        let target = fs::canonicalize(&args.target)
            .map_err(|error| format!("cannot resolve startup target: {error}"))?;
        let library = fs::canonicalize(&args.startup_library)
            .map_err(|error| format!("cannot resolve startup library: {error}"))?;
        let library_bytes = library.as_os_str().as_bytes();
        if library_bytes
            .iter()
            .any(|byte| matches!(byte, b':' | b' ' | b'\t' | b'\n'))
        {
            return Err("startup library path contains an LD_PRELOAD list separator".into());
        }
        let input = fs::read(&args.stdin_file)
            .map_err(|error| format!("cannot read startup input: {error}"))?;
        let (control_reader, control_writer) = pipe_cloexec()
            .map_err(|error| format!("cannot create startup control pipe: {error}"))?;
        let (runtime_stdout_reader, runtime_stdout_writer) = pipe_cloexec()
            .map_err(|error| format!("cannot create runtime stdout pipe: {error}"))?;
        let (runtime_stderr_reader, runtime_stderr_writer) = pipe_cloexec()
            .map_err(|error| format!("cannot create runtime stderr pipe: {error}"))?;
        let (observer_reader, observer_writer) = UnixStream::pair()
            .map_err(|error| format!("cannot create startup observer socket: {error}"))?;
        let (early_reader, early_writer) = pipe_cloexec()
            .map_err(|error| format!("cannot create early startup record pipe: {error}"))?;
        let reserve = || {
            File::open("/dev/null")
                .map_err(|error| format!("cannot reserve early startup descriptor: {error}"))
        };
        let slots = [reserve()?, reserve()?, reserve()?];
        let runtime_stdin = reserve()?;
        let original_preload = std::env::var_os("LD_PRELOAD");
        let original_control = std::env::var_os(CONTROL_ENV);
        let launch_id = rand::random();
        let control_fd = control_reader.as_raw_fd();
        let control = StartupControl {
            profile: args.startup_profile,
            runtime_stdout_fd: runtime_stdout_writer.as_raw_fd(),
            runtime_stderr_fd: runtime_stderr_writer.as_raw_fd(),
            observer_fd: observer_writer.as_raw_fd(),
            early_record_fd: early_reader.as_raw_fd(),
            original_preload: original_preload.as_deref().map(OsStrExt::as_bytes),
            original_control: original_control.as_deref().map(OsStrExt::as_bytes),
            launch_id,
        }
        .encode(control_fd)?;
        let mut preload = library_bytes.to_vec();
        if let Some(original) = &original_preload {
            if !original.is_empty() {
                preload.push(b':');
                preload.extend_from_slice(original.as_bytes());
            }
        }
        let mut command = match args.exec_kind {
            ExecKind::Native => {
                let mut command = Command::new(&target);
                if args.startup_profile == StartupProfile::NativeReference {
                    command.arg0(&args.target);
                }
                command
            }
            ExecKind::DotnetDll => {
                let mut command = Command::new("dotnet");
                command.arg(&target);
                command
            }
        };
        command
            .args(&args.argv)
            .env("LD_PRELOAD", OsString::from_vec(preload))
            .env(CONTROL_ENV, control_fd.to_string());
        let transfer = EarlyTransfer {
            profile: args.startup_profile,
            launch_id,
            slots: slots.each_ref().map(AsRawFd::as_raw_fd),
            runtime: [
                runtime_stdin.as_raw_fd(),
                runtime_stdout_writer.as_raw_fd(),
                runtime_stderr_writer.as_raw_fd(),
            ],
            writer: early_writer.as_raw_fd(),
            inherited: [
                control_fd,
                runtime_stdout_writer.as_raw_fd(),
                runtime_stderr_writer.as_raw_fd(),
                observer_writer.as_raw_fd(),
                early_reader.as_raw_fd(),
            ],
        };
        let signal_action = SignalAction::for_pipe(args.sigpipe);
        // Every endpoint stays owned and CLOEXEC in the parent; only this child's
        // reserved capabilities and private channels cross its exec boundary.
        unsafe {
            command.pre_exec(move || {
                // Command resets SIGPIPE first; install the requested target
                // disposition here without changing its inherited blocked mask.
                signal_action.install_pipe()?;
                transfer.prepare()
            });
        }
        fs::create_dir(&args.result_dir)
            .map_err(|error| format!("cannot create fresh startup result directory: {error}"))?;
        let child = PreparedProcess::spawn(&mut command);
        drop((
            control_reader,
            runtime_stdout_writer,
            runtime_stderr_writer,
            observer_writer,
            early_reader,
            early_writer,
            slots,
            runtime_stdin,
        ));
        let (pid, result) = match child {
            Ok(child) => {
                let pid = child.id();
                let result = child.collect_with_channels(
                    &input,
                    timeout,
                    vec![
                        ProcessChannel {
                            name: "control".into(),
                            file: control_writer,
                            input: Some(control),
                        },
                        ProcessChannel {
                            name: "runtime.stdout".into(),
                            file: runtime_stdout_reader,
                            input: None,
                        },
                        ProcessChannel {
                            name: "runtime.stderr".into(),
                            file: runtime_stderr_reader,
                            input: None,
                        },
                        ProcessChannel {
                            name: "observer.bin".into(),
                            file: File::from(OwnedFd::from(observer_reader)),
                            input: None,
                        },
                    ],
                );
                (Some(pid), result)
            }
            Err(error) => (
                None,
                ProcessCollection {
                    errors: vec![error],
                    ..Default::default()
                },
            ),
        };
        let channel = |name: &str| {
            result
                .channels
                .iter()
                .find(|channel| channel.name == name)
                .map(|channel| channel.bytes.as_slice())
                .unwrap_or_default()
        };
        let (stdout_name, stderr_name) = match args.startup_profile {
            StartupProfile::ManagedTransfer => ("utility.stdout", "utility.stderr"),
            StartupProfile::NativeReference => ("reference.stdout", "reference.stderr"),
        };
        for (name, bytes) in [
            (stdout_name, result.stdout.as_slice()),
            (stderr_name, result.stderr.as_slice()),
            ("runtime.stdout", channel("runtime.stdout")),
            ("runtime.stderr", channel("runtime.stderr")),
            ("observer.bin", channel("observer.bin")),
        ] {
            fs::write(args.result_dir.join(name), bytes)
                .map_err(|error| format!("cannot write startup artifact {name}: {error}"))?;
        }
        let (events, protocol_error) =
            match decode_events(channel("observer.bin"), launch_id, args.startup_profile) {
                Ok(events) => {
                    let error = pid.map_or_else(
                        || Some("target did not start".into()),
                        |pid| {
                            validate_lifecycle(&events, pid, args.sigpipe, args.startup_profile)
                                .err()
                        },
                    );
                    (Some(events), error)
                }
                Err(error) => (None, Some(error)),
            };
        let startup_complete = result.errors.is_empty() && protocol_error.is_none();
        let report = StartupReport {
            schema_version: match args.startup_profile {
                StartupProfile::ManagedTransfer => 2,
                StartupProfile::NativeReference => 3,
            },
            startup_protocol: StartupProtocolProfile {
                version: 2,
                standard_availability_phase: match args.startup_profile {
                    StartupProfile::ManagedTransfer => CapturePhase::BeforeExec,
                    StartupProfile::NativeReference => {
                        CapturePhase::AfterSharedObjectInitializersBeforeExecutableInitializers
                    }
                },
                status_signal_resource_phase: match args.startup_profile {
                    StartupProfile::ManagedTransfer => CapturePhase::AfterLoaderBeforeRuntimeMain,
                    StartupProfile::NativeReference => {
                        CapturePhase::AfterSharedObjectInitializersBeforeExecutableInitializers
                    }
                },
                requested_sigpipe: args.sigpipe,
                profile: (args.startup_profile == StartupProfile::NativeReference)
                    .then_some(args.startup_profile),
                standard_source_phase: (args.startup_profile == StartupProfile::NativeReference)
                    .then_some(CapturePhase::BeforeExec),
                utility_entry_phase: (args.startup_profile == StartupProfile::NativeReference)
                    .then_some(CapturePhase::AfterExecutableInitializersBeforeNativeMain),
                reference_stream_scope: (args.startup_profile == StartupProfile::NativeReference)
                    .then_some(StreamScope::WholeTargetProcess),
                reference_stream_phase_attribution: (args.startup_profile
                    == StartupProfile::NativeReference)
                    .then_some(PhaseAttribution::Unavailable),
                runtime_channel_role: (args.startup_profile == StartupProfile::NativeReference)
                    .then_some(RuntimeChannelRole::PrivateStartupTransport),
            },
            launch_id,
            process_id: pid,
            target_bytes: target.as_os_str().as_bytes(),
            argv0_bytes: (args.startup_profile == StartupProfile::NativeReference)
                .then_some(args.target.as_os_str().as_bytes()),
            exec_kind: args.exec_kind,
            argv_bytes: args.argv.iter().map(|arg| arg.as_bytes()).collect(),
            termination: result.status.map(Termination::from_status),
            collection_errors: &result.errors,
            events,
            protocol_error,
            startup_complete,
        };
        let json = serde_json::to_vec_pretty(&report)
            .map_err(|error| format!("cannot serialize startup report: {error}"))?;
        fs::write(args.result_dir.join("startup.json"), json)
            .map_err(|error| format!("cannot write startup report: {error}"))?;
        if startup_complete {
            Ok(())
        } else {
            Err(format!(
                "startup collection failed; see {}",
                args.result_dir.join("startup.json").display()
            ))
        }
    }
    #[cfg(test)]
    mod tests {
        use super::validate_lifecycle;
        use crate::utils::startup_protocol::{
            EntryStandardObservation, ObservedPipeDisposition, PipeDisposition, StartupEvent,
            StartupProfile, StartupSnapshot, UtilityEntry,
        };

        fn lifecycle() -> [StartupEvent; 2] {
            [
                StartupEvent::BootstrapReady(StartupSnapshot {
                    process_id: 123,
                    initial_thread_id: 123,
                    sigpipe: ObservedPipeDisposition::Default,
                    sigpipe_blocked: false,
                    sigpipe_pending: false,
                    standards: Vec::new(),
                    resources: Vec::new(),
                }),
                StartupEvent::UtilityEntered(UtilityEntry {
                    process_id: 123,
                    thread_id: 123,
                    sigpipe: ObservedPipeDisposition::Default,
                    sigpipe_blocked: false,
                    standards: None,
                }),
            ]
        }

        // A duplicated entry event cannot establish a valid one-time startup lifecycle.
        #[test]
        fn duplicate_utility_entry_is_rejected() {
            let [ready, entry] = lifecycle();
            assert!(validate_lifecycle(
                &[ready, entry.clone(), entry],
                123,
                PipeDisposition::Default,
                StartupProfile::ManagedTransfer,
            )
            .is_err());
        }

        // Entry before readiness is not accepted even when both records have the right process.
        #[test]
        fn entry_before_readiness_is_rejected() {
            let [ready, entry] = lifecycle();
            assert!(validate_lifecycle(
                &[entry, ready],
                123,
                PipeDisposition::Default,
                StartupProfile::ManagedTransfer,
            )
            .is_err());
        }

        // Correctly ordered observations from a different child do not satisfy this launch.
        #[test]
        fn another_process_identity_is_rejected() {
            assert!(validate_lifecycle(
                &lifecycle(),
                456,
                PipeDisposition::Default,
                StartupProfile::ManagedTransfer,
            )
            .is_err());
        }

        // Consistent capture and entry cannot hide a different requested launch policy.
        #[test]
        fn captured_default_rejects_requested_ignored() {
            let error = validate_lifecycle(
                &lifecycle(),
                123,
                PipeDisposition::Ignored,
                StartupProfile::ManagedTransfer,
            )
            .unwrap_err();
            assert_eq!(
                error,
                "observed SIGPIPE disposition differs from the requested target policy"
            );
        }

        // A matching bootstrap cannot hide a disposition changed by runtime initialization.
        #[test]
        fn entry_disposition_must_match_requested_policy() {
            let mut events = lifecycle();
            if let StartupEvent::UtilityEntered(entry) = &mut events[1] {
                entry.sigpipe = ObservedPipeDisposition::Ignored;
            }
            let error = validate_lifecycle(
                &events,
                123,
                PipeDisposition::Default,
                StartupProfile::ManagedTransfer,
            )
            .unwrap_err();
            assert_eq!(
                error,
                "observed SIGPIPE disposition differs from the requested target policy"
            );
        }

        // Reference entry records constructor changes without rejecting or rewriting them.
        #[test]
        fn reference_lifecycle_accepts_constructor_signal_change() {
            let mut events = lifecycle();
            if let StartupEvent::UtilityEntered(entry) = &mut events[1] {
                entry.sigpipe = ObservedPipeDisposition::Custom;
                entry.standards = Some(
                    (0..3)
                        .map(|role| EntryStandardObservation {
                            role,
                            available: true,
                            availability_errno: 0,
                        })
                        .collect(),
                );
            }
            assert!(validate_lifecycle(
                &events,
                123,
                PipeDisposition::Default,
                StartupProfile::NativeReference,
            )
            .is_ok());
        }

        // Exhausting the child's descriptor range reports the real early dup3 error before exec.
        #[test]
        fn early_transfer_reports_descriptor_limit_failure() {
            use super::{pipe_cloexec, EarlyTransfer, File, PreparedProcess, UnixStream};
            use crate::utils::process::ProcessError;
            use std::os::fd::AsRawFd;
            use std::os::unix::process::CommandExt;
            use std::process::Command;

            #[repr(C)]
            struct Limits {
                soft: u64,
                hard: u64,
            }
            unsafe extern "C" {
                fn setrlimit(resource: i32, value: *const Limits) -> i32;
            }
            let slots = [
                File::open("/dev/null").unwrap(),
                File::open("/dev/null").unwrap(),
                File::open("/dev/null").unwrap(),
            ];
            let runtime_stdin = File::open("/dev/null").unwrap();
            let (control_read, _control_write) = pipe_cloexec().unwrap();
            let (_out_read, out_write) = pipe_cloexec().unwrap();
            let (_err_read, err_write) = pipe_cloexec().unwrap();
            let (early_read, early_write) = pipe_cloexec().unwrap();
            let (_observer_read, observer_write) = UnixStream::pair().unwrap();
            let transfer = EarlyTransfer {
                profile: StartupProfile::ManagedTransfer,
                launch_id: 1,
                slots: slots.each_ref().map(AsRawFd::as_raw_fd),
                runtime: [
                    runtime_stdin.as_raw_fd(),
                    out_write.as_raw_fd(),
                    err_write.as_raw_fd(),
                ],
                writer: early_write.as_raw_fd(),
                inherited: [
                    control_read.as_raw_fd(),
                    out_write.as_raw_fd(),
                    err_write.as_raw_fd(),
                    observer_write.as_raw_fd(),
                    early_read.as_raw_fd(),
                ],
            };
            let mut command = Command::new("/bin/true");
            unsafe {
                command.pre_exec(move || {
                    if setrlimit(7, &Limits { soft: 3, hard: 3 }) < 0 {
                        return Err(std::io::Error::last_os_error());
                    }
                    transfer.prepare()
                });
            }
            assert!(matches!(PreparedProcess::spawn(&mut command),
                Err(ProcessError::Spawn(message)) if message.contains("os error 9")));
        }
    }
}
