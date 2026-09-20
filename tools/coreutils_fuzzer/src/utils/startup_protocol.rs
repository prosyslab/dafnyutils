use serde::Serialize;

pub(crate) const CONTROL_ENV: &str = "DAFNYUTILS_STARTUP_FD";
const CONTROL_BYTES: usize = 72;
const EVENT_HEADER_BYTES: usize = 32;
const READY_BYTES: usize = 1024;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Serialize, clap::ValueEnum)]
#[serde(rename_all = "snake_case")]
pub(crate) enum StartupProfile {
    #[default]
    ManagedTransfer,
    NativeReference,
}

impl StartupProfile {
    pub(crate) fn wire(self) -> u32 {
        match self {
            Self::ManagedTransfer => 0,
            Self::NativeReference => 1,
        }
    }
}

pub(crate) struct StartupControl<'a> {
    pub(crate) profile: StartupProfile,
    pub(crate) runtime_stdout_fd: i32,
    pub(crate) runtime_stderr_fd: i32,
    pub(crate) observer_fd: i32,
    pub(crate) early_record_fd: i32,
    pub(crate) original_preload: Option<&'a [u8]>,
    pub(crate) original_control: Option<&'a [u8]>,
    pub(crate) launch_id: u64,
}

impl StartupControl<'_> {
    pub(crate) fn encode(&self, control_fd: i32) -> Result<Vec<u8>, String> {
        let fds = [
            control_fd,
            self.runtime_stdout_fd,
            self.runtime_stderr_fd,
            self.observer_fd,
            self.early_record_fd,
        ];
        for (index, fd) in fds.iter().enumerate() {
            if *fd < 3 || fds[..index].contains(fd) {
                return Err("startup channels require distinct descriptors at least 3".into());
            }
        }
        let preload = self.original_preload.unwrap_or_default();
        let control = self.original_control.unwrap_or_default();
        if preload.contains(&0) || control.contains(&0) {
            return Err("startup environment values cannot contain NUL".into());
        }
        let length = CONTROL_BYTES
            .checked_add(preload.len())
            .and_then(|n| n.checked_add(control.len()))
            .and_then(|n| u32::try_from(n).ok())
            .ok_or("startup control record exceeds its length representation")?;
        let mut bytes = vec![0; CONTROL_BYTES];
        bytes[..8].copy_from_slice(b"DFYSTRT2");
        put32(&mut bytes, 8, 2);
        put32(&mut bytes, 12, CONTROL_BYTES as u32);
        put32(&mut bytes, 16, length);
        put32(&mut bytes, 20, self.runtime_stdout_fd as u32);
        put32(&mut bytes, 24, self.runtime_stderr_fd as u32);
        put32(&mut bytes, 28, self.observer_fd as u32);
        put32(&mut bytes, 32, self.original_preload.is_some() as u32);
        put32(&mut bytes, 36, preload.len() as u32);
        put32(&mut bytes, 40, self.original_control.is_some() as u32);
        put32(&mut bytes, 44, control.len() as u32);
        put32(&mut bytes, 48, self.profile.wire());
        bytes[56..64].copy_from_slice(&self.launch_id.to_le_bytes());
        put32(&mut bytes, 64, self.early_record_fd as u32);
        bytes.extend_from_slice(preload);
        bytes.extend_from_slice(control);
        Ok(bytes)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct NativeStat {
    pub(crate) device: u64,
    pub(crate) inode: u64,
    pub(crate) special_device: u64,
    pub(crate) size: i64,
    pub(crate) allocated_512_blocks: i64,
    pub(crate) preferred_io_block_bytes: i64,
    pub(crate) links: u64,
    pub(crate) mode: u32,
    pub(crate) uid: u32,
    pub(crate) gid: u32,
    pub(crate) atime_seconds: i64,
    pub(crate) atime_nanoseconds: i64,
    pub(crate) mtime_seconds: i64,
    pub(crate) mtime_nanoseconds: i64,
    pub(crate) ctime_seconds: i64,
    pub(crate) ctime_nanoseconds: i64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct StandardCapability {
    pub(crate) role: u32,
    pub(crate) source_state: StandardSourceState,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) private_fd: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) native_role: Option<u32>,
    pub(crate) status_flags: u32,
    pub(crate) availability_errno: u32,
    pub(crate) stat_errno: u32,
    pub(crate) stat: Option<NativeStat>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum StandardSourceState {
    Closed,
    Inherited,
    CloseOnExec,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", content = "value", rename_all = "snake_case")]
pub(crate) enum ResourceLimit {
    Finite(u64),
    Infinite,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct ResourceObservation {
    pub(crate) resource: u32,
    pub(crate) errno: u32,
    pub(crate) soft: Option<ResourceLimit>,
    pub(crate) hard: Option<ResourceLimit>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, clap::ValueEnum)]
#[serde(rename_all = "snake_case")]
pub(crate) enum PipeDisposition {
    Default,
    Ignored,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ObservedPipeDisposition {
    Default,
    Ignored,
    Custom,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct StartupSnapshot {
    pub(crate) process_id: u32,
    pub(crate) initial_thread_id: u32,
    pub(crate) sigpipe: ObservedPipeDisposition,
    pub(crate) sigpipe_blocked: bool,
    pub(crate) sigpipe_pending: bool,
    pub(crate) standards: Vec<StandardCapability>,
    pub(crate) resources: Vec<ResourceObservation>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum StartupFailureKind {
    Configuration,
    System,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct StartupFailure {
    pub(crate) phase: u32,
    pub(crate) kind: StartupFailureKind,
    pub(crate) code: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct UtilityEntry {
    pub(crate) process_id: u32,
    pub(crate) thread_id: u32,
    pub(crate) sigpipe: ObservedPipeDisposition,
    pub(crate) sigpipe_blocked: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) standards: Option<Vec<EntryStandardObservation>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct EntryStandardObservation {
    pub(crate) role: u32,
    pub(crate) available: bool,
    pub(crate) availability_errno: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", content = "data", rename_all = "snake_case")]
pub(crate) enum StartupEvent {
    BootstrapReady(StartupSnapshot),
    BootstrapError(StartupFailure),
    UtilityEntered(UtilityEntry),
    UtilityEntryError(StartupFailure),
}

fn put32(bytes: &mut [u8], offset: usize, value: u32) {
    bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
}

// Callers first validate the exact fixed record length; these accesses are then bounded.
fn u32_at(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(
        bytes[offset..offset + 4]
            .try_into()
            .expect("fixed u32 field"),
    )
}
fn u64_at(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(
        bytes[offset..offset + 8]
            .try_into()
            .expect("fixed u64 field"),
    )
}
fn zero(bytes: &[u8]) -> bool {
    bytes.iter().all(|byte| *byte == 0)
}
fn bit(value: u32) -> Result<bool, String> {
    match value {
        0 => Ok(false),
        1 => Ok(true),
        _ => Err("invalid startup boolean".into()),
    }
}
fn disposition(value: u32) -> Result<ObservedPipeDisposition, String> {
    match value {
        0 => Ok(ObservedPipeDisposition::Default),
        1 => Ok(ObservedPipeDisposition::Ignored),
        2 => Ok(ObservedPipeDisposition::Custom),
        _ => Err("unsupported SIGPIPE disposition".into()),
    }
}

fn standard(
    bytes: &[u8],
    role: u32,
    profile: StartupProfile,
) -> Result<StandardCapability, String> {
    let available = bit(u32_at(bytes, 4))?;
    let source_state = match u32_at(bytes, 28) {
        0 => StandardSourceState::Closed,
        1 => StandardSourceState::Inherited,
        2 => StandardSourceState::CloseOnExec,
        _ => return Err("invalid pre-exec standard source state".into()),
    };
    let stat_present = bit(u32_at(bytes, 24))?;
    let fd = u32_at(bytes, 8) as i32;
    let flags = u32_at(bytes, 12);
    let availability_errno = u32_at(bytes, 16);
    let stat_errno = u32_at(bytes, 20);
    let binding = u32_at(bytes, 100);
    let binding_valid = binding == profile.wire();
    let available_binding_valid = match profile {
        StartupProfile::ManagedTransfer => fd >= 3,
        StartupProfile::NativeReference => fd == role as i32,
    };
    let source_availability_valid = profile == StartupProfile::NativeReference
        || available == (source_state == StandardSourceState::Inherited);
    if u32_at(bytes, 0) != role
        || !source_availability_valid
        || !binding_valid
        || !zero(&bytes[152..160])
        || (available && (!available_binding_valid || availability_errno != 0))
        || (!available
            && (fd != -1
                || flags != 0
                || availability_errno != 9
                || stat_errno != 9
                || stat_present))
        || (stat_present && stat_errno != 0)
        || (!stat_present && (stat_errno == 0 || !zero(&bytes[32..100]) || !zero(&bytes[104..160])))
    {
        return Err("inconsistent standard capability record".into());
    }
    let stat = stat_present.then(|| NativeStat {
        device: u64_at(bytes, 32),
        inode: u64_at(bytes, 40),
        special_device: u64_at(bytes, 48),
        size: u64_at(bytes, 56) as i64,
        allocated_512_blocks: u64_at(bytes, 64) as i64,
        preferred_io_block_bytes: u64_at(bytes, 72) as i64,
        links: u64_at(bytes, 80),
        mode: u32_at(bytes, 88),
        uid: u32_at(bytes, 92),
        gid: u32_at(bytes, 96),
        atime_seconds: u64_at(bytes, 104) as i64,
        atime_nanoseconds: u64_at(bytes, 112) as i64,
        mtime_seconds: u64_at(bytes, 120) as i64,
        mtime_nanoseconds: u64_at(bytes, 128) as i64,
        ctime_seconds: u64_at(bytes, 136) as i64,
        ctime_nanoseconds: u64_at(bytes, 144) as i64,
    });
    Ok(StandardCapability {
        role,
        source_state,
        private_fd: (profile == StartupProfile::ManagedTransfer && available).then_some(fd),
        native_role: (profile == StartupProfile::NativeReference).then_some(role),
        status_flags: flags,
        availability_errno,
        stat_errno,
        stat,
    })
}

fn resource(bytes: &[u8], id: u32) -> Result<ResourceObservation, String> {
    let errno = u32_at(bytes, 4);
    let soft = u64_at(bytes, 8);
    let hard = u64_at(bytes, 16);
    let flags = u32_at(bytes, 24);
    if u32_at(bytes, 0) != id
        || flags > 3
        || u32_at(bytes, 28) != 0
        || (errno != 0 && (soft != 0 || hard != 0 || flags != 0))
        || (flags & 1 != 0 && soft != 0)
        || (flags & 2 != 0 && hard != 0)
    {
        return Err("inconsistent resource observation".into());
    }
    let limit = |value, infinite| {
        if infinite {
            ResourceLimit::Infinite
        } else {
            ResourceLimit::Finite(value)
        }
    };
    Ok(ResourceObservation {
        resource: id,
        errno,
        soft: (errno == 0).then(|| limit(soft, flags & 1 != 0)),
        hard: (errno == 0).then(|| limit(hard, flags & 2 != 0)),
    })
}

fn snapshot(bytes: &[u8], profile: StartupProfile) -> Result<StartupSnapshot, String> {
    if u32_at(bytes, 0) != 2
        || u32_at(bytes, 16) != 3
        || u32_at(bytes, 20) != 16
        || u32_at(bytes, 4) == 0
        || u32_at(bytes, 24) == 0
    {
        return Err("invalid startup snapshot prefix".into());
    }
    let standards = (0..3)
        .map(|role| {
            let start = 32 + role as usize * 160;
            standard(&bytes[start..start + 160], role, profile)
        })
        .collect::<Result<Vec<_>, _>>()?;
    for (index, capability) in standards.iter().enumerate() {
        if let Some(fd) = capability.private_fd {
            if standards[..index]
                .iter()
                .any(|other| other.private_fd == Some(fd))
            {
                return Err("private standard capabilities share a descriptor number".into());
            }
        }
    }
    let resources = (0..16)
        .map(|id| {
            let start = 512 + id as usize * 32;
            resource(&bytes[start..start + 32], id)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(StartupSnapshot {
        process_id: u32_at(bytes, 4),
        initial_thread_id: u32_at(bytes, 24),
        sigpipe: disposition(u32_at(bytes, 8))?,
        sigpipe_blocked: bit(u32_at(bytes, 12))?,
        sigpipe_pending: bit(u32_at(bytes, 28))?,
        standards,
        resources,
    })
}

fn failure(bytes: &[u8]) -> Result<StartupFailure, String> {
    let phase = u32_at(bytes, 0);
    let code = u32_at(bytes, 8);
    let kind = match u32_at(bytes, 4) {
        1 if (1..=10).contains(&code) => StartupFailureKind::Configuration,
        2 if code > 0 => StartupFailureKind::System,
        _ => return Err("invalid startup failure domain or code".into()),
    };
    if !(1..=7).contains(&phase) || u32_at(bytes, 12) != 0 {
        return Err("invalid startup failure phase or reserved field".into());
    }
    Ok(StartupFailure { phase, kind, code })
}

pub(crate) fn decode_events(
    mut bytes: &[u8],
    launch_id: u64,
    profile: StartupProfile,
) -> Result<Vec<StartupEvent>, String> {
    let mut events = Vec::new();
    while !bytes.is_empty() {
        if bytes.len() < EVENT_HEADER_BYTES {
            return Err("truncated startup event header".into());
        }
        if &bytes[..8] != b"DFYSTEV2"
            || u32_at(bytes, 8) != 2
            || u32_at(bytes, 20) != 0
            || u64_at(bytes, 24) != launch_id
        {
            return Err("invalid startup event header or launch identity".into());
        }
        let kind = u32_at(bytes, 12);
        let size = match kind {
            1 => READY_BYTES,
            2 | 4 => 16,
            3 => match profile {
                StartupProfile::ManagedTransfer => 16,
                StartupProfile::NativeReference => 40,
            },
            _ => return Err("unknown startup event kind".into()),
        };
        if u32_at(bytes, 16) as usize != size || bytes.len() < EVENT_HEADER_BYTES + size {
            return Err("invalid or truncated startup event payload".into());
        }
        let payload = &bytes[EVENT_HEADER_BYTES..EVENT_HEADER_BYTES + size];
        let event = match kind {
            1 => StartupEvent::BootstrapReady(snapshot(payload, profile)?),
            2 => StartupEvent::BootstrapError(failure(payload)?),
            3 => {
                if u32_at(payload, 0) == 0 || u32_at(payload, 4) == 0 {
                    return Err("invalid utility entry identity".into());
                }
                let standards = if profile == StartupProfile::NativeReference {
                    Some(
                        (0..3)
                            .map(|role| {
                                let offset = 16 + role as usize * 8;
                                let available = bit(u32_at(payload, offset))?;
                                let availability_errno = u32_at(payload, offset + 4);
                                if (available && availability_errno != 0)
                                    || (!available && availability_errno != 9)
                                {
                                    return Err("inconsistent utility entry standard".into());
                                }
                                Ok(EntryStandardObservation {
                                    role,
                                    available,
                                    availability_errno,
                                })
                            })
                            .collect::<Result<Vec<_>, String>>()?,
                    )
                } else {
                    None
                };
                StartupEvent::UtilityEntered(UtilityEntry {
                    process_id: u32_at(payload, 0),
                    thread_id: u32_at(payload, 4),
                    sigpipe: disposition(u32_at(payload, 8))?,
                    sigpipe_blocked: bit(u32_at(payload, 12))?,
                    standards,
                })
            }
            4 => StartupEvent::UtilityEntryError(failure(payload)?),
            _ => unreachable!("validated kind"),
        };
        events.push(event);
        bytes = &bytes[EVENT_HEADER_BYTES + size..];
    }
    Ok(events)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Bootstrap transport preserves absence, an empty value and non-UTF8 environment bytes.
    #[test]
    fn control_preserves_environment_bytes() {
        for preload in [None, Some(&b""[..]), Some(&b"path\xff"[..])] {
            let control = StartupControl {
                profile: StartupProfile::ManagedTransfer,
                runtime_stdout_fd: 4,
                runtime_stderr_fd: 5,
                observer_fd: 6,
                early_record_fd: 7,
                original_preload: preload,
                original_control: Some(b""),
                launch_id: 73,
            };
            let bytes = control.encode(3).unwrap();
            assert_eq!(&bytes[..8], b"DFYSTRT2");
            assert_eq!(u32_at(&bytes, 32), preload.is_some() as u32);
            assert_eq!(u32_at(&bytes, 40), 1);
            assert_eq!(&bytes[72..], preload.unwrap_or_default());
            assert_eq!(u64_at(&bytes, 56), 73);
            assert_eq!(u32_at(&bytes, 48), 0);
            assert!(zero(&bytes[52..56]));
            assert_eq!(u32_at(&bytes, 16) as usize, bytes.len());
        }
    }

    // The opt-in profile occupies only the selected v2 control flag word.
    #[test]
    fn reference_control_sets_exact_profile_flag() {
        let control = StartupControl {
            profile: StartupProfile::NativeReference,
            runtime_stdout_fd: 4,
            runtime_stderr_fd: 5,
            observer_fd: 6,
            early_record_fd: 7,
            original_preload: None,
            original_control: None,
            launch_id: 9,
        };
        let bytes = control.encode(3).unwrap();
        assert_eq!(u32_at(&bytes, 48), 1);
        assert!(zero(&bytes[52..56]));
        assert_eq!(u32_at(&bytes, 68), 0);
    }

    // A private observer endpoint cannot also be the consumed control channel.
    #[test]
    fn control_rejects_aliasing_channels() {
        let control = StartupControl {
            profile: StartupProfile::ManagedTransfer,
            runtime_stdout_fd: 4,
            runtime_stderr_fd: 5,
            observer_fd: 3,
            early_record_fd: 7,
            original_preload: None,
            original_control: None,
            launch_id: 1,
        };
        assert!(control.encode(3).is_err());
    }

    // Truncated observer records are infrastructure errors rather than absent observations.
    #[test]
    fn truncated_record_is_rejected() {
        assert!(decode_events(b"DFYSTEV2", 1, StartupProfile::ManagedTransfer).is_err());
    }

    // A system failure retains its raw errno without confusing it with a configuration code.
    #[test]
    fn system_error_preserves_errno() {
        let mut bytes = vec![0; 48];
        bytes[..8].copy_from_slice(b"DFYSTEV2");
        put32(&mut bytes, 8, 2);
        put32(&mut bytes, 12, 2);
        put32(&mut bytes, 16, 16);
        bytes[24..32].copy_from_slice(&8u64.to_le_bytes());
        put32(&mut bytes, 32, 3);
        put32(&mut bytes, 36, 2);
        put32(&mut bytes, 40, 24);
        assert_eq!(
            decode_events(&bytes, 8, StartupProfile::ManagedTransfer).unwrap(),
            vec![StartupEvent::BootstrapError(StartupFailure {
                phase: 3,
                kind: StartupFailureKind::System,
                code: 24
            })]
        );
        assert!(decode_events(&bytes, 9, StartupProfile::ManagedTransfer).is_err());
    }

    // Reference entry decoding accepts custom signal state and exact per-role absence.
    #[test]
    fn reference_entry_decodes_custom_signal_and_absent_roles() {
        let mut bytes = vec![0; EVENT_HEADER_BYTES + 40];
        bytes[..8].copy_from_slice(b"DFYSTEV2");
        put32(&mut bytes, 8, 2);
        put32(&mut bytes, 12, 3);
        put32(&mut bytes, 16, 40);
        bytes[24..32].copy_from_slice(&11u64.to_le_bytes());
        put32(&mut bytes, 32, 101);
        put32(&mut bytes, 36, 101);
        put32(&mut bytes, 40, 2);
        for role in 0..3 {
            put32(&mut bytes, 52 + role * 8, 9);
        }
        let events = decode_events(&bytes, 11, StartupProfile::NativeReference).unwrap();
        let StartupEvent::UtilityEntered(entry) = &events[0] else {
            panic!("expected utility entry")
        };
        assert_eq!(entry.sigpipe, ObservedPipeDisposition::Custom);
        assert!(entry
            .standards
            .as_ref()
            .unwrap()
            .iter()
            .all(|standard| !standard.available && standard.availability_errno == 9));
        assert!(decode_events(&bytes, 11, StartupProfile::ManagedTransfer).is_err());
    }
}
