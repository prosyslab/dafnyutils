use crate::fuzz::HostInodeKeySnapshot;
use serde::de::{MapAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use serde_json::value::RawValue;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::num::NonZeroU32;

fn deserialize_unique_map<'de, D, K, V>(deserializer: D) -> Result<BTreeMap<K, V>, D::Error>
where
    D: Deserializer<'de>,
    K: Ord + Deserialize<'de>,
    V: Deserialize<'de>,
{
    struct UniqueMapVisitor<K, V>(std::marker::PhantomData<(K, V)>);
    impl<'de, K, V> Visitor<'de> for UniqueMapVisitor<K, V>
    where
        K: Ord + Deserialize<'de>,
        V: Deserialize<'de>,
    {
        type Value = BTreeMap<K, V>;
        fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("an object with unique keys")
        }
        fn visit_map<A>(self, mut access: A) -> Result<Self::Value, A::Error>
        where
            A: MapAccess<'de>,
        {
            let mut map = BTreeMap::new();
            while let Some((key, value)) = access.next_entry()? {
                if map.insert(key, value).is_some() {
                    return Err(serde::de::Error::custom("duplicate object key"));
                }
            }
            Ok(map)
        }
    }
    deserializer.deserialize_map(UniqueMapVisitor(std::marker::PhantomData))
}

fn deserialize_optional_unique_map<'de, D, K, V>(
    deserializer: D,
) -> Result<Option<BTreeMap<K, V>>, D::Error>
where
    D: Deserializer<'de>,
    K: Ord + Deserialize<'de>,
    V: Deserialize<'de>,
{
    #[derive(Deserialize)]
    #[serde(
        transparent,
        bound(deserialize = "K: Ord + Deserialize<'de>, V: Deserialize<'de>")
    )]
    struct UniqueMap<K, V>(#[serde(deserialize_with = "deserialize_unique_map")] BTreeMap<K, V>);
    Option::<UniqueMap<K, V>>::deserialize(deserializer).map(|value| value.map(|map| map.0))
}

pub const IO_SNAPSHOT_SCHEMA_VERSION: u32 = 6;

/// Canonical decimal text preserves unbounded Dafny arguments, including values
/// rejected by the native ABI. Validation also makes source emission unambiguous.
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
#[serde(transparent)]
pub struct IntegerLiteralJson(String);

impl IntegerLiteralJson {
    pub fn new(value: String) -> Result<Self, String> {
        let digits = value.strip_prefix('-').unwrap_or(&value);
        if digits.is_empty()
            || !digits.bytes().all(|byte| byte.is_ascii_digit())
            || (digits.len() > 1 && digits.starts_with('0'))
            || value == "-0"
        {
            return Err("integer observation must be canonical decimal text".to_string());
        }
        Ok(Self(value))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    fn is_negative(&self) -> bool {
        self.0.starts_with('-')
    }
}

impl<'de> Deserialize<'de> for IntegerLiteralJson {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::new(String::deserialize(deserializer)?).map_err(serde::de::Error::custom)
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RealtimeInstantJson {
    pub seconds: i64,
    pub nanoseconds: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TerminalAttributesJson {
    pub input_flags: u32,
    pub output_flags: u32,
    pub control_flags: u32,
    pub local_flags: u32,
    pub line_discipline: u8,
    pub control_characters: Vec<u8>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub enum SyscallResultJson<T> {
    SyscallOk(T),
    SyscallError(NonZeroU32),
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum SyscallOriginJson {
    KernelReturned,
    AdapterRejected,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TimespecArgumentJson {
    pub seconds: IntegerLiteralJson,
    pub nanoseconds: IntegerLiteralJson,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub enum UtimensTimesJson {
    NullTimes,
    TimesPair {
        atime: TimespecArgumentJson,
        mtime: TimespecArgumentJson,
    },
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TimestampPolicyJson {
    pub min_seconds: i64,
    pub max_seconds: i64,
    pub granularity_nanoseconds: u32,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
#[allow(clippy::enum_variant_names)] // Preserve the public BenchWorld constructors.
pub enum TimestampSemanticsJson {
    VfsTimestampSemantics(TimestampPolicyJson),
    UnsupportedTimestampSemantics,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TimestampSemanticsEntryJson {
    pub host_key: HostInodeKeySnapshot,
    pub semantics: TimestampSemanticsJson,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[allow(clippy::enum_variant_names)] // Preserve the public BenchWorld constructors.
pub enum DescriptorAccessJson {
    ReadAccess,
    WriteAccess,
    ReadWriteAccess,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[allow(clippy::enum_variant_names)] // Preserve the public BenchWorld constructors.
pub enum SeekWhenceJson {
    SeekStart,
    SeekCurrent,
    SeekEnd,
}

/// Raw observation coverage is separate from the legacy positive storage projection.
/// Unknown remains a valid abstract input. A complete model snapshot containing
/// Unknown does not establish complete native raw-stat capture.
#[derive(Debug, Clone, Copy, Default, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub enum RawStatMetadataJson {
    #[default]
    Unknown,
    Known {
        device_number: u64,
        io_block_bytes: i64,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct FileStatusJson {
    #[serde(default)]
    pub raw_stat_metadata: RawStatMetadataJson,
    pub kind: FileKindJson,
    pub mode: u32,
    pub ownership: OwnershipJson,
    pub storage: StorageInfoJson,
    pub times: FsTimesJson,
    pub host_key: HostInodeKeySnapshot,
    pub link_count: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
#[allow(clippy::enum_variant_names)] // Preserve the public BenchWorld constructors.
pub enum DescriptorTargetJson {
    InodeTarget(u64),
    StreamTarget(FileStatusJson),
    InvalidTarget,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub enum DescriptorOffsetJson {
    KnownOffset(u64),
    UnspecifiedOffset,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[allow(clippy::enum_variant_names)] // Preserve the public BenchWorld constructors.
pub enum StandardStreamJson {
    StandardInput,
    StandardOutput,
    StandardError,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct DescriptorFlagsJson {
    pub access: DescriptorAccessJson,
    pub append: bool,
    pub nonblocking: bool,
    pub direct: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct OpenFlagsJson {
    pub access: DescriptorAccessJson,
    pub create_if_missing: bool,
    pub truncate: bool,
    pub append: bool,
    pub nonblocking: bool,
    pub noctty: bool,
    pub cloexec: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct OpenDescriptionJson {
    pub target: DescriptorTargetJson,
    pub offset: DescriptorOffsetJson,
    pub flags: DescriptorFlagsJson,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct DescriptorStateJson {
    #[serde(deserialize_with = "deserialize_unique_map")]
    pub bindings: BTreeMap<i64, u64>,
    #[serde(deserialize_with = "deserialize_unique_map")]
    pub observers: BTreeMap<i64, StandardStreamJson>,
    #[serde(deserialize_with = "deserialize_unique_map")]
    pub descriptions: BTreeMap<u64, OpenDescriptionJson>,
    #[serde(deserialize_with = "deserialize_unique_map")]
    pub detached_inodes: BTreeMap<u64, InodeRecordJson>,
    pub next_handle: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct FilesystemSecurityContextJson {
    pub fsuid: u32,
    pub fsgid: u32,
    pub supplementary_groups: BTreeSet<u32>,
    pub dac_override: bool,
    pub dac_read_search: bool,
    pub fowner: bool,
    pub fsetid: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
#[allow(clippy::enum_variant_names)] // Preserve the public BenchWorld constructors.
pub enum SyscallObservationJson {
    ClockObservation {
        clock_result: SyscallResultJson<RealtimeInstantJson>,
    },
    AuxiliaryObservation {
        tag: IntegerLiteralJson,
        value: SyscallResultJson<u64>,
    },
    CloseObservation {
        handle: u64,
        origin: SyscallOriginJson,
        result: SyscallResultJson<bool>,
    },
    FlagsObservation {
        handle: u64,
        origin: SyscallOriginJson,
        flags: SyscallResultJson<u32>,
    },
    TerminalQueryObservation {
        handle: u64,
        origin: SyscallOriginJson,
        attributes: SyscallResultJson<TerminalAttributesJson>,
    },
    FstatObservation {
        handle: u64,
        origin: SyscallOriginJson,
        status: SyscallResultJson<FileStatusJson>,
    },
    PathStatObservation {
        path: String,
        follow_symlink: bool,
        origin: SyscallOriginJson,
        status: SyscallResultJson<FileStatusJson>,
    },
    UtimensPathObservation {
        path: String,
        follow_symlink: bool,
        requested_times: UtimensTimesJson,
        origin: SyscallOriginJson,
        result: SyscallResultJson<bool>,
    },
    UtimensFdObservation {
        handle: u64,
        requested_times: UtimensTimesJson,
        origin: SyscallOriginJson,
        result: SyscallResultJson<bool>,
    },
    ReadObservation {
        handle: u64,
        origin: SyscallOriginJson,
        capacity: IntegerLiteralJson,
        data: SyscallResultJson<Vec<u8>>,
    },
    WriteObservation {
        handle: u64,
        origin: SyscallOriginJson,
        requested_data: Vec<u8>,
        count: SyscallResultJson<u64>,
    },
    OpenObservation {
        path: String,
        origin: SyscallOriginJson,
        requested_flags: OpenFlagsJson,
        mode: u32,
        open_result: SyscallResultJson<u64>,
    },
    SeekObservation {
        handle: u64,
        origin: SyscallOriginJson,
        requested: IntegerLiteralJson,
        whence: SeekWhenceJson,
        position: SyscallResultJson<u64>,
    },
}

/// Versioned, complete capture of the public `BenchIO.IO` observation boundary.
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct IoSnapshot {
    #[serde(rename = "schemaVersion")]
    pub schema_version: u32,
    pub fs: InodeFileSystemJson,
    pub props: BTreeMap<String, String>,
    pub cwd: String,
    pub env: BTreeMap<String, String>,
    pub stdin: Vec<u8>,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    #[serde(rename = "dirHandles")]
    pub dir_handles: BTreeMap<i64, DirHandleJson>,
    pub now: i64,
    pub credentials: ProcessCredentialsJson,
    pub descriptors: DescriptorStateJson,
    pub timestamp_semantics: Vec<TimestampSemanticsEntryJson>,
    pub events: Vec<SyscallObservationJson>,
    pub security: FilesystemSecurityContextJson,
    pub umask: u32,
}

/// An exact pre/post observation and process exit verdict.
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct IoTransition {
    pub pre: IoSnapshot,
    pub post: IoSnapshot,
    #[serde(rename = "exit")]
    pub exit_code: i32,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct DirHandleJson {
    pub path: String,
    pub remaining: Vec<DirEntryJson>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(deny_unknown_fields)]
pub struct DirEntryJson {
    pub name: String,
    pub is_dir: bool,
    pub is_symlink: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ObservationOutcome {
    Complete(Box<IoSnapshot>),
    Partial(Box<PartialIoSnapshot>),
    Unsupported {
        field: String,
        reason: String,
        observed: Box<PartialIoSnapshot>,
    },
    Error {
        field: String,
        reason: String,
    },
}

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct PartialIoSnapshot {
    pub fs: Option<InodeFileSystemJson>,
    #[serde(default, deserialize_with = "deserialize_optional_unique_map")]
    pub props: Option<BTreeMap<String, String>>,
    pub cwd: Option<String>,
    #[serde(default, deserialize_with = "deserialize_optional_unique_map")]
    pub env: Option<BTreeMap<String, String>>,
    pub stdin: Option<Vec<u8>>,
    pub stdout: Option<Vec<u8>>,
    pub stderr: Option<Vec<u8>>,
    #[serde(default, deserialize_with = "deserialize_optional_unique_map")]
    pub dir_handles: Option<BTreeMap<i64, DirHandleJson>>,
    pub now: Option<i64>,
    pub credentials: Option<ProcessCredentialsJson>,
    pub descriptors: Option<DescriptorStateJson>,
    pub timestamp_semantics: Option<Vec<TimestampSemanticsEntryJson>>,
    pub events: Option<Vec<SyscallObservationJson>>,
    pub security: Option<FilesystemSecurityContextJson>,
    pub umask: Option<u32>,
}

impl From<IoSnapshot> for PartialIoSnapshot {
    fn from(snapshot: IoSnapshot) -> Self {
        Self {
            fs: Some(snapshot.fs),
            props: Some(snapshot.props),
            cwd: Some(snapshot.cwd),
            env: Some(snapshot.env),
            stdin: Some(snapshot.stdin),
            stdout: Some(snapshot.stdout),
            stderr: Some(snapshot.stderr),
            dir_handles: Some(snapshot.dir_handles),
            now: Some(snapshot.now),
            credentials: Some(snapshot.credentials),
            descriptors: Some(snapshot.descriptors),
            timestamp_semantics: Some(snapshot.timestamp_semantics),
            events: Some(snapshot.events),
            security: Some(snapshot.security),
            umask: Some(snapshot.umask),
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub enum LinkCountJson {
    Unknown,
    Known(u64),
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct OwnershipJson {
    pub uid: u32,
    pub gid: u32,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct ProcessCredentialsJson {
    pub effective_uid: u32,
    pub effective_gid: u32,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct StorageInfoJson {
    pub size: u64,
    pub allocated_512_blocks: u64,
    pub preferred_io_block_bytes: u64,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub enum FileKindJson {
    Regular,
    Directory,
    Symlink,
    BlockDevice,
    CharacterDevice,
    Fifo,
    Socket,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct InodeRecordJson {
    pub raw_stat_metadata: RawStatMetadataJson,
    pub host_key: HostInodeKeySnapshot,
    pub node: FsNodeJson,
    pub links: LinkCountJson,
    pub ownership: OwnershipJson,
    pub storage: StorageInfoJson,
    pub kind: FileKindJson,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct InodeNamespaceJson {
    pub inode: u64,
    pub children: BTreeMap<String, InodeNamespaceJson>,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct InodeFileSystemJson {
    pub namespace: InodeNamespaceJson,
    pub inodes: BTreeMap<u64, InodeRecordJson>,
}

impl<'de> Deserialize<'de> for InodeRecordJson {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Raw {
            #[serde(default)]
            raw_stat_metadata: RawStatMetadataJson,
            host_key: HostInodeKeySnapshot,
            node: FsNodeJson,
            links: LinkCountJson,
            ownership: OwnershipJson,
            storage: StorageInfoJson,
            kind: FileKindJson,
        }
        let raw = Raw::deserialize(deserializer)?;
        Ok(Self {
            raw_stat_metadata: raw.raw_stat_metadata,
            host_key: raw.host_key,
            node: raw.node,
            links: raw.links,
            ownership: raw.ownership,
            storage: raw.storage,
            kind: raw.kind,
        })
    }
}

impl<'de> Deserialize<'de> for InodeNamespaceJson {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Raw {
            inode: u64,
            #[serde(deserialize_with = "deserialize_unique_map")]
            children: BTreeMap<String, InodeNamespaceJson>,
        }
        let raw = Raw::deserialize(deserializer)?;
        Ok(Self {
            inode: raw.inode,
            children: raw.children,
        })
    }
}

impl<'de> Deserialize<'de> for InodeFileSystemJson {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Raw {
            namespace: InodeNamespaceJson,
            #[serde(deserialize_with = "deserialize_unique_map")]
            inodes: BTreeMap<u64, InodeRecordJson>,
        }
        let raw = Raw::deserialize(deserializer)?;
        let value = Self {
            namespace: raw.namespace,
            inodes: raw.inodes,
        };
        value.validate().map_err(serde::de::Error::custom)?;
        Ok(value)
    }
}

#[allow(dead_code)]
impl InodeFileSystemJson {
    pub fn validate(&self) -> Result<(), String> {
        let mut refs = BTreeMap::new();
        self.validate_tree(&self.namespace, &mut refs)?;
        if !matches!(
            self.inodes
                .get(&self.namespace.inode)
                .map(|record| &record.node),
            Some(FsNodeJson::Directory { .. })
        ) {
            return Err("inode filesystem root must be a directory".to_string());
        }
        if refs.len() != self.inodes.len()
            || refs.keys().any(|inode| !self.inodes.contains_key(inode))
        {
            return Err("inode namespace and record table must have the same IDs".to_string());
        }
        let mut keys = BTreeMap::new();
        for (inode, record) in &self.inodes {
            record.node.validate()?;
            Self::validate_record_metadata(record)?;
            if keys.insert(record.host_key, inode).is_some() {
                return Err("inode records have duplicate host keys".to_string());
            }
            match record.links {
                LinkCountJson::Known(count) if count > 0 && refs[inode] <= count => {}
                _ => {
                    return Err(format!(
                        "inode `{inode}` has invalid link count observation"
                    ))
                }
            }
        }
        Ok(())
    }

    fn validate_record_metadata(record: &InodeRecordJson) -> Result<(), String> {
        if record.storage.preferred_io_block_bytes == 0 {
            return Err("inode preferred IO block size must be positive".to_string());
        }
        let expected_size = match &record.node {
            FsNodeJson::Regular { data, .. } => Some(data.len() as u64),
            FsNodeJson::Symlink { target, .. } => Some(target.len() as u64),
            FsNodeJson::Directory { .. } | FsNodeJson::Inaccessible { .. } => None,
        };
        if expected_size.is_some_and(|size| record.storage.size != size) {
            return Err("inode storage size conflicts with node contents".to_string());
        }
        let kind_matches = match &record.node {
            FsNodeJson::Regular { .. } => {
                !matches!(record.kind, FileKindJson::Directory | FileKindJson::Symlink)
            }
            FsNodeJson::Directory { .. } => record.kind == FileKindJson::Directory,
            FsNodeJson::Symlink { .. } => record.kind == FileKindJson::Symlink,
            FsNodeJson::Inaccessible { .. } => {
                !matches!(record.kind, FileKindJson::Directory | FileKindJson::Symlink)
            }
        };
        if !kind_matches {
            return Err("inode file kind conflicts with node representation".to_string());
        }
        Ok(())
    }

    pub fn validate_complete(&self) -> Result<(), String> {
        self.validate()?;
        let mut refs = BTreeMap::new();
        self.validate_tree(&self.namespace, &mut refs)?;
        for (inode, record) in &self.inodes {
            if matches!(
                record.node,
                FsNodeJson::Regular { .. } | FsNodeJson::Symlink { .. }
            ) && record.links != LinkCountJson::Known(refs[inode])
            {
                return Err(format!(
                    "inode `{inode}` is outside the captured alias scope"
                ));
            }
        }
        Ok(())
    }

    pub fn validate_identity_transition(&self, post: &Self) -> Result<(), String> {
        for (pre_id, pre_record) in &self.inodes {
            if let Some(post_record) = post.inodes.get(pre_id) {
                if pre_record.host_key != post_record.host_key {
                    return Err(format!("logical inode `{pre_id}` changed host identity"));
                }
            }
        }
        Ok(())
    }

    fn validate_tree(
        &self,
        tree: &InodeNamespaceJson,
        refs: &mut BTreeMap<u64, u64>,
    ) -> Result<(), String> {
        let record = self
            .inodes
            .get(&tree.inode)
            .ok_or_else(|| format!("namespace references missing inode `{}`", tree.inode))?;
        *refs.entry(tree.inode).or_insert(0) += 1;
        if !matches!(record.node, FsNodeJson::Directory { .. }) && !tree.children.is_empty() {
            return Err(format!("non-directory inode `{}` has children", tree.inode));
        }
        for (name, child) in &tree.children {
            validate_path_segment(name)?;
            self.validate_tree(child, refs)?;
        }
        Ok(())
    }
}

impl<'de> Deserialize<'de> for IoSnapshot {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct RawIoSnapshot {
            #[serde(rename = "schemaVersion")]
            schema_version: u32,
            fs: Box<RawValue>,
            #[serde(deserialize_with = "deserialize_unique_map")]
            props: BTreeMap<String, String>,
            cwd: String,
            #[serde(deserialize_with = "deserialize_unique_map")]
            env: BTreeMap<String, String>,
            stdin: Vec<u8>,
            stdout: Vec<u8>,
            stderr: Vec<u8>,
            #[serde(rename = "dirHandles")]
            #[serde(deserialize_with = "deserialize_unique_map")]
            dir_handles: BTreeMap<i64, DirHandleJson>,
            now: i64,
            credentials: Option<ProcessCredentialsJson>,
            descriptors: Option<DescriptorStateJson>,
            timestamp_semantics: Option<Vec<TimestampSemanticsEntryJson>>,
            events: Option<Vec<SyscallObservationJson>>,
            security: Option<FilesystemSecurityContextJson>,
            umask: Option<u32>,
        }

        let raw = RawIoSnapshot::deserialize(deserializer)?;
        if raw.schema_version != IO_SNAPSHOT_SCHEMA_VERSION {
            return Err(serde::de::Error::custom(format!(
                "unsupported IO snapshot schema version `{}`",
                raw.schema_version
            )));
        }
        let snapshot = IoSnapshot {
            schema_version: raw.schema_version,
            fs: serde_json::from_str(raw.fs.get()).map_err(serde::de::Error::custom)?,
            props: raw.props,
            cwd: raw.cwd,
            env: raw.env,
            stdin: raw.stdin,
            stdout: raw.stdout,
            stderr: raw.stderr,
            dir_handles: raw.dir_handles,
            now: raw.now,
            credentials: raw.credentials.ok_or_else(|| {
                serde::de::Error::custom("IO snapshot is missing process credentials")
            })?,
            descriptors: raw.descriptors.ok_or_else(|| {
                serde::de::Error::custom("IO snapshot is missing descriptor state")
            })?,
            timestamp_semantics: raw.timestamp_semantics.ok_or_else(|| {
                serde::de::Error::custom("IO snapshot is missing timestamp semantics")
            })?,
            events: raw.events.ok_or_else(|| {
                serde::de::Error::custom("IO snapshot is missing syscall observations")
            })?,
            security: raw.security.ok_or_else(|| {
                serde::de::Error::custom("IO snapshot is missing filesystem security context")
            })?,
            umask: raw
                .umask
                .ok_or_else(|| serde::de::Error::custom("IO snapshot is missing umask"))?,
        };
        snapshot.validate().map_err(serde::de::Error::custom)?;
        Ok(snapshot)
    }
}

impl DescriptorStateJson {
    pub fn validate(&self, fs: &InodeFileSystemJson) -> Result<(), String> {
        if self.next_handle < 3 {
            return Err("descriptor next_handle must be at least three".to_string());
        }
        for (handle, description) in &self.bindings {
            if *handle < 0
                || *handle as u64 >= self.next_handle
                || !self.descriptions.contains_key(description)
            {
                return Err(format!("invalid descriptor binding `{handle}`"));
            }
        }
        for (handle, observer) in &self.observers {
            let expected = match observer {
                StandardStreamJson::StandardInput => 0,
                StandardStreamJson::StandardOutput => 1,
                StandardStreamJson::StandardError => 2,
            };
            if *handle != expected || !self.bindings.contains_key(handle) {
                return Err(format!("invalid standard stream observer `{handle}`"));
            }
        }
        for (id, description) in &self.descriptions {
            if *id >= self.next_handle || !self.bindings.values().any(|value| value == id) {
                return Err(format!("unbound or out-of-range open description `{id}`"));
            }
            if let DescriptorTargetJson::InodeTarget(inode) = description.target {
                if !fs.inodes.contains_key(&inode) && !self.detached_inodes.contains_key(&inode) {
                    return Err(format!("open description targets missing inode `{inode}`"));
                }
            }
            if let DescriptorTargetJson::StreamTarget(status) = &description.target {
                status.times.validate()?;
            }
        }
        let mut host_keys: BTreeSet<_> = fs.inodes.values().map(|record| record.host_key).collect();
        for (id, record) in &self.detached_inodes {
            if fs.inodes.contains_key(id) || !host_keys.insert(record.host_key) {
                return Err(format!("detached inode `{id}` overlaps a live identity"));
            }
            if record.links != LinkCountJson::Known(0)
                || !self
                    .descriptions
                    .values()
                    .any(|description| description.target == DescriptorTargetJson::InodeTarget(*id))
            {
                return Err(format!("detached inode `{id}` must be unlinked and open"));
            }
            record.node.validate()?;
            InodeFileSystemJson::validate_record_metadata(record)?;
        }
        Ok(())
    }
}

fn validate_events(events: &[SyscallObservationJson]) -> Result<(), String> {
    for event in events {
        match event {
            SyscallObservationJson::ClockObservation {
                clock_result: SyscallResultJson::SyscallOk(value),
            } if value.nanoseconds >= 1_000_000_000 => {
                return Err("clock nanoseconds must be below one billion".to_string());
            }
            SyscallObservationJson::ReadObservation { capacity, .. } if capacity.is_negative() => {
                return Err("read capacity must be nonnegative".to_string());
            }
            SyscallObservationJson::AuxiliaryObservation { tag, .. } if tag.is_negative() => {
                return Err("auxiliary vector tag must be nonnegative".to_string());
            }
            SyscallObservationJson::TerminalQueryObservation {
                attributes: SyscallResultJson::SyscallOk(attributes),
                ..
            } if attributes.control_characters.len() != 19 => {
                return Err(
                    "terminal attributes must contain exactly 19 control characters".to_string(),
                );
            }
            SyscallObservationJson::TerminalQueryObservation {
                origin: SyscallOriginJson::AdapterRejected,
                attributes,
                ..
            } if !matches!(
                attributes,
                SyscallResultJson::SyscallError(errno) if errno.get() == 9
            ) =>
            {
                return Err(
                    "adapter-rejected terminal query must report bad file descriptor".to_string(),
                );
            }
            SyscallObservationJson::FstatObservation {
                status: SyscallResultJson::SyscallOk(status),
                ..
            }
            | SyscallObservationJson::PathStatObservation {
                status: SyscallResultJson::SyscallOk(status),
                ..
            } => status.times.validate()?,
            _ => {}
        }
    }
    Ok(())
}

fn validate_umask(umask: u32) -> Result<(), String> {
    if umask > 0o777 {
        return Err("observed umask must contain only permission bits".to_string());
    }
    Ok(())
}

impl IoSnapshot {
    pub fn validate(&self) -> Result<(), String> {
        if self.schema_version != IO_SNAPSHOT_SCHEMA_VERSION {
            return Err(format!(
                "unsupported IO snapshot schema version `{}`",
                self.schema_version
            ));
        }
        self.fs.validate_complete()?;
        self.descriptors.validate(&self.fs)?;
        validate_timestamp_semantics(&self.timestamp_semantics, &self.fs, Some(&self.descriptors))?;
        validate_events(&self.events)?;
        validate_umask(self.umask)?;
        for handle in self.dir_handles.values() {
            handle.validate()?;
        }
        Ok(())
    }
}

impl<'de> Deserialize<'de> for IoTransition {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct RawIoTransition {
            pre: IoSnapshot,
            post: IoSnapshot,
            #[serde(rename = "exit")]
            exit_code: i32,
        }
        let raw = RawIoTransition::deserialize(deserializer)?;
        let transition = IoTransition {
            pre: raw.pre,
            post: raw.post,
            exit_code: raw.exit_code,
        };
        transition.validate().map_err(serde::de::Error::custom)?;
        Ok(transition)
    }
}

impl IoTransition {
    pub fn validate(&self) -> Result<(), String> {
        self.pre
            .validate()
            .map_err(|err| format!("invalid pre IO snapshot: {err}"))?;
        self.post
            .validate()
            .map_err(|err| format!("invalid post IO snapshot: {err}"))?;
        validate_observed_identity_transition(
            &self.pre.fs,
            Some(&self.pre.descriptors),
            &self.post.fs,
            Some(&self.post.descriptors),
        )
        .map_err(|err| format!("invalid IO transition identity: {err}"))?;
        validate_timestamp_semantics_transition(
            Some(&self.pre.timestamp_semantics),
            Some(&self.post.timestamp_semantics),
        )?;
        Ok(())
    }
}

fn validate_timestamp_semantics(
    entries: &[TimestampSemanticsEntryJson],
    fs: &InodeFileSystemJson,
    descriptors: Option<&DescriptorStateJson>,
) -> Result<(), String> {
    let mut keys = BTreeSet::new();
    for entry in entries {
        if !keys.insert(entry.host_key) {
            return Err("duplicate timestamp semantics host key".into());
        }
        if let TimestampSemanticsJson::VfsTimestampSemantics(policy) = entry.semantics {
            if policy.min_seconds > policy.max_seconds
                || !(1..=1_000_000_000).contains(&policy.granularity_nanoseconds)
            {
                return Err("invalid VFS timestamp range or granularity".into());
            }
        }
    }
    let mut required: BTreeSet<_> = fs.inodes.values().map(|record| record.host_key).collect();
    if let Some(descriptors) = descriptors {
        required.extend(
            descriptors
                .detached_inodes
                .values()
                .map(|record| record.host_key),
        );
        required.extend(descriptors.descriptions.values().filter_map(|description| {
            if let DescriptorTargetJson::StreamTarget(status) = &description.target {
                Some(status.host_key)
            } else {
                None
            }
        }));
    }
    if !required.is_subset(&keys) {
        return Err("timestamp semantics are missing a represented host key".into());
    }
    if descriptors.is_some() && keys != required {
        return Err("timestamp semantics contain an unrepresented host key".into());
    }
    Ok(())
}

fn validate_timestamp_semantics_transition(
    pre: Option<&[TimestampSemanticsEntryJson]>,
    post: Option<&[TimestampSemanticsEntryJson]>,
) -> Result<(), String> {
    if let (Some(pre), Some(post)) = (pre, post) {
        let before: BTreeMap<_, _> = pre
            .iter()
            .map(|entry| (entry.host_key, entry.semantics))
            .collect();
        for entry in post {
            if before
                .get(&entry.host_key)
                .is_some_and(|old| *old != entry.semantics)
            {
                return Err("surviving host key changed timestamp semantics".into());
            }
        }
    }
    Ok(())
}

fn validate_observed_identity_transition(
    pre_fs: &InodeFileSystemJson,
    pre_descriptors: Option<&DescriptorStateJson>,
    post_fs: &InodeFileSystemJson,
    post_descriptors: Option<&DescriptorStateJson>,
) -> Result<(), String> {
    let pre_records = pre_fs.inodes.iter().chain(
        pre_descriptors
            .into_iter()
            .flat_map(|state| state.detached_inodes.iter()),
    );
    for (id, record) in pre_records {
        let post_record = post_fs
            .inodes
            .get(id)
            .or_else(|| post_descriptors.and_then(|state| state.detached_inodes.get(id)));
        if post_record.is_some_and(|post| post.host_key != record.host_key) {
            return Err(format!("logical inode `{id}` changed host identity"));
        }
    }
    Ok(())
}

impl<'de> Deserialize<'de> for DirHandleJson {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct RawDirHandleJson {
            path: String,
            remaining: Vec<DirEntryJson>,
        }
        let raw = RawDirHandleJson::deserialize(deserializer)?;
        let handle = DirHandleJson {
            path: raw.path,
            remaining: raw.remaining,
        };
        handle.validate().map_err(serde::de::Error::custom)?;
        Ok(handle)
    }
}

impl DirHandleJson {
    fn validate(&self) -> Result<(), String> {
        path_components(&self.path)?;
        for entry in &self.remaining {
            validate_path_segment(&entry.name)?;
        }
        if self.remaining.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err("directory handle entries must be unique and sorted".to_string());
        }
        Ok(())
    }
}

impl<'de> Deserialize<'de> for FsNodeJson {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        enum RawFsNodeJson {
            Regular {
                data: Vec<u8>,
                mode: u32,
                times: FsTimesJson,
                #[serde(deserialize_with = "deserialize_unique_map")]
                ext: BTreeMap<String, String>,
            },
            Directory {
                mode: u32,
                times: FsTimesJson,
                #[serde(deserialize_with = "deserialize_unique_map")]
                ext: BTreeMap<String, String>,
            },
            Symlink {
                target: String,
                mode: u32,
                times: FsTimesJson,
                #[serde(deserialize_with = "deserialize_unique_map")]
                ext: BTreeMap<String, String>,
            },
            Inaccessible {
                #[serde(deserialize_with = "deserialize_unique_map")]
                ext: BTreeMap<String, String>,
            },
        }
        let node = match RawFsNodeJson::deserialize(deserializer)? {
            RawFsNodeJson::Regular {
                data,
                mode,
                times,
                ext,
            } => FsNodeJson::Regular {
                data,
                mode,
                times,
                ext,
            },
            RawFsNodeJson::Directory { mode, times, ext } => {
                FsNodeJson::Directory { mode, times, ext }
            }
            RawFsNodeJson::Symlink {
                target,
                mode,
                times,
                ext,
            } => FsNodeJson::Symlink {
                target,
                mode,
                times,
                ext,
            },
            RawFsNodeJson::Inaccessible { ext } => FsNodeJson::Inaccessible { ext },
        };
        node.validate().map_err(serde::de::Error::custom)?;
        Ok(node)
    }
}

impl FsNodeJson {
    fn validate(&self) -> Result<(), String> {
        match self {
            FsNodeJson::Regular { mode, times, .. }
            | FsNodeJson::Directory { mode, times, .. }
            | FsNodeJson::Symlink { mode, times, .. } => {
                validate_mode(*mode)?;
                times.validate()
            }
            FsNodeJson::Inaccessible { .. } => Ok(()),
        }
    }
}

fn validate_mode(mode: u32) -> Result<(), String> {
    if mode <= 0o7777 {
        Ok(())
    } else {
        Err(format!("invalid filesystem mode `{mode:o}`"))
    }
}

fn validate_path_segment(segment: &str) -> Result<(), String> {
    if segment.is_empty() || segment == "." || segment == ".." || segment.contains('/') {
        Err(format!("invalid filesystem path segment `{segment}`"))
    } else {
        Ok(())
    }
}

fn path_components(path: &str) -> Result<Vec<&str>, String> {
    if path == "." {
        return Ok(Vec::new());
    }
    if path.is_empty() || path.starts_with('/') || path.ends_with('/') {
        return Err(format!("filesystem snapshot has invalid path `{path}`"));
    }
    let components: Vec<_> = path.split('/').collect();
    if components
        .iter()
        .any(|part| part.is_empty() || *part == "." || *part == "..")
    {
        return Err(format!("filesystem snapshot has invalid path `{path}`"));
    }
    Ok(components)
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub enum FsNodeJson {
    Regular {
        data: Vec<u8>,
        mode: u32,
        times: FsTimesJson,
        ext: BTreeMap<String, String>,
    },
    Directory {
        mode: u32,
        times: FsTimesJson,
        ext: BTreeMap<String, String>,
    },
    Symlink {
        target: String,
        mode: u32,
        times: FsTimesJson,
        ext: BTreeMap<String, String>,
    },
    Inaccessible {
        ext: BTreeMap<String, String>,
    },
}

#[derive(Debug, Clone, Copy, Default, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct FsTimesJson {
    pub atime_sec: i64,
    pub atime_nsec: i64,
    pub mtime_sec: i64,
    pub mtime_nsec: i64,
    pub ctime_sec: i64,
    pub ctime_nsec: i64,
}

impl FsTimesJson {
    fn validate(&self) -> Result<(), String> {
        if [self.atime_nsec, self.mtime_nsec, self.ctime_nsec]
            .into_iter()
            .any(|nsec| !(0..1_000_000_000).contains(&nsec))
        {
            return Err("stored timestamp nanoseconds must be in [0, 1000000000)".to_string());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fuzz::HostInodeKeySnapshot;
    use std::collections::BTreeMap;

    fn inode_world() -> InodeFileSystemJson {
        let key = HostInodeKeySnapshot {
            device: 1,
            inode: 1,
        };
        InodeFileSystemJson {
            namespace: InodeNamespaceJson {
                inode: 0,
                children: BTreeMap::from([
                    (
                        "left".to_string(),
                        InodeNamespaceJson {
                            inode: 1,
                            children: BTreeMap::new(),
                        },
                    ),
                    (
                        "right".to_string(),
                        InodeNamespaceJson {
                            inode: 1,
                            children: BTreeMap::new(),
                        },
                    ),
                ]),
            },
            inodes: BTreeMap::from([
                (
                    0,
                    InodeRecordJson {
                        raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
                        host_key: HostInodeKeySnapshot {
                            device: 1,
                            inode: 0,
                        },
                        node: FsNodeJson::Directory {
                            mode: 0o755,
                            times: FsTimesJson::default(),
                            ext: BTreeMap::new(),
                        },
                        links: LinkCountJson::Known(1),
                        ownership: OwnershipJson {
                            uid: 1000,
                            gid: 1000,
                        },
                        storage: StorageInfoJson {
                            size: 4096,
                            allocated_512_blocks: 8,
                            preferred_io_block_bytes: 4096,
                        },
                        kind: FileKindJson::Directory,
                    },
                ),
                (
                    1,
                    InodeRecordJson {
                        raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
                        host_key: key,
                        node: FsNodeJson::Regular {
                            data: b"x".to_vec(),
                            mode: 0o644,
                            times: FsTimesJson::default(),
                            ext: BTreeMap::new(),
                        },
                        links: LinkCountJson::Known(2),
                        ownership: OwnershipJson {
                            uid: 1000,
                            gid: 1000,
                        },
                        storage: StorageInfoJson {
                            size: 1,
                            allocated_512_blocks: 8,
                            preferred_io_block_bytes: 4096,
                        },
                        kind: FileKindJson::Regular,
                    },
                ),
            ]),
        }
    }

    fn open_snapshot() -> IoSnapshot {
        IoSnapshot {
            schema_version: IO_SNAPSHOT_SCHEMA_VERSION,
            timestamp_semantics: inode_world()
                .inodes
                .values()
                .map(|record| TimestampSemanticsEntryJson {
                    host_key: record.host_key,
                    semantics: TimestampSemanticsJson::UnsupportedTimestampSemantics,
                })
                .collect(),
            fs: inode_world(),
            props: BTreeMap::new(),
            cwd: ".".to_string(),
            env: BTreeMap::new(),
            stdin: vec![0, 127, 128, 255],
            stdout: Vec::new(),
            stderr: Vec::new(),
            dir_handles: BTreeMap::new(),
            now: 0,
            credentials: ProcessCredentialsJson {
                effective_uid: 1000,
                effective_gid: 1001,
            },
            descriptors: DescriptorStateJson {
                bindings: BTreeMap::from([(3, 3)]),
                observers: BTreeMap::new(),
                descriptions: BTreeMap::from([(
                    3,
                    OpenDescriptionJson {
                        target: DescriptorTargetJson::InodeTarget(1),
                        offset: DescriptorOffsetJson::KnownOffset(0),
                        flags: DescriptorFlagsJson {
                            access: DescriptorAccessJson::ReadWriteAccess,
                            append: true,
                            nonblocking: false,
                            direct: false,
                        },
                    },
                )]),
                detached_inodes: BTreeMap::new(),
                next_handle: 4,
            },
            events: Vec::new(),
            security: FilesystemSecurityContextJson {
                fsuid: 1002,
                fsgid: 1003,
                supplementary_groups: BTreeSet::from([1004, 1005]),
                dac_override: false,
                dac_read_search: true,
                fowner: false,
                fsetid: true,
            },
            umask: 0o027,
        }
    }

    fn unlink_snapshot(snapshot: &mut IoSnapshot) {
        snapshot.fs.namespace.children.clear();
        let mut record = snapshot.fs.inodes.remove(&1).unwrap();
        record.links = LinkCountJson::Known(0);
        snapshot.descriptors.detached_inodes.insert(1, record);
    }

    fn file_status() -> FileStatusJson {
        FileStatusJson {
            raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson::Unknown,
            kind: FileKindJson::Regular,
            mode: 0o600,
            ownership: OwnershipJson {
                uid: 1000,
                gid: 1001,
            },
            storage: StorageInfoJson {
                size: 0,
                allocated_512_blocks: 0,
                preferred_io_block_bytes: 4096,
            },
            times: FsTimesJson::default(),
            host_key: HostInodeKeySnapshot {
                device: 2,
                inode: 3,
            },
            link_count: 1,
        }
    }

    fn terminal_attributes(control_characters: Vec<u8>) -> TerminalAttributesJson {
        TerminalAttributesJson {
            input_flags: 0,
            output_flags: u32::MAX,
            control_flags: 1 << 31,
            local_flags: 1,
            line_discipline: u8::MAX,
            control_characters,
        }
    }

    // Every kernel termios field and byte endpoint survives schema6 exactly.
    #[test]
    fn terminal_attributes_schema6_roundtrips_exact_fields() {
        let mut snapshot = open_snapshot();
        let attributes = terminal_attributes(vec![
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 128, 255,
        ]);
        snapshot
            .events
            .push(SyscallObservationJson::TerminalQueryObservation {
                handle: 1,
                origin: SyscallOriginJson::KernelReturned,
                attributes: SyscallResultJson::SyscallOk(attributes),
            });
        let encoded = serde_json::to_vec(&snapshot).unwrap();
        let decoded: IoSnapshot = serde_json::from_slice(&encoded).unwrap();
        assert_eq!(decoded, snapshot);
        assert_eq!(decoded.schema_version, 6);
    }

    // Kernel errors remain present observations rather than adapter rejection.
    #[test]
    fn terminal_attributes_kernel_error_roundtrips() {
        let mut snapshot = open_snapshot();
        snapshot
            .events
            .push(SyscallObservationJson::TerminalQueryObservation {
                handle: 1,
                origin: SyscallOriginJson::KernelReturned,
                attributes: SyscallResultJson::SyscallError(std::num::NonZeroU32::new(25).unwrap()),
            });
        let decoded: IoSnapshot =
            serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded, snapshot);
    }

    // The fixed Linux TCGETS vector cannot be shortened or extended.
    #[test]
    fn terminal_attributes_rejects_invalid_control_lengths() {
        for length in [0, 18, 20] {
            let mut snapshot = open_snapshot();
            snapshot
                .events
                .push(SyscallObservationJson::TerminalQueryObservation {
                    handle: 1,
                    origin: SyscallOriginJson::KernelReturned,
                    attributes: SyscallResultJson::SyscallOk(terminal_attributes(vec![0; length])),
                });
            assert!(snapshot
                .validate()
                .unwrap_err()
                .contains("exactly 19 control characters"));
        }
    }

    // Adapter rejection has one exact absent-capability result.
    #[test]
    fn terminal_attributes_rejects_inconsistent_adapter_results() {
        for attributes in [
            SyscallResultJson::SyscallOk(terminal_attributes(vec![0; 19])),
            SyscallResultJson::SyscallError(std::num::NonZeroU32::new(25).unwrap()),
        ] {
            let mut snapshot = open_snapshot();
            snapshot
                .events
                .push(SyscallObservationJson::TerminalQueryObservation {
                    handle: 1,
                    origin: SyscallOriginJson::AdapterRejected,
                    attributes,
                });
            assert!(snapshot
                .validate()
                .unwrap_err()
                .contains("bad file descriptor"));
        }
    }

    // Explicit malformed fields cannot be defaulted, truncated or accepted twice.
    #[test]
    fn terminal_attributes_strict_decoder_rejects_malformed_fields() {
        for text in [
            r#"{"UnknownTerminalObservation":{"handle":1}}"#,
            r#"{"TerminalQueryObservation":{"handle":1,"origin":"KernelReturned","attributes":null}}"#,
            r#"{"TerminalQueryObservation":{"handle":1,"origin":"KernelReturned"}}"#,
            r#"{"TerminalQueryObservation":{"handle":1,"handle":2,"origin":"KernelReturned","attributes":{"SyscallError":25}}}"#,
            r#"{"TerminalQueryObservation":{"handle":1,"origin":"KernelReturned","origin":"AdapterRejected","attributes":{"SyscallError":25}}}"#,
            r#"{"TerminalQueryObservation":{"handle":1,"origin":"KernelReturned","attributes":{"SyscallError":25},"attributes":{"SyscallError":9}}}"#,
            r#"{"TerminalQueryObservation":{"handle":1,"origin":"KernelReturned","attributes":{"SyscallOk":null}}}"#,
            r#"{"TerminalQueryObservation":{"handle":1,"origin":"KernelReturned","attributes":{"SyscallOk":{"input_flags":0,"output_flags":0,"control_flags":0,"local_flags":0,"line_discipline":0}}}}"#,
            r#"{"TerminalQueryObservation":{"handle":1,"origin":"KernelReturned","attributes":{"SyscallOk":{"input_flags":0,"output_flags":0,"control_flags":0,"local_flags":0,"line_discipline":0,"control_characters":[],"extra":0}}}}"#,
            r#"{"TerminalQueryObservation":{"handle":1,"origin":"KernelReturned","attributes":{"SyscallOk":{"input_flags":0,"input_flags":1,"output_flags":0,"control_flags":0,"local_flags":0,"line_discipline":0,"control_characters":[]}}}}"#,
            r#"{"TerminalQueryObservation":{"handle":1,"origin":"KernelReturned","attributes":{"SyscallOk":{"input_flags":0,"output_flags":0,"control_flags":0,"local_flags":0,"line_discipline":256,"control_characters":[]}}}}"#,
        ] {
            assert!(
                serde_json::from_str::<SyscallObservationJson>(text).is_err(),
                "{text}"
            );
        }
    }

    // A followed Unicode path retains the exact stat result, including subsecond time.
    #[test]
    fn path_stat_success_roundtrips() {
        let mut snapshot = open_snapshot();
        let mut status = file_status();
        status.times.atime_sec = -1;
        status.times.atime_nsec = 999_999_999;
        snapshot
            .events
            .push(SyscallObservationJson::PathStatObservation {
                path: "資料/alias".to_string(),
                follow_symlink: true,
                origin: SyscallOriginJson::KernelReturned,
                status: SyscallResultJson::SyscallOk(status),
            });
        let decoded: IoSnapshot =
            serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded, snapshot);
    }

    // Adapter rejection retains an embedded NUL instead of silently truncating the path.
    #[test]
    fn path_stat_rejected_nul_roundtrips() {
        let mut snapshot = open_snapshot();
        snapshot
            .events
            .push(SyscallObservationJson::PathStatObservation {
                path: "target\0ignored".to_string(),
                follow_symlink: false,
                origin: SyscallOriginJson::AdapterRejected,
                status: SyscallResultJson::SyscallError(NonZeroU32::new(22).unwrap()),
            });
        let decoded: IoSnapshot =
            serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded, snapshot);
    }

    // Kernel ENAMETOOLONG remains distinct from ENOENT in the saved observation.
    #[test]
    fn path_stat_kernel_name_too_long_roundtrips() {
        let mut snapshot = open_snapshot();
        snapshot
            .events
            .push(SyscallObservationJson::PathStatObservation {
                path: "x".repeat(256),
                follow_symlink: false,
                origin: SyscallOriginJson::KernelReturned,
                status: SyscallResultJson::SyscallError(NonZeroU32::new(36).unwrap()),
            });
        let decoded: IoSnapshot =
            serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded, snapshot);
    }

    // Path stat success must use stored timestamp units, not an overflowing nanosecond field.
    #[test]
    fn path_stat_success_rejects_timestamp_overflow() {
        let mut snapshot = open_snapshot();
        let mut status = file_status();
        status.times.ctime_nsec = 1_000_000_000;
        snapshot
            .events
            .push(SyscallObservationJson::PathStatObservation {
                path: "target".to_string(),
                follow_symlink: true,
                origin: SyscallOriginJson::KernelReturned,
                status: SyscallResultJson::SyscallOk(status),
            });
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("stored timestamp nanoseconds"));
    }

    // A zero auxiliary value survives the complete observation wire format as a success.
    #[test]
    fn auxiliary_zero_value_roundtrips() {
        let mut snapshot = open_snapshot();
        snapshot
            .events
            .push(SyscallObservationJson::AuxiliaryObservation {
                tag: IntegerLiteralJson::new("23".to_string()).unwrap(),
                value: SyscallResultJson::SyscallOk(0),
            });
        let encoded = serde_json::to_string(&snapshot).unwrap();
        let decoded: IoSnapshot = serde_json::from_str(&encoded).unwrap();
        assert_eq!(decoded, snapshot);
    }

    // A rejected tag beyond u64 retains its exact original argument and error.
    #[test]
    fn auxiliary_large_rejected_tag_roundtrips() {
        let mut snapshot = open_snapshot();
        snapshot
            .events
            .push(SyscallObservationJson::AuxiliaryObservation {
                tag: IntegerLiteralJson::new("1208925819614629174706176".to_string()).unwrap(),
                value: SyscallResultJson::SyscallError(NonZeroU32::new(75).unwrap()),
            });
        let encoded = serde_json::to_string(&snapshot).unwrap();
        let decoded: IoSnapshot = serde_json::from_str(&encoded).unwrap();
        assert_eq!(decoded, snapshot);
    }

    // A negative tag cannot be supplied to the Dafny nat argument through observation JSON.
    #[test]
    fn auxiliary_negative_tag_is_rejected() {
        let mut snapshot = open_snapshot();
        snapshot
            .events
            .push(SyscallObservationJson::AuxiliaryObservation {
                tag: IntegerLiteralJson::new("-1".to_string()).unwrap(),
                value: SyscallResultJson::SyscallError(NonZeroU32::new(75).unwrap()),
            });
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("tag must be nonnegative"));
    }

    // Stored inode timestamps cannot use a negative nanosecond component.
    #[test]
    fn inode_snapshot_rejects_negative_timestamp_nanoseconds() {
        let mut json = serde_json::to_value(open_snapshot()).unwrap();
        json["fs"]["inodes"]["0"]["node"]["Directory"]["times"]["atime_nsec"] =
            serde_json::json!(-1);
        assert!(serde_json::from_value::<IoSnapshot>(json)
            .unwrap_err()
            .to_string()
            .contains("stored timestamp nanoseconds"));
    }

    // A successful fstat observation has normalized stored timestamps, not request sentinels.
    #[test]
    fn io_snapshot_rejects_fstat_timestamp_overflow() {
        let mut snapshot = open_snapshot();
        let mut status = file_status();
        status.times.mtime_nsec = 1_000_000_000;
        snapshot
            .events
            .push(SyscallObservationJson::FstatObservation {
                handle: 3,
                origin: SyscallOriginJson::KernelReturned,
                status: SyscallResultJson::SyscallOk(status),
            });
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("stored timestamp nanoseconds"));
    }

    // Descriptors for external streams also preserve the stat timestamp domain.
    #[test]
    fn io_snapshot_rejects_stream_status_timestamp_sentinel() {
        let mut snapshot = open_snapshot();
        let mut status = file_status();
        status.times.ctime_nsec = (1 << 30) - 1; // Linux UTIME_NOW request sentinel.
        snapshot
            .descriptors
            .descriptions
            .get_mut(&3)
            .unwrap()
            .target = DescriptorTargetJson::StreamTarget(status);
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("stored timestamp nanoseconds"));
    }

    // A complete open-file observation preserves bytes, independent credentials and flags.
    #[test]
    fn io_snapshot_round_trips_minimal_state() {
        let snapshot = open_snapshot();
        snapshot.validate().unwrap();
        let decoded: IoSnapshot =
            serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded, snapshot);
    }

    // Unlink keeps the still-open inode and its logical identity in the exact transition.
    #[test]
    fn io_transition_round_trips_detached_open_inode() {
        let pre = open_snapshot();
        let mut post = pre.clone();
        unlink_snapshot(&mut post);
        let transition = IoTransition {
            pre,
            post,
            exit_code: 0,
        };
        let decoded: IoTransition =
            serde_json::from_slice(&serde_json::to_vec(&transition).unwrap()).unwrap();
        assert_eq!(decoded, transition);
    }

    // A live inode cannot acquire a different host identity when it becomes detached.
    #[test]
    fn io_transition_rejects_identity_change_on_unlink() {
        let pre = open_snapshot();
        let mut post = pre.clone();
        unlink_snapshot(&mut post);
        let original_key = post.descriptors.detached_inodes[&1].host_key;
        post.timestamp_semantics
            .iter_mut()
            .find(|entry| entry.host_key == original_key)
            .unwrap()
            .host_key
            .inode = 99;
        post.descriptors
            .detached_inodes
            .get_mut(&1)
            .unwrap()
            .host_key
            .inode = 99;
        assert!(IoTransition {
            pre,
            post,
            exit_code: 0
        }
        .validate()
        .unwrap_err()
        .contains("changed host identity"));
    }

    // An unobserved new IO region stays absent across a partial JSON round trip.
    #[test]
    fn partial_snapshot_preserves_missing_observations() {
        let partial: PartialIoSnapshot = serde_json::from_str("{}").unwrap();
        assert_eq!(partial, PartialIoSnapshot::default());
        let decoded: PartialIoSnapshot =
            serde_json::from_slice(&serde_json::to_vec(&partial).unwrap()).unwrap();
        assert_eq!(decoded, partial);
    }

    // A misspelled observation field cannot silently disappear from a partial capture.
    #[test]
    fn partial_snapshot_rejects_unknown_field() {
        assert!(serde_json::from_str::<PartialIoSnapshot>(r#"{"event": []}"#).is_err());
    }

    // Duplicate environment entries cannot overwrite raw partial observations silently.
    #[test]
    fn partial_snapshot_rejects_duplicate_environment_key() {
        let raw = r#"{"env":{"TZ":"UTC0","TZ":"America/New_York"}}"#;
        assert!(serde_json::from_str::<PartialIoSnapshot>(raw)
            .unwrap_err()
            .to_string()
            .contains("duplicate object key"));
    }

    // Schema five cannot turn missing syscall observations into an empty trace.
    #[test]
    fn io_snapshot_requires_syscall_observations() {
        let mut json = serde_json::to_value(open_snapshot()).unwrap();
        json.as_object_mut().unwrap().remove("events");
        assert!(serde_json::from_value::<IoSnapshot>(json)
            .unwrap_err()
            .to_string()
            .contains("missing syscall observations"));
    }

    // An old complete schema cannot imply values for newly required IO regions.
    #[test]
    fn io_snapshot_rejects_version_four() {
        let mut json = serde_json::to_value(open_snapshot()).unwrap();
        json["schemaVersion"] = serde_json::json!(4);
        assert!(serde_json::from_value::<IoSnapshot>(json)
            .unwrap_err()
            .to_string()
            .contains("unsupported IO snapshot schema version `4`"));
    }

    // An open descriptor cannot refer to an absent open-file description.
    #[test]
    fn io_snapshot_rejects_dangling_descriptor_binding() {
        let mut snapshot = open_snapshot();
        snapshot.descriptors.bindings.insert(3, 4);
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("invalid descriptor binding"));
    }

    // Only the standard stdout handle can contribute to the stdout transcript.
    #[test]
    fn io_snapshot_rejects_wrong_stdout_observer() {
        let mut snapshot = open_snapshot();
        snapshot
            .descriptors
            .observers
            .insert(3, StandardStreamJson::StandardOutput);
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("invalid standard stream observer"));
    }

    // A detached record cannot duplicate a live host inode under a new logical ID.
    #[test]
    fn io_snapshot_rejects_detached_host_alias() {
        let mut snapshot = open_snapshot();
        unlink_snapshot(&mut snapshot);
        snapshot
            .descriptors
            .detached_inodes
            .get_mut(&1)
            .unwrap()
            .host_key = snapshot.fs.inodes[&0].host_key;
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("overlaps a live identity"));
    }

    // A detached inode requires an open description to justify its retained lifetime.
    #[test]
    fn io_snapshot_rejects_unreferenced_detached_inode() {
        let mut snapshot = open_snapshot();
        unlink_snapshot(&mut snapshot);
        snapshot.descriptors.bindings.clear();
        snapshot.descriptors.descriptions.clear();
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("must be unlinked and open"));
    }

    // Syscall errors retain their actual positive errno instead of conflating zero with failure.
    #[test]
    fn syscall_observation_rejects_zero_errno() {
        let raw = r#"{"ClockObservation":{"clock_result":{"SyscallError":0}}}"#;
        assert!(serde_json::from_str::<SyscallObservationJson>(raw).is_err());
    }

    // A malformed nanosecond clock observation is rejected before source generation.
    #[test]
    fn io_snapshot_rejects_invalid_clock_nanoseconds() {
        let mut snapshot = open_snapshot();
        snapshot
            .events
            .push(SyscallObservationJson::ClockObservation {
                clock_result: SyscallResultJson::SyscallOk(RealtimeInstantJson {
                    seconds: -1,
                    nanoseconds: 1_000_000_000,
                }),
            });
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("clock nanoseconds"));
    }

    // Realtime observations may move backwards, including across the Unix epoch.
    #[test]
    fn io_snapshot_round_trips_backward_clock_observations() {
        let mut snapshot = open_snapshot();
        snapshot.events = [1, -1]
            .into_iter()
            .map(|seconds| SyscallObservationJson::ClockObservation {
                clock_result: SyscallResultJson::SyscallOk(RealtimeInstantJson {
                    seconds,
                    nanoseconds: 999_999_999,
                }),
            })
            .collect();
        let decoded: IoSnapshot =
            serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded.events, snapshot.events);
    }

    // An ABI-rejected read retains its large request, provenance and errno exactly.
    #[test]
    fn io_snapshot_round_trips_unbounded_rejected_read() {
        let mut snapshot = open_snapshot();
        snapshot
            .events
            .push(SyscallObservationJson::ReadObservation {
                handle: 3,
                origin: SyscallOriginJson::AdapterRejected,
                capacity: IntegerLiteralJson::new(
                    "340282366920938463463374607431768211456".to_string(),
                )
                .unwrap(),
                data: SyscallResultJson::SyscallError(NonZeroU32::new(22).unwrap()),
            });
        let decoded: IoSnapshot =
            serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded.events, snapshot.events);
    }

    // A native short write preserves the whole attempted byte sequence and accepted count.
    #[test]
    fn io_snapshot_round_trips_short_raw_write() {
        let mut snapshot = open_snapshot();
        snapshot
            .events
            .push(SyscallObservationJson::WriteObservation {
                handle: 3,
                origin: SyscallOriginJson::KernelReturned,
                requested_data: vec![0, 127, 128, 255],
                count: SyscallResultJson::SyscallOk(2),
            });
        let decoded: IoSnapshot =
            serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded.events, snapshot.events);
    }

    // Decimal observations cannot inject Dafny syntax through an unbounded integer argument.
    #[test]
    fn integer_observation_rejects_source_injection() {
        assert!(IntegerLiteralJson::new("0); assume false; //".to_string()).is_err());
    }

    // The unsigned read-capacity domain is checked even for programmatic observations.
    #[test]
    fn io_snapshot_rejects_negative_read_capacity() {
        let mut snapshot = open_snapshot();
        snapshot
            .events
            .push(SyscallObservationJson::ReadObservation {
                handle: 3,
                origin: SyscallOriginJson::AdapterRejected,
                capacity: IntegerLiteralJson::new("-1".to_string()).unwrap(),
                data: SyscallResultJson::SyscallError(NonZeroU32::new(22).unwrap()),
            });
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("read capacity must be nonnegative"));
    }

    // Umask observations may contain only the nine permission mask bits.
    #[test]
    fn io_snapshot_rejects_umask_special_bits() {
        let mut snapshot = open_snapshot();
        snapshot.umask = 0o1000;
        assert!(snapshot.validate().unwrap_err().contains("umask"));
    }

    // Two names for one regular inode survive an exact external JSON round trip.
    #[test]
    fn inode_world_json_round_trips_hardlink_aliases() {
        let world = inode_world();
        let decoded: InodeFileSystemJson =
            serde_json::from_value(serde_json::to_value(&world).unwrap()).unwrap();
        assert_eq!(decoded, world);
    }

    // A zero preferred block size cannot represent a concrete Unix inode observation.
    #[test]
    fn inode_world_json_rejects_zero_preferred_block_size() {
        let mut world = inode_world();
        world
            .inodes
            .get_mut(&1)
            .unwrap()
            .storage
            .preferred_io_block_bytes = 0;
        assert!(world.validate().is_err());
    }

    // Regular-file storage size must agree with the exact captured file contents.
    #[test]
    fn inode_world_json_rejects_regular_size_mismatch() {
        let mut world = inode_world();
        world.inodes.get_mut(&1).unwrap().storage.size = 7;
        assert!(world.validate().is_err());
    }

    // A directory node cannot be paired with a regular-file status kind.
    #[test]
    fn inode_world_json_rejects_directory_kind_mismatch() {
        let mut world = inode_world();
        world.inodes.get_mut(&0).unwrap().kind = FileKindJson::Regular;
        assert!(world.validate().is_err());
    }

    // Host inode identities reject unknown fields from external inode-world JSON.
    #[test]
    fn inode_world_json_rejects_unknown_host_key_field() {
        let mut json = serde_json::to_value(inode_world()).unwrap();
        json["inodes"]["1"]["host_key"]["unexpected"] = serde_json::json!(1);
        assert!(serde_json::from_value::<InodeFileSystemJson>(json).is_err());
    }

    // External inode records cannot omit the concrete storage observation.
    #[test]
    fn inode_world_json_rejects_missing_storage_metadata() {
        let mut json = serde_json::to_value(inode_world()).unwrap();
        json["inodes"]["1"]
            .as_object_mut()
            .unwrap()
            .remove("storage");
        assert!(serde_json::from_value::<InodeFileSystemJson>(json).is_err());
    }

    // A namespace ID without a table record cannot describe a filesystem.
    #[test]
    fn inode_world_json_rejects_missing_inode_record() {
        let mut world = inode_world();
        world.inodes.remove(&1);
        assert!(world.validate().is_err());
    }

    // An unreferenced inode record cannot be retained as hidden state.
    #[test]
    fn inode_world_json_rejects_orphan_inode_record() {
        let mut world = inode_world();
        world.inodes.insert(2, world.inodes[&1].clone());
        assert!(world.validate().is_err());
    }

    // Duplicate external inode keys fail rather than overwriting a record.
    #[test]
    fn inode_world_json_rejects_duplicate_inode_record_key() {
        let json = r#"{"namespace":{"inode":0,"children":{}},"inodes":{"0":{"host_key":{"device":1,"inode":0},"node":{"Directory":{"mode":493,"times":{"atime_sec":0,"atime_nsec":0,"mtime_sec":0,"mtime_nsec":0},"ext":{}}},"links":"Unknown"},"0":{"host_key":{"device":1,"inode":0},"node":{"Directory":{"mode":493,"times":{"atime_sec":0,"atime_nsec":0,"mtime_sec":0,"mtime_nsec":0},"ext":{}}},"links":"Unknown"}}}"#;
        assert!(serde_json::from_str::<InodeFileSystemJson>(json).is_err());
    }

    // A directory may appear at only one namespace path.
    #[test]
    fn inode_world_json_rejects_directory_alias() {
        let mut world = inode_world();
        world.namespace.children.get_mut("right").unwrap().inode = 0;
        assert!(world.validate().is_err());
    }
    // Child names must remain single namespace segments.
    #[test]
    fn inode_world_json_rejects_invalid_child_name() {
        let mut world = inode_world();
        let child = world.namespace.children.remove("left").unwrap();
        world
            .namespace
            .children
            .insert("bad/name".to_string(), child);
        assert!(world.validate().is_err());
    }
    // Namespace children are allowed only beneath directory records.
    #[test]
    fn inode_world_json_rejects_child_under_non_directory() {
        let mut world = inode_world();
        world
            .namespace
            .children
            .get_mut("left")
            .unwrap()
            .children
            .insert(
                "child".to_string(),
                InodeNamespaceJson {
                    inode: 1,
                    children: BTreeMap::new(),
                },
            );
        assert!(world.validate().is_err());
    }
    // The root namespace must name a directory record.
    #[test]
    fn inode_world_json_rejects_non_directory_root() {
        let mut world = inode_world();
        world.namespace.children.clear();
        world.namespace.inode = 1;
        world.inodes.get_mut(&1).unwrap().links = LinkCountJson::Known(1);
        assert!(world.validate().is_err());
    }
    // Live host identities identify one logical inode only.
    #[test]
    fn inode_world_json_rejects_duplicate_live_host_key() {
        let mut world = inode_world();
        let record = world.inodes[&1].clone();
        world.inodes.insert(2, record);
        world.namespace.children.insert(
            "third".to_string(),
            InodeNamespaceJson {
                inode: 2,
                children: BTreeMap::new(),
            },
        );
        assert!(world.validate().is_err());
    }
    // Regular files require an observed positive link count.
    #[test]
    fn inode_world_json_rejects_regular_unknown_links() {
        let mut world = inode_world();
        world.inodes.get_mut(&1).unwrap().links = LinkCountJson::Unknown;
        assert!(world.validate().is_err());
    }
    // Symlinks require an observed positive link count.
    #[test]
    fn inode_world_json_rejects_symlink_unknown_links() {
        let mut world = inode_world();
        world.inodes.get_mut(&1).unwrap().node = FsNodeJson::Symlink {
            target: "x".to_string(),
            mode: 0o777,
            times: FsTimesJson::default(),
            ext: BTreeMap::new(),
        };
        world.inodes.get_mut(&1).unwrap().links = LinkCountJson::Unknown;
        assert!(world.validate().is_err());
    }
    // Every live inode, including a directory, needs a positive link-count witness.
    #[test]
    fn inode_world_json_rejects_directory_unknown_links() {
        let mut world = inode_world();
        world.inodes.get_mut(&0).unwrap().links = LinkCountJson::Unknown;
        assert!(world.validate().is_err());
    }
    // A link-count witness below the captured inaccessible aliases is invalid.
    #[test]
    fn inode_world_json_rejects_inaccessible_link_count_below_references() {
        let mut world = inode_world();
        world.inodes.get_mut(&1).unwrap().node = FsNodeJson::Inaccessible {
            ext: BTreeMap::new(),
        };
        world.inodes.get_mut(&1).unwrap().links = LinkCountJson::Known(1);
        assert!(world.validate().is_err());
    }
    // A zero link count is not a live regular-file observation.
    #[test]
    fn inode_world_json_rejects_zero_known_link_count() {
        let mut world = inode_world();
        world.inodes.get_mut(&1).unwrap().links = LinkCountJson::Known(0);
        assert!(world.validate().is_err());
    }
    // A reported link count cannot be smaller than namespace aliases.
    #[test]
    fn inode_world_json_rejects_link_count_smaller_than_reference_count() {
        let mut world = inode_world();
        world.inodes.get_mut(&1).unwrap().links = LinkCountJson::Known(1);
        assert!(world.validate().is_err());
    }

    // A complete capture cannot omit a live regular-file alias.
    #[test]
    fn inode_world_json_complete_rejects_uncaptured_alias() {
        let mut world = inode_world();
        world.inodes.get_mut(&1).unwrap().links = LinkCountJson::Known(3);
        assert!(world.validate().is_ok());
        assert!(world.validate_complete().is_err());
    }

    // A logical inode token cannot identify a different host object after a transition.
    #[test]
    fn inode_world_transition_rejects_reused_logical_id() {
        let pre = inode_world();
        let mut post = pre.clone();
        post.inodes.get_mut(&1).unwrap().host_key.inode = 2;
        assert!(pre.validate_identity_transition(&post).is_err());
    }

    // A raw host inode number may be reused for a new logical object after deletion.
    #[test]
    fn inode_world_transition_allows_reused_host_id_with_new_logical_id() {
        let pre = inode_world();
        let mut post = pre.clone();
        let record = post.inodes.remove(&1).unwrap();
        post.namespace.children.get_mut("left").unwrap().inode = 2;
        post.namespace.children.get_mut("right").unwrap().inode = 2;
        post.inodes.insert(2, record);

        assert!(pre.validate_identity_transition(&post).is_ok());
    }

    // A legacy envelope reports its version before the version-2 filesystem body is decoded.
    #[test]
    fn io_snapshot_rejects_v1_before_decoding_filesystem() {
        let raw = r#"{"schemaVersion":1,"fs":{"not":"an inode filesystem"},"props":{},"cwd":".","env":{},"stdin":[],"stdout":[],"stderr":[],"dirHandles":{},"now":0}"#;
        let error = serde_json::from_str::<IoSnapshot>(raw).unwrap_err();
        assert!(error
            .to_string()
            .contains("unsupported IO snapshot schema version `1`"));
    }
    fn vfs_policy() -> TimestampSemanticsJson {
        TimestampSemanticsJson::VfsTimestampSemantics(TimestampPolicyJson {
            min_seconds: i64::MIN,
            max_seconds: i64::MAX,
            granularity_nanoseconds: 1,
        })
    }

    // Exact snapshots preserve full signed ABI policy endpoints without a guessed host default.
    #[test]
    fn timestamp_policy_round_trips_signed_endpoints() {
        let mut snapshot = open_snapshot();
        snapshot.timestamp_semantics[0].semantics = vfs_policy();
        let decoded: IoSnapshot =
            serde_json::from_value(serde_json::to_value(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded, snapshot);
    }

    // Duplicate host entries cannot silently overwrite one policy with another.
    #[test]
    fn timestamp_policy_rejects_duplicate_key() {
        let mut snapshot = open_snapshot();
        let mut duplicate = snapshot.timestamp_semantics[0].clone();
        duplicate.semantics = vfs_policy();
        snapshot.timestamp_semantics.push(duplicate);
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("duplicate timestamp"));
    }

    // A complete observation must carry the new region explicitly.
    #[test]
    fn timestamp_policy_is_required_in_exact_snapshot() {
        let mut json = serde_json::to_value(open_snapshot()).unwrap();
        json.as_object_mut().unwrap().remove("timestamp_semantics");
        assert!(serde_json::from_value::<IoSnapshot>(json)
            .unwrap_err()
            .to_string()
            .contains("missing timestamp semantics"));
    }

    // Exact key coverage includes every represented inode even when its semantics are unsupported.
    #[test]
    fn timestamp_policy_rejects_missing_live_key() {
        let mut snapshot = open_snapshot();
        snapshot.timestamp_semantics.pop();
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("missing a represented host key"));
    }

    // A reversed VFS range cannot be used to construct a timestamp policy subset value.
    #[test]
    fn timestamp_policy_rejects_reversed_range() {
        let mut snapshot = open_snapshot();
        snapshot.timestamp_semantics[0].semantics =
            TimestampSemanticsJson::VfsTimestampSemantics(TimestampPolicyJson {
                min_seconds: 1,
                max_seconds: -1,
                granularity_nanoseconds: 1,
            });
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("range or granularity"));
    }

    // Zero and greater-than-one-second granularity violate the modeled VFS policy domain.
    #[test]
    fn timestamp_policy_rejects_invalid_granularity() {
        for granularity_nanoseconds in [0, 1_000_000_001] {
            let mut snapshot = open_snapshot();
            snapshot.timestamp_semantics[0].semantics =
                TimestampSemanticsJson::VfsTimestampSemantics(TimestampPolicyJson {
                    min_seconds: 0,
                    max_seconds: 0,
                    granularity_nanoseconds,
                });
            assert!(snapshot
                .validate()
                .unwrap_err()
                .contains("range or granularity"));
        }
    }

    // A surviving host object cannot change the environmental timestamp semantics between observations.
    #[test]
    fn timestamp_policy_rejects_changed_survivor() {
        let pre = open_snapshot();
        let mut post = pre.clone();
        post.timestamp_semantics[0].semantics = vfs_policy();
        assert!(IoTransition {
            pre,
            post,
            exit_code: 0
        }
        .validate()
        .unwrap_err()
        .contains("changed timestamp semantics"));
    }

    // A stream status contributes its host key even though it is not an inode-map entry.
    #[test]
    fn timestamp_policy_covers_stream_target() {
        let mut snapshot = open_snapshot();
        let mut status = file_status();
        status.host_key = HostInodeKeySnapshot {
            device: 123,
            inode: 456,
        };
        snapshot
            .timestamp_semantics
            .push(TimestampSemanticsEntryJson {
                host_key: status.host_key,
                semantics: vfs_policy(),
            });
        snapshot.descriptors.bindings.insert(4, 4);
        let mut description = snapshot.descriptors.descriptions[&3].clone();
        description.target = DescriptorTargetJson::StreamTarget(status);
        snapshot.descriptors.descriptions.insert(4, description);
        snapshot.descriptors.next_handle = 5;
        let decoded: IoSnapshot =
            serde_json::from_value(serde_json::to_value(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded, snapshot);
    }

    // Exact descriptors rule out policy entries for otherwise unrepresented objects.
    #[test]
    fn timestamp_policy_rejects_extra_exact_key() {
        let mut snapshot = open_snapshot();
        snapshot
            .timestamp_semantics
            .push(TimestampSemanticsEntryJson {
                host_key: HostInodeKeySnapshot {
                    device: 123,
                    inode: 456,
                },
                semantics: vfs_policy(),
            });
        assert!(snapshot
            .validate()
            .unwrap_err()
            .contains("unrepresented host key"));
    }

    // A null times pointer is preserved separately from a pair of NOW arguments.
    #[test]
    fn utimens_null_times_round_trips() {
        let event = SyscallObservationJson::UtimensFdObservation {
            handle: 4,
            requested_times: UtimensTimesJson::NullTimes,
            origin: SyscallOriginJson::KernelReturned,
            result: SyscallResultJson::SyscallOk(true),
        };
        let decoded: SyscallObservationJson =
            serde_json::from_value(serde_json::to_value(&event).unwrap()).unwrap();
        assert_eq!(decoded, event);
    }

    // Rejected unbounded ignored seconds and both kernel sentinel values remain exact raw arguments.
    #[test]
    fn utimens_rejected_raw_pair_round_trips() {
        let number = |text: &str| IntegerLiteralJson::new(text.into()).unwrap();
        let event = SyscallObservationJson::UtimensPathObservation {
            path: "bad\0path".into(),
            follow_symlink: false,
            requested_times: UtimensTimesJson::TimesPair {
                atime: TimespecArgumentJson {
                    seconds: number("-9223372036854775809"),
                    nanoseconds: number("1073741823"),
                },
                mtime: TimespecArgumentJson {
                    seconds: number("9223372036854775808"),
                    nanoseconds: number("1073741822"),
                },
            },
            origin: SyscallOriginJson::AdapterRejected,
            result: SyscallResultJson::SyscallError(NonZeroU32::new(22).unwrap()),
        };
        let mut snapshot = open_snapshot();
        snapshot.events.push(event);
        let decoded: IoSnapshot =
            serde_json::from_value(serde_json::to_value(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded, snapshot);
    }

    // Kernel-rejected negative nanoseconds are not normalized or filtered out of the observation.
    #[test]
    fn utimens_kernel_invalid_nanoseconds_round_trips() {
        let number = |text: &str| IntegerLiteralJson::new(text.into()).unwrap();
        let mut snapshot = open_snapshot();
        snapshot
            .events
            .push(SyscallObservationJson::UtimensFdObservation {
                handle: 3,
                requested_times: UtimensTimesJson::TimesPair {
                    atime: TimespecArgumentJson {
                        seconds: number("0"),
                        nanoseconds: number("-1"),
                    },
                    mtime: TimespecArgumentJson {
                        seconds: number("0"),
                        nanoseconds: number("1000000000"),
                    },
                },
                origin: SyscallOriginJson::KernelReturned,
                result: SyscallResultJson::SyscallError(NonZeroU32::new(22).unwrap()),
            });
        let decoded: IoSnapshot =
            serde_json::from_value(serde_json::to_value(&snapshot).unwrap()).unwrap();
        assert_eq!(decoded, snapshot);
    }

    // Old omitted status and inode metadata remains Unknown even with nondefault legacy storage.
    #[test]
    fn raw_metadata_old_inputs_are_unknown() {
        let mut status = serde_json::to_value(file_status()).unwrap();
        status.as_object_mut().unwrap().remove("raw_stat_metadata");
        status["storage"]["preferred_io_block_bytes"] = serde_json::json!(65536);
        let restored: FileStatusJson = serde_json::from_value(status).unwrap();
        assert_eq!(restored.raw_stat_metadata, RawStatMetadataJson::Unknown);
        let original = open_snapshot();
        let mut old = serde_json::to_value(&original).unwrap();
        for record in old["fs"]["inodes"].as_object_mut().unwrap().values_mut() {
            record.as_object_mut().unwrap().remove("raw_stat_metadata");
        }
        let restored: IoSnapshot = serde_json::from_value(old).unwrap();
        assert_eq!(restored.fs, original.fs);
    }

    // Raw device and block-size endpoint values survive both ordinary and custom status/inode decoders.
    #[test]
    fn raw_metadata_signed_endpoints_round_trip() {
        for block in [i64::MIN, -1, 0, i64::MAX] {
            let raw = RawStatMetadataJson::Known {
                device_number: u64::MAX,
                io_block_bytes: block,
            };
            let mut status = file_status();
            status.raw_stat_metadata = raw;
            let encoded = serde_json::to_value(&status).unwrap();
            assert_eq!(
                encoded["raw_stat_metadata"],
                serde_json::json!({"Known": {
                "device_number": u64::MAX, "io_block_bytes": block }})
            );
            assert_eq!(
                serde_json::from_value::<FileStatusJson>(encoded).unwrap(),
                status
            );
            let mut snapshot = open_snapshot();
            for record in snapshot.fs.inodes.values_mut() {
                record.raw_stat_metadata = raw;
            }
            snapshot
                .events
                .push(SyscallObservationJson::FstatObservation {
                    handle: 3,
                    origin: SyscallOriginJson::KernelReturned,
                    status: SyscallResultJson::SyscallOk(status),
                });
            assert_eq!(
                serde_json::from_value::<IoSnapshot>(serde_json::to_value(&snapshot).unwrap())
                    .unwrap(),
                snapshot
            );
        }
    }

    // Malformed, extra, missing or out-of-range explicit raw fields cannot become Unknown by fallback.
    #[test]
    fn raw_metadata_rejects_invalid_explicit_inputs() {
        for text in [
            "null",
            "{}",
            r#"{"Unknown":{}}"#,
            r#"{"Known":{"device_number":-1,"io_block_bytes":0}}"#,
            r#"{"Known":{"device_number":18446744073709551616,"io_block_bytes":0}}"#,
            r#"{"Known":{"device_number":0,"io_block_bytes":9223372036854775808}}"#,
            r#"{"Known":{"device_number":0,"io_block_bytes":-9223372036854775809}}"#,
            r#"{"Known":{"device_number":0}}"#,
            r#"{"Known":{"device_number":0,"io_block_bytes":0,"extra":1}}"#,
            r#"{"Known":{"device_number":0,"device_number":1,"io_block_bytes":0}}"#,
        ] {
            assert!(
                serde_json::from_str::<RawStatMetadataJson>(text).is_err(),
                "{text}"
            );
        }
    }
}
