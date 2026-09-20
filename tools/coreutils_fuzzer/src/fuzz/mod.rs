use crate::utils::cli::ExecKind;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::path::PathBuf;

#[derive(Debug, Clone, Serialize)]
pub struct ResolvedPaths {
    pub(crate) reference: ResolvedTarget,
    pub(crate) dut: ResolvedTarget,
}

#[derive(Debug, Clone, Serialize)]
pub struct ResolvedTarget {
    pub(crate) kind: ExecKind,
    pub(crate) path: PathBuf,
    pub(crate) label: &'static str,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratedCase {
    pub(crate) argv: Vec<String>,
    pub(crate) fixture: FixtureBlueprint,
    pub(crate) stdin: Vec<u8>,
    pub(crate) cwd: PathBuf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct UtilityProfile {
    pub(crate) requires_path_operand: bool,
    pub(crate) prefers_existing_paths: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixtureBlueprint {
    pub(crate) directories: Vec<DirSpec>,
    pub(crate) files: Vec<FileSpec>,
    pub(crate) symlinks: Vec<SymlinkSpec>,
    pub(crate) hardlinks: Vec<HardlinkSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DirSpec {
    pub(crate) relative_path: PathBuf,
    pub(crate) mode: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FileSpec {
    pub(crate) relative_path: PathBuf,
    pub(crate) bytes: Vec<u8>,
    pub(crate) mode: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SymlinkSpec {
    pub(crate) relative_path: PathBuf,
    pub(crate) target: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HardlinkSpec {
    pub(crate) relative_path: PathBuf,
    pub(crate) source_relative_path: PathBuf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum VariantKind {
    Ref,
    Dut,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RunResult {
    pub(crate) termination: process_outcome::Termination,
    pub(crate) stdout: Vec<u8>,
    pub(crate) stderr: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FsNodeSnapshot {
    pub(crate) raw_stat_metadata: crate::utils::world_json::RawStatMetadataJson,
    pub(crate) kind: String,
    pub(crate) mode_octal: String,
    pub(crate) times: FsTimes,
    pub(crate) uid: Option<u32>,
    pub(crate) gid: Option<u32>,
    pub(crate) logical_size: Option<u64>,
    pub(crate) allocated_512_blocks: Option<u64>,
    pub(crate) preferred_io_block_bytes: Option<u64>,
    pub(crate) target: String,
    pub(crate) data: Vec<u8>,
    pub(crate) host_key: Option<HostInodeKeySnapshot>,
    pub(crate) link_count: Option<u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HostInodeKeySnapshot {
    pub device: u64,
    pub inode: u64,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FsTimes {
    pub(crate) atime_sec: i64,
    pub(crate) atime_nsec: i64,
    pub(crate) mtime_sec: i64,
    pub(crate) mtime_nsec: i64,
    pub(crate) ctime_sec: i64,
    pub(crate) ctime_nsec: i64,
}

pub type FsSnapshot = BTreeMap<String, FsNodeSnapshot>;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub enum CompareResult {
    Match,
    Mismatch {
        process_outcome_diff: Option<(
            compare::ProcessOutcomeEvidence,
            compare::ProcessOutcomeEvidence,
        )>,
        stdout_diff: bool,
        stderr_diff: bool,
        fs_diff: Vec<String>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiffOp {
    Equal(String),
    Remove(String),
    Add(String),
}

pub mod campaign;
pub mod case_source;
pub mod compare;
pub(crate) mod container;
pub mod corpus;
pub mod coverage;
pub mod execution;
pub mod fixture;
pub(crate) mod input;
pub mod metrics;
pub mod mutation;
pub(crate) mod process_outcome;
pub mod regression;
pub mod replay;
pub mod repro;
pub(crate) mod runtime;
pub mod semantic;
pub mod shrink;
pub(crate) mod startup;
pub(crate) mod time_coverage;

pub use campaign::run_fuzzer;
