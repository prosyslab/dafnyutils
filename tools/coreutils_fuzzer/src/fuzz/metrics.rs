use super::case_source::CaseOrigin;
use super::repro::{tool_provenance, ToolProvenance};
use super::time_coverage::EvaluatedComparison;
use super::{GeneratedCase, ResolvedTarget};
use crate::utils::cli::ExecKind;
use serde::Serialize;
use std::collections::BTreeMap;
use std::fs;
use std::io::{BufReader, Read};
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

pub(crate) const METRICS_SCHEMA_V1: &str = "coreutils-fuzzer.metrics.v1";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum CampaignMode {
    Fuzz,
    Regression,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub(crate) struct StageDurations {
    pub(crate) source_ns: u128,
    pub(crate) evaluation_ns: u128,
    pub(crate) coverage_ns: u128,
    pub(crate) shrink_ns: u128,
    pub(crate) persist_ns: u128,
    pub(crate) queue_wait_ns: u128,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub(crate) struct CaseMetricsV1 {
    pub(crate) id: String,
    pub(crate) origin: CaseOrigin,
    pub(crate) transformed_from: Option<String>,
    pub(crate) case_fingerprint: String,
    pub(crate) outcome: String,
    pub(crate) comparison: Option<EvaluatedComparison>,
    pub(crate) durations: StageDurations,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize)]
pub(crate) struct CoverageMetricsV1 {
    pub(crate) option_singles_seen: usize,
    pub(crate) option_singles_total: usize,
    pub(crate) option_pairs_seen: usize,
    pub(crate) option_pairs_total: usize,
    pub(crate) semantic_buckets_seen: usize,
    pub(crate) semantic_buckets_total: usize,
}

#[derive(Debug, Serialize)]
struct CampaignMetricsV1 {
    schema_version: &'static str,
    run_id: String,
    tool: ToolProvenance,
    mode: CampaignMode,
    util: String,
    seed: u64,
    requested: usize,
    submitted: usize,
    completed: usize,
    abandoned: usize,
    outcomes: BTreeMap<String, usize>,
    elapsed_ns: u128,
    configuration: BTreeMap<String, String>,
    coverage: CoverageMetricsV1,
    cases: Vec<CaseMetricsV1>,
}

pub(crate) struct MetricsRecorder {
    path: Option<PathBuf>,
    started: std::time::Instant,
    document: CampaignMetricsV1,
}

impl MetricsRecorder {
    pub(crate) fn new(
        path: Option<PathBuf>,
        mode: CampaignMode,
        util: &str,
        seed: u64,
        requested: usize,
    ) -> Self {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        let tool = tool_provenance();
        Self {
            path,
            started: std::time::Instant::now(),
            document: CampaignMetricsV1 {
                schema_version: METRICS_SCHEMA_V1,
                run_id: format!("{timestamp}-{}-{seed}", std::process::id()),
                tool,
                mode,
                util: util.to_string(),
                seed,
                requested,
                submitted: 0,
                completed: 0,
                abandoned: 0,
                outcomes: BTreeMap::new(),
                elapsed_ns: 0,
                configuration: crate::utils::capabilities::capability_for(util)
                    .map(|capability| {
                        BTreeMap::from([(
                            "time_coverage_requirement".to_string(),
                            capability.time_coverage.as_str().to_string(),
                        )])
                    })
                    .unwrap_or_default(),
                coverage: CoverageMetricsV1::default(),
                cases: Vec::new(),
            },
        }
    }

    pub(crate) fn submit(&mut self) {
        self.document.submitted += 1;
    }

    pub(crate) fn is_enabled(&self) -> bool {
        self.path.is_some()
    }

    pub(crate) fn complete(&mut self, metrics: CaseMetricsV1) {
        self.document.completed += 1;
        self.record_case(metrics);
    }

    fn record_case(&mut self, metrics: CaseMetricsV1) {
        *self
            .document
            .outcomes
            .entry(metrics.outcome.clone())
            .or_insert(0) += 1;
        self.document.cases.push(metrics);
    }

    pub(crate) fn set_coverage(&mut self, coverage: CoverageMetricsV1) {
        self.document.coverage = coverage;
    }

    pub(crate) fn set_configuration(&mut self, key: &str, value: impl ToString) {
        self.document
            .configuration
            .insert(key.to_string(), value.to_string());
    }

    pub(crate) fn set_target_configuration(
        &mut self,
        prefix: &str,
        target: &ResolvedTarget,
    ) -> Result<(), String> {
        self.set_configuration(
            format!("{prefix}_kind").as_str(),
            exec_kind_name(target.kind),
        );
        self.set_artifact_configuration(prefix, &target.path)
    }

    pub(crate) fn set_artifact_configuration(
        &mut self,
        prefix: &str,
        path: &Path,
    ) -> Result<(), String> {
        let resolved = fs::canonicalize(path).map_err(|error| {
            format!(
                "failed to resolve {prefix} artifact `{}` for metrics: {error}",
                path.display()
            )
        })?;
        let (fingerprint, size_bytes) = file_fingerprint(&resolved)?;
        self.set_configuration(format!("{prefix}_path").as_str(), resolved.display());
        self.set_configuration(
            format!("{prefix}_artifact_fingerprint").as_str(),
            fingerprint,
        );
        self.set_configuration(format!("{prefix}_artifact_size_bytes").as_str(), size_bytes);
        Ok(())
    }

    pub(crate) fn set_input_file_configuration(
        &mut self,
        prefix: &str,
        path: &Path,
    ) -> Result<(), String> {
        self.set_artifact_configuration(prefix, path)
    }

    pub(crate) fn render_population_report(&self) -> String {
        let document = &self.document;
        let count = |name: &str| document.outcomes.get(name).copied().unwrap_or(0);
        let matches = count("match");
        let mismatches = count("mismatch") + count("semantic_mismatch");
        let timeouts = count("fuzzer_timeout");
        let incomplete = count("incomplete_coverage");
        let other = document.completed - matches - mismatches - timeouts - incomplete;
        format!(
            concat!(
                "  Iterations : requested={} submitted={} completed={} not_started={} unfinished={}\n",
                "  Outcomes   : match={} mismatch={} timeout={} incomplete_coverage={} other_errors={}\n",
                "  Elapsed    : {:.2}s"
            ),
            document.requested,
            document.submitted,
            document.completed,
            document.requested - document.submitted,
            document.submitted - document.completed,
            matches,
            mismatches,
            timeouts,
            incomplete,
            other,
            self.started.elapsed().as_secs_f64(),
        )
    }

    pub(crate) fn finish(mut self) -> Result<(), String> {
        let Some(path) = self.path.take() else {
            return Ok(());
        };
        self.document.elapsed_ns = self.started.elapsed().as_nanos();
        write_metrics(&path, &self.document)
    }

    pub(crate) fn finish_preserving_error(self, primary_error: String) -> String {
        match self.finish() {
            Ok(()) => primary_error,
            Err(metrics_error) => {
                format!("{primary_error}\nmetrics output failure: {metrics_error}")
            }
        }
    }
}

pub(crate) fn duration_ns(duration: Duration) -> u128 {
    duration.as_nanos()
}

pub(crate) fn case_fingerprint(case: &GeneratedCase) -> String {
    let bytes = serde_json::to_vec(case)
        .expect("validated GeneratedCase paths and fields always serialize to JSON");
    let mut hash = 0xcbf29ce484222325u64;
    for byte in bytes {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{hash:016x}")
}

pub(crate) fn error_outcome(error: &str) -> String {
    error
        .lines()
        .find_map(|line| line.strip_prefix("FUZZER_OUTCOME="))
        .filter(|value| !value.is_empty())
        .unwrap_or("execution_error")
        .to_string()
}

fn exec_kind_name(kind: ExecKind) -> &'static str {
    match kind {
        ExecKind::Native => "native",
        ExecKind::DotnetDll => "dotnet-dll",
    }
}

fn file_fingerprint(path: &Path) -> Result<(String, u64), String> {
    let file = fs::File::open(path).map_err(|error| {
        format!(
            "failed to read metrics artifact `{}`: {error}",
            path.display()
        )
    })?;
    let mut reader = BufReader::new(file);
    let mut hash = 0xcbf29ce484222325u64;
    let mut size = 0u64;
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let read = reader.read(&mut buffer).map_err(|error| {
            format!(
                "failed to hash metrics artifact `{}`: {error}",
                path.display()
            )
        })?;
        if read == 0 {
            break;
        }
        size += read as u64;
        for byte in &buffer[..read] {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
    }
    Ok((format!("fnv1a64:{hash:016x}"), size))
}

fn write_metrics(path: &Path, metrics: &CampaignMetricsV1) -> Result<(), String> {
    if path.exists() {
        return Err(format!(
            "refusing to overwrite metrics output `{}`",
            path.display()
        ));
    }
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|error| {
            format!(
                "failed to create metrics directory `{}`: {error}",
                parent.display()
            )
        })?;
    }
    let file_name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| {
            format!(
                "metrics output has no valid file name: `{}`",
                path.display()
            )
        })?;
    let temporary = path.with_file_name(format!(".{file_name}.tmp-{}", std::process::id()));
    let bytes = serde_json::to_vec_pretty(metrics)
        .map_err(|error| format!("failed to serialize campaign metrics: {error}"))?;
    fs::write(&temporary, bytes).map_err(|error| {
        format!(
            "failed to write metrics temporary file `{}`: {error}",
            temporary.display()
        )
    })?;
    match fs::hard_link(&temporary, path) {
        Ok(()) => fs::remove_file(&temporary).map_err(|error| {
            format!(
                "published metrics but failed to remove temporary file `{}`: {error}",
                temporary.display()
            )
        }),
        Err(error) => {
            let _ = fs::remove_file(&temporary);
            Err(format!(
                "failed to publish metrics output `{}` without overwrite: {error}",
                path.display()
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        case_fingerprint, error_outcome, CampaignMode, MetricsRecorder, METRICS_SCHEMA_V1,
    };
    use crate::fuzz::{FixtureBlueprint, GeneratedCase};
    use std::fs;
    use std::path::PathBuf;

    fn sample_case() -> GeneratedCase {
        GeneratedCase {
            argv: vec!["-".to_string()],
            fixture: FixtureBlueprint {
                directories: Vec::new(),
                files: Vec::new(),
                symlinks: Vec::new(),
                hardlinks: Vec::new(),
            },
            stdin: b"input\n".to_vec(),
            cwd: PathBuf::from("."),
        }
    }

    // The same serialized case has one stable metrics fingerprint.
    #[test]
    fn case_fingerprint_is_deterministic() {
        assert_eq!(
            case_fingerprint(&sample_case()),
            case_fingerprint(&sample_case())
        );
    }

    // Metrics publication writes one versioned document and preserves an existing artifact.
    #[test]
    fn metrics_are_versioned_and_never_overwritten() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("metrics.json");
        MetricsRecorder::new(Some(path.clone()), CampaignMode::Fuzz, "cat", 1, 0)
            .finish()
            .unwrap();
        let value: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        assert_eq!(value["schema_version"], METRICS_SCHEMA_V1);

        let error = MetricsRecorder::new(Some(path.clone()), CampaignMode::Fuzz, "cat", 1, 0)
            .finish()
            .unwrap_err();
        assert!(error.contains("refusing to overwrite"));
    }

    // A failed case remains submitted but incomplete instead of being counted as throughput.
    #[test]
    fn incomplete_work_is_preserved_in_metrics_denominators() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("failed.json");
        let mut recorder =
            MetricsRecorder::new(Some(path.clone()), CampaignMode::Fuzz, "cat", 1, 1);
        recorder.submit();
        recorder.finish().unwrap();
        let value: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();

        assert_eq!(value["requested"], 1);
        assert_eq!(value["submitted"], 1);
        assert_eq!(value["completed"], 0);
        assert_eq!(value["cases"].as_array().unwrap().len(), 0);
    }

    // Stable fuzzer markers become structured error outcomes while unmarked errors stay explicit.
    #[test]
    fn error_outcome_preserves_marker_or_execution_failure() {
        assert_eq!(
            error_outcome("FUZZER_OUTCOME=fuzzer_timeout\ntimed out"),
            "fuzzer_timeout"
        );
        assert_eq!(error_outcome("fixture failed"), "execution_error");
    }
    fn record_outcome(recorder: &mut MetricsRecorder, outcome: &str) {
        recorder.submit();
        recorder.complete(super::CaseMetricsV1 {
            id: "reported-case".to_string(),
            origin: crate::fuzz::case_source::CaseOrigin::Explicit,
            transformed_from: None,
            case_fingerprint: case_fingerprint(&sample_case()),
            outcome: outcome.to_string(),
            comparison: None,
            durations: super::StageDurations::default(),
        });
    }

    // Completed timeout work must not be reported as matches or as a completed budget.
    #[test]
    fn population_report_distinguishes_timeout_from_unstarted_work() {
        let mut recorder = MetricsRecorder::new(None, CampaignMode::Fuzz, "cat", 7, 1000);
        record_outcome(&mut recorder, "match");
        record_outcome(&mut recorder, "fuzzer_timeout");
        let report = recorder.render_population_report();
        assert!(
            report.contains("requested=1000 submitted=2 completed=2 not_started=998 unfinished=0")
        );
        assert!(
            report.contains("match=1 mismatch=0 timeout=1 incomplete_coverage=0 other_errors=0")
        );
    }

    // Mismatches and missing observations remain visible even without a metrics output file.
    #[test]
    fn population_report_retains_nonmatch_outcomes_without_json() {
        let mut recorder = MetricsRecorder::new(None, CampaignMode::Fuzz, "cat", 19, 4);
        record_outcome(&mut recorder, "mismatch");
        record_outcome(&mut recorder, "incomplete_coverage");
        record_outcome(&mut recorder, "fuzzer_target_spawn_failure");
        recorder.submit();
        let report = recorder.render_population_report();
        assert!(report.contains("requested=4 submitted=4 completed=3 not_started=0 unfinished=1"));
        assert!(
            report.contains("match=0 mismatch=1 timeout=0 incomplete_coverage=1 other_errors=1")
        );
    }
}
