use super::CompareResult;
use crate::utils::capabilities::TimeCoverageRequirement;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum CaseVerdict {
    Match,
    Mismatch,
    IncompleteCoverage,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum TimeCoverageGap {
    ReferenceExecutionTrace,
    DutExecutionTrace,
    ReferenceSpecClassification,
    DutSpecClassification,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case", deny_unknown_fields)]
pub(crate) enum TimeCoverageVerdict {
    NotRequired,
    Incomplete { gaps: Vec<TimeCoverageGap> },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct EvaluatedComparison {
    pub(crate) observable: CompareResult,
    pub(crate) time_requirement: TimeCoverageRequirement,
    pub(crate) time_coverage: TimeCoverageVerdict,
}

impl EvaluatedComparison {
    /// Current launch paths collect no complete per-execution temporal evidence.
    /// A future complete result must be constructed from checked observer evidence
    /// and both executions' same-Spec results, never from matching raw timestamps.
    pub(crate) fn without_time_observations(
        observable: CompareResult,
        time_requirement: TimeCoverageRequirement,
    ) -> Self {
        let time_coverage = match time_requirement {
            TimeCoverageRequirement::None => TimeCoverageVerdict::NotRequired,
            TimeCoverageRequirement::ExactPerExecution => TimeCoverageVerdict::Incomplete {
                gaps: vec![
                    TimeCoverageGap::ReferenceExecutionTrace,
                    TimeCoverageGap::DutExecutionTrace,
                    TimeCoverageGap::ReferenceSpecClassification,
                    TimeCoverageGap::DutSpecClassification,
                ],
            },
        };
        Self {
            observable,
            time_requirement,
            time_coverage,
        }
    }

    pub(crate) fn verdict(&self) -> CaseVerdict {
        if self.time_requirement == TimeCoverageRequirement::ExactPerExecution
            || !matches!(self.time_coverage, TimeCoverageVerdict::NotRequired)
        {
            return CaseVerdict::IncompleteCoverage;
        }
        match self.observable {
            CompareResult::Match => CaseVerdict::Match,
            CompareResult::Mismatch { .. } => CaseVerdict::Mismatch,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::CaseVerdict;
    use crate::fuzz::case_source::{CaseSetV1, ExplicitCaseV1, CASE_SET_SCHEMA_V1};
    use crate::fuzz::repro::ReproManifest;
    use crate::fuzz::{FileSpec, FixtureBlueprint, GeneratedCase};
    use crate::utils::cli::Cli;
    use clap::Parser;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::sync::Mutex;

    // Library-level fuzz calls share the process-owned work root; keep their lifetimes disjoint.
    static FUZZ_RUN_LOCK: Mutex<()> = Mutex::new(());

    fn write_cases(root: &Path, utility: &str) -> PathBuf {
        let path = root.join("cases.json");
        let cases = CaseSetV1 {
            schema_version: CASE_SET_SCHEMA_V1.to_string(),
            util: utility.to_string(),
            cases: vec![ExplicitCaseV1 {
                id: "file".to_string(),
                case: GeneratedCase {
                    argv: vec!["file".to_string()],
                    fixture: FixtureBlueprint {
                        directories: Vec::new(),
                        files: vec![FileSpec {
                            relative_path: PathBuf::from("file"),
                            bytes: b"same content".to_vec(),
                            mode: 0o644,
                        }],
                        symlinks: Vec::new(),
                        hardlinks: Vec::new(),
                    },
                    stdin: Vec::new(),
                    cwd: PathBuf::from("."),
                },
            }],
        };
        fs::write(&path, serde_json::to_vec(&cases).unwrap()).unwrap();
        path
    }

    fn run_incomplete_fuzz(root: &Path, utility: &str, dut: &str) -> (String, PathBuf) {
        let _guard = FUZZ_RUN_LOCK.lock().unwrap();
        let cases = write_cases(root, utility);
        let metrics = root.join("metrics.json");
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            utility,
            "--ref-bin",
            "/bin/true",
            "--dut-bin",
            dut,
            "--dut-kind",
            "native",
            "--iterations",
            "1",
            "--seed",
            "991",
            "--shrink-attempts",
            "0",
            "--case-set",
            cases.to_str().unwrap(),
            "--metrics-out",
            metrics.to_str().unwrap(),
        ])
        .unwrap();
        let error = crate::run_cli(cli).unwrap_err();
        assert!(
            error.contains("FUZZER_OUTCOME=incomplete_coverage"),
            "{error}"
        );
        let bundle = error
            .lines()
            .find_map(|line| line.strip_prefix("raw observation bundle: "))
            .expect("incomplete execution preserves raw evidence");
        (error.clone(), PathBuf::from(bundle))
    }

    // A time utility's unequal output remains raw evidence until both executions have time evidence.
    #[test]
    fn time_coverage_does_not_label_unobserved_time_output_a_semantic_mismatch() {
        let root = tempfile::tempdir().unwrap();
        let (_, bundle) = run_incomplete_fuzz(root.path(), "stat", "/bin/echo");
        let manifest: ReproManifest =
            serde_json::from_slice(&fs::read(bundle.join("manifest.json")).unwrap()).unwrap();
        assert!(matches!(
            manifest.comparison.evaluated.observable,
            crate::fuzz::CompareResult::Mismatch {
                stdout_diff: true,
                ..
            }
        ));
        assert_eq!(
            manifest.comparison.evaluated.verdict(),
            CaseVerdict::IncompleteCoverage
        );
    }
}
