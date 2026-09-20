use super::case_source::{load_case_set, CaseOrigin, CaseSetV1};
use super::container::CommandCaseExecutor;
use super::fixture::current_read_only_time_anchor;
use super::metrics::{
    case_fingerprint, duration_ns, error_outcome, CampaignMode, CaseMetricsV1, MetricsRecorder,
    StageDurations,
};
use super::repro::save_case_evaluation;
use super::runtime::resolve_fuzz_paths;
use super::shrink::evaluate_case_with_executor;
use super::time_coverage::CaseVerdict;
use crate::utils::capabilities::require_fuzz_capability;
use crate::utils::chmod_campaign::{current_process_umask, selected_chmod_umask};
use crate::utils::cli::{CampaignArgs, FuzzArgs, RegressionArgs, WorkdirMode};
use crate::{fuzzer_outcome_marker, INCOMPLETE_COVERAGE, REGRESSION_FAILURE};
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

const REGRESSION_SCHEMA_V1: &str = "coreutils-fuzzer.regression-suite.v1";

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum RegressionExpectation {
    Match,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RegressionCaseV1 {
    pub(crate) case_id: String,
    pub(crate) expect: RegressionExpectation,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct RegressionSuiteV1 {
    pub(crate) schema_version: String,
    pub(crate) util: String,
    pub(crate) case_set: PathBuf,
    pub(crate) expectations: Vec<RegressionCaseV1>,
}

pub(crate) fn run_regression(args: RegressionArgs) -> Result<(), String> {
    let suite = load_suite(&args.suite)?;
    let suite_parent = args.suite.parent().unwrap_or_else(|| Path::new("."));
    let case_set_path = if suite.case_set.is_absolute() {
        suite.case_set.clone()
    } else {
        suite_parent.join(&suite.case_set)
    };
    let case_set = load_case_set(
        &case_set_path,
        &suite.util,
        suite_case_count(&case_set_path)?,
    )?;
    validate_suite(&suite, &case_set)?;
    require_fuzz_capability(&suite.util)?;

    let seed = 1;
    let common = CampaignArgs {
        util: suite.util.clone(),
        ref_bin: args.ref_bin.clone(),
        ref_kind: args.ref_kind,
        opts: None,
        iterations: case_set.cases.len(),
        seed: Some(seed),
        max_args: case_set
            .cases
            .iter()
            .map(|entry| entry.case.argv.len())
            .max()
            .unwrap_or_default(),
        max_fs_entries: case_set
            .cases
            .iter()
            .map(|entry| fixture_entry_count(&entry.case.fixture))
            .max()
            .unwrap_or_default(),
        workdir_mode: WorkdirMode::PerIteration,
        case_set: None,
        metrics_out: None,
        work_root: args.work_root.clone(),
        container_image: args.container_image.clone(),
        target_uid: args.target_uid,
        target_gid: args.target_gid,
    };
    let mut fuzz_args = FuzzArgs {
        common: common.clone(),
        dut_bin: args.dut_bin.clone(),
        dut_kind: args.dut_kind,
        shrink_attempts: 0,
        process_timeout_seconds: args.process_timeout_seconds,
        ignore_stderr: args.ignore_stderr,
        read_only_time_anchor_seconds: None,
        process_umask: Some(current_process_umask()?),
        container_image_id: None,
    };
    if matches!(suite.util.as_str(), "ls" | "stat") {
        fuzz_args.read_only_time_anchor_seconds = Some(current_read_only_time_anchor()?);
    }
    let fuzz_paths = resolve_fuzz_paths(&fuzz_args)?;
    let mut executor = CommandCaseExecutor::create(&fuzz_args, &fuzz_paths)?;
    fuzz_args.container_image_id = Some(executor.image_id().unwrap_or("local-test").to_string());
    fuzz_args.common.work_root = Some(executor.work_root_base().to_path_buf());
    let mut metrics = MetricsRecorder::new(
        args.metrics_out.clone(),
        CampaignMode::Regression,
        &suite.util,
        seed,
        suite.expectations.len(),
    );
    metrics.set_configuration("process_timeout_seconds", args.process_timeout_seconds);
    metrics.set_configuration("verifier_internal_cores", "host-default");
    metrics.set_configuration("workdir_mode", "per-iteration");
    metrics.set_configuration("case_set", case_set_path.display());
    metrics.set_configuration("execution_backend", executor.backend_name());
    metrics.set_configuration("container_image", &args.container_image);
    metrics.set_configuration(
        "container_image_id",
        executor.image_id().unwrap_or("local-test"),
    );
    metrics.set_configuration("target_uid", args.target_uid);
    metrics.set_configuration("target_gid", args.target_gid);
    metrics.set_configuration("work_root_source", executor.work_root_source());
    metrics.set_configuration("work_root_base", executor.work_root_base().display());
    metrics.set_configuration("work_root_path", executor.work_root_path().display());
    if let Err(error) = configure_metrics(
        &mut metrics,
        &args,
        &suite,
        &case_set_path,
        &fuzz_paths,
        &fuzz_args,
    ) {
        return Err(metrics.finish_preserving_error(error));
    }
    let mut failures = Vec::new();
    let mut incomplete_coverage = false;

    for (iteration, expectation) in suite.expectations.iter().enumerate() {
        let entry = case_set
            .cases
            .iter()
            .find(|entry| entry.id == expectation.case_id)
            .expect("validated regression case id");
        let fingerprint = case_fingerprint(&entry.case);
        metrics.submit();
        let mut comparison = None;
        let (outcome, error, durations) = match expectation.expect {
            RegressionExpectation::Match => {
                let evaluation_started = Instant::now();
                let result = match evaluate_case_with_executor(
                    &fuzz_args,
                    &mut executor,
                    seed,
                    iteration,
                    iteration,
                    &entry.case,
                ) {
                    Ok(evaluation) => {
                        let verdict = evaluation.comparison.verdict();
                        comparison = Some(evaluation.comparison.clone());
                        match verdict {
                            CaseVerdict::Match => ("match".to_string(), None),
                            CaseVerdict::IncompleteCoverage => {
                                incomplete_coverage = true;
                                let evidence = match save_case_evaluation(
                                    &fuzz_args,
                                    seed,
                                    iteration,
                                    &fuzz_paths,
                                    &evaluation,
                                ) {
                                    Ok(path) => {
                                        format!("raw observation bundle: {}", path.display())
                                    }
                                    Err(error) => {
                                        format!("failed to save raw observation bundle: {error}")
                                    }
                                };
                                (INCOMPLETE_COVERAGE.to_string(), Some(format!(
                                "case `{}` expected Match but per-execution time evidence is incomplete\n{evidence}", entry.id)))
                            }
                            CaseVerdict::Mismatch => (
                                "mismatch".to_string(),
                                Some(format!(
                                "case `{}` expected Match but the comparator reported a mismatch",
                                entry.id
                            )),
                            ),
                        }
                    }
                    Err(error) => {
                        let outcome = error_outcome(&error);
                        (
                            outcome,
                            Some(format!(
                                "case `{}` Match execution failed: {error}",
                                entry.id
                            )),
                        )
                    }
                };
                (
                    result.0,
                    result.1,
                    StageDurations {
                        evaluation_ns: duration_ns(evaluation_started.elapsed()),
                        ..StageDurations::default()
                    },
                )
            }
        };
        metrics.complete(CaseMetricsV1 {
            comparison,
            id: format!("{}:{:?}", entry.id, expectation.expect).to_ascii_lowercase(),
            origin: CaseOrigin::Explicit,
            transformed_from: None,
            case_fingerprint: fingerprint,
            outcome,
            durations,
        });
        if let Some(error) = error {
            failures.push(error);
        }
    }

    if failures.is_empty() {
        metrics.finish()?;
        println!(
            "Regression suite passed for util={} expectations={}",
            suite.util,
            suite.expectations.len()
        );
        Ok(())
    } else {
        let error = format!(
            "{}\n{}",
            fuzzer_outcome_marker(if incomplete_coverage {
                INCOMPLETE_COVERAGE
            } else {
                REGRESSION_FAILURE
            }),
            failures.join("\n")
        );
        Err(metrics.finish_preserving_error(error))
    }
}

#[allow(clippy::too_many_arguments)]
fn configure_metrics(
    metrics: &mut MetricsRecorder,
    args: &RegressionArgs,
    suite: &RegressionSuiteV1,
    case_set_path: &Path,
    fuzz_paths: &super::ResolvedPaths,
    fuzz_args: &FuzzArgs,
) -> Result<(), String> {
    if !metrics.is_enabled() {
        return Ok(());
    }
    metrics.set_target_configuration("reference", &fuzz_paths.reference)?;
    metrics.set_target_configuration("dut", &fuzz_paths.dut)?;
    metrics.set_artifact_configuration(
        "fuzzer_executable",
        &std::env::current_exe()
            .map_err(|error| format!("failed to resolve current fuzzer executable: {error}"))?,
    )?;
    metrics.set_input_file_configuration("regression_suite", &args.suite)?;
    metrics.set_input_file_configuration("case_set", case_set_path)?;
    metrics.set_configuration("option_pool", "[]");
    metrics.set_configuration("ignore_stderr", args.ignore_stderr);
    metrics.set_configuration("shrink_attempts", 0);
    if suite.util == "chmod" {
        let schedule: Vec<String> = (0..suite.expectations.len())
            .map(|iteration| format!("{:#05o}", selected_chmod_umask(1, iteration)))
            .collect();
        metrics.set_configuration(
            "process_umask_schedule",
            serde_json::to_string(&schedule).map_err(|error| {
                format!("failed to serialize chmod umask schedule for metrics: {error}")
            })?,
        );
    } else {
        metrics.set_configuration(
            "process_umask",
            fuzz_args
                .process_umask
                .map(|value| format!("{value:#05o}"))
                .unwrap_or_else(|| "unavailable".to_string()),
        );
    }
    metrics.set_configuration(
        "read_only_time_anchor_seconds",
        fuzz_args
            .read_only_time_anchor_seconds
            .map(|value| value.to_string())
            .unwrap_or_else(|| "none".to_string()),
    );
    Ok(())
}

fn load_suite(path: &Path) -> Result<RegressionSuiteV1, String> {
    let bytes = fs::read(path).map_err(|error| {
        format!(
            "failed to read regression suite `{}`: {error}",
            path.display()
        )
    })?;
    let suite: RegressionSuiteV1 = serde_json::from_slice(&bytes).map_err(|error| {
        format!(
            "failed to decode regression suite `{}`: {error}",
            path.display()
        )
    })?;
    if suite.schema_version != REGRESSION_SCHEMA_V1 {
        return Err(format!(
            "unsupported regression schema `{}`; expected `{REGRESSION_SCHEMA_V1}`",
            suite.schema_version
        ));
    }
    if suite.expectations.is_empty() {
        return Err("regression suite must contain at least one expectation".to_string());
    }
    Ok(suite)
}

fn suite_case_count(path: &Path) -> Result<usize, String> {
    let bytes = fs::read(path)
        .map_err(|error| format!("failed to read case set `{}`: {error}", path.display()))?;
    let value: serde_json::Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("failed to decode case set `{}`: {error}", path.display()))?;
    value
        .get("cases")
        .and_then(serde_json::Value::as_array)
        .map(Vec::len)
        .ok_or_else(|| "case set must contain a `cases` array".to_string())
}

fn validate_suite(suite: &RegressionSuiteV1, case_set: &CaseSetV1) -> Result<(), String> {
    let case_ids: BTreeSet<&str> = case_set
        .cases
        .iter()
        .map(|entry| entry.id.as_str())
        .collect();
    let mut used = BTreeSet::new();
    let mut pairs = BTreeSet::new();
    for expectation in &suite.expectations {
        if !case_ids.contains(expectation.case_id.as_str()) {
            return Err(format!(
                "regression expectation references unknown case id `{}`",
                expectation.case_id
            ));
        }
        if !pairs.insert((expectation.case_id.as_str(), expectation.expect)) {
            return Err(format!(
                "duplicate regression expectation for case `{}` and {:?}",
                expectation.case_id, expectation.expect
            ));
        }
        used.insert(expectation.case_id.as_str());
    }
    if used != case_ids {
        let missing: Vec<&str> = case_ids.difference(&used).copied().collect();
        return Err(format!(
            "regression suite omits case-set ids: {}",
            missing.join(", ")
        ));
    }
    Ok(())
}

fn fixture_entry_count(fixture: &super::FixtureBlueprint) -> usize {
    fixture.directories.len()
        + fixture.files.len()
        + fixture.symlinks.len()
        + fixture.hardlinks.len()
}

#[cfg(test)]
mod tests {
    use super::{
        load_suite, run_regression, validate_suite, RegressionCaseV1, RegressionExpectation,
        RegressionSuiteV1, REGRESSION_SCHEMA_V1,
    };
    use crate::fuzz::case_source::{CaseSetV1, ExplicitCaseV1, CASE_SET_SCHEMA_V1};
    use crate::fuzz::{FixtureBlueprint, GeneratedCase};
    use clap::Parser;
    use std::fs;
    use std::path::PathBuf;

    fn case_set() -> CaseSetV1 {
        CaseSetV1 {
            schema_version: CASE_SET_SCHEMA_V1.to_string(),
            util: "cat".to_string(),
            cases: vec![ExplicitCaseV1 {
                id: "stdin".to_string(),
                case: GeneratedCase {
                    argv: vec!["-".to_string()],
                    fixture: FixtureBlueprint {
                        directories: Vec::new(),
                        files: Vec::new(),
                        symlinks: Vec::new(),
                        hardlinks: Vec::new(),
                    },
                    stdin: b"input\n".to_vec(),
                    cwd: PathBuf::from("."),
                },
            }],
        }
    }

    // Every case in a regression case set must have an explicit expectation.
    #[test]
    fn regression_suite_rejects_unknown_or_omitted_cases() {
        let root = tempfile::tempdir().unwrap();
        let suite_path = root.path().join("suite.json");
        fs::write(
            &suite_path,
            br#"{"schema_version":"coreutils-fuzzer.regression-suite.v1","util":"cat","case_set":"cases.json","expectations":[{"case_id":"missing","expect":"match"}]}"#,
        )
        .unwrap();
        let suite = load_suite(&suite_path).unwrap();

        let error = validate_suite(&suite, &case_set()).unwrap_err();

        assert!(error.contains("unknown case id"));
    }

    fn write_match_suite(root: &std::path::Path) -> PathBuf {
        let cases = root.join("cases.json");
        fs::write(&cases, serde_json::to_vec(&case_set()).unwrap()).unwrap();
        let suite = root.join("suite.json");
        fs::write(
            &suite,
            serde_json::to_vec(&RegressionSuiteV1 {
                schema_version: REGRESSION_SCHEMA_V1.to_string(),
                util: "cat".to_string(),
                case_set: PathBuf::from("cases.json"),
                expectations: vec![RegressionCaseV1 {
                    case_id: "stdin".to_string(),
                    expect: RegressionExpectation::Match,
                }],
            })
            .unwrap(),
        )
        .unwrap();
        suite
    }

    // A fixed DUT that equals the reference satisfies a Match regression expectation.
    #[test]
    fn match_regression_accepts_equal_native_targets() {
        let root = tempfile::tempdir().unwrap();
        let suite = write_match_suite(root.path());
        let cli = crate::utils::cli::Cli::try_parse_from([
            "coreutils_fuzzer",
            "regression",
            "--suite",
            suite.to_str().unwrap(),
            "--ref-bin",
            "/bin/cat",
            "--dut-bin",
            "/bin/cat",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let crate::utils::cli::CliCommand::Regression(args) = cli.command else {
            unreachable!()
        };

        run_regression(args).unwrap();
    }

    // A still-broken DUT fails a Match regression instead of changing replay semantics.
    #[test]
    fn match_regression_rejects_different_native_target() {
        let root = tempfile::tempdir().unwrap();
        let suite = write_match_suite(root.path());
        let cli = crate::utils::cli::Cli::try_parse_from([
            "coreutils_fuzzer",
            "regression",
            "--suite",
            suite.to_str().unwrap(),
            "--ref-bin",
            "/bin/cat",
            "--dut-bin",
            "/bin/false",
            "--dut-kind",
            "native",
        ])
        .unwrap();
        let crate::utils::cli::CliCommand::Regression(args) = cli.command else {
            unreachable!()
        };

        let error = run_regression(args).unwrap_err();

        assert!(error.contains("FUZZER_OUTCOME=regression_failure"));
        assert!(error.contains("expected Match"));
    }
}
