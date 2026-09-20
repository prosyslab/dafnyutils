use super::case_source::{CaseGenerationLimits, CaseSource};
use super::compare::report_mismatch;
use super::container::CommandCaseExecutor;
use super::corpus::InterestingCorpus;
use super::coverage::OptionCoverage;
use super::fixture::current_read_only_time_anchor;
use super::metrics::{
    case_fingerprint, duration_ns, error_outcome, CampaignMode, CaseMetricsV1, CoverageMetricsV1,
    MetricsRecorder, StageDurations,
};
use super::repro::save_case_evaluation;
use super::runtime::resolve_fuzz_paths;
use super::semantic::SemanticCoverage;
use super::shrink::{evaluate_case_with_executor, shrink_mismatch_with_executor, CaseExecutor};
use super::time_coverage::CaseVerdict;
use crate::utils::capabilities::require_fuzz_capability;
use crate::utils::chmod_campaign::{current_process_umask, selected_chmod_umask};
use crate::utils::cli::{parse_option_pool, FuzzArgs};
use crate::{fuzzer_outcome_marker, INCOMPLETE_COVERAGE, SEMANTIC_MISMATCH};
use rand::rngs::StdRng;
use rand::SeedableRng;
use std::time::Instant;

pub fn run_fuzzer(mut args: FuzzArgs) -> Result<(), String> {
    require_fuzz_capability(&args.common.util)?;
    args.process_umask = Some(current_process_umask()?);
    if matches!(args.common.util.as_str(), "ls" | "stat") {
        args.read_only_time_anchor_seconds = Some(current_read_only_time_anchor()?);
    }
    let seed = args.common.seed.unwrap_or_else(rand::random);
    let mut rng = StdRng::seed_from_u64(seed);
    let paths = resolve_fuzz_paths(&args)?;
    print_campaign_configuration(&args, &paths, seed);
    let mut executor = CommandCaseExecutor::create(&args, &paths)?;
    args.container_image_id = Some(executor.image_id().unwrap_or("local-test").to_string());
    let option_pool = match args.common.opts.as_deref() {
        Some(options) => parse_option_pool(Some(options)),
        None => executor.discover_common_options(std::time::Duration::from_secs(
            args.process_timeout_seconds,
        ))?,
    };
    println!(
        "  Image ID   : {}",
        executor.image_id().unwrap_or("local-test")
    );
    println!(
        "  Option pool: {} ({})",
        option_pool.len(),
        if args.common.opts.is_some() {
            "provided"
        } else {
            "discovered"
        }
    );
    let mut option_coverage = OptionCoverage::new(&option_pool);
    let mut semantic_coverage = SemanticCoverage::default();
    let mut corpus = InterestingCorpus::default();
    let case_source = CaseSource::load(
        args.common.case_set.as_deref(),
        &args.common.util,
        args.common.iterations,
    )?;
    let mut metrics = MetricsRecorder::new(
        args.common.metrics_out.clone(),
        CampaignMode::Fuzz,
        &args.common.util,
        seed,
        args.common.iterations,
    );
    metrics.set_configuration("process_timeout_seconds", args.process_timeout_seconds);
    metrics.set_configuration("workdir_mode", workdir_mode_label(args.common.workdir_mode));
    metrics.set_configuration("case_set", args.common.case_set.is_some());
    metrics.set_configuration("max_args", args.common.max_args);
    metrics.set_configuration("max_fs_entries", args.common.max_fs_entries);
    if let Err(error) = configure_metrics(&mut metrics, &args, &paths, &option_pool, seed) {
        return Err(metrics.finish_preserving_error(error));
    }
    args.common.work_root = Some(executor.work_root_base().to_path_buf());
    metrics.set_configuration("execution_backend", executor.backend_name());
    metrics.set_configuration("container_image", &args.common.container_image);
    metrics.set_configuration(
        "container_image_id",
        executor.image_id().unwrap_or("local-test"),
    );
    metrics.set_configuration("target_uid", args.common.target_uid);
    metrics.set_configuration("target_gid", args.common.target_gid);
    metrics.set_configuration("work_root_source", executor.work_root_source());
    metrics.set_configuration("work_root_base", executor.work_root_base().display());
    metrics.set_configuration("work_root_path", executor.work_root_path().display());

    let target_iterations = args.common.iterations;

    for attempt in 0..target_iterations {
        let result = run_single_iteration(
            &args,
            seed,
            attempt,
            &paths,
            &option_pool,
            &mut option_coverage,
            &mut semantic_coverage,
            &mut corpus,
            &mut executor,
            &mut rng,
            &case_source,
            &mut metrics,
        );
        if let Err(error) = result {
            return finish_campaign(metrics, &option_coverage, &semantic_coverage, Err(error));
        }
    }

    finish_campaign(metrics, &option_coverage, &semantic_coverage, Ok(()))
}

fn print_campaign_configuration(args: &FuzzArgs, paths: &super::ResolvedPaths, seed: u64) {
    println!("\n=== Coreutils fuzz campaign ===\nConfiguration");
    println!("  Utility    : {}", args.common.util);
    println!("  Seed       : {seed}");
    println!("  Budget     : {} iterations", args.common.iterations);
    println!(
        "  Reference  : {:?} ({:?})",
        paths.reference.path, paths.reference.kind
    );
    println!("  DUT        : {:?} ({:?})", paths.dut.path, paths.dut.kind);
    println!(
        "  Case source: {}",
        args.common
            .case_set
            .as_ref()
            .map(|path| format!("explicit {:?}", path))
            .unwrap_or_else(
                || "generated (scenarios, random inputs and corpus mutation)".to_string()
            )
    );
    println!(
        "  Limits     : max_args={} max_fs_entries={} timeout={}s shrink_attempts={}",
        args.common.max_args,
        args.common.max_fs_entries,
        args.process_timeout_seconds,
        args.shrink_attempts
    );
    println!(
        "  Comparison : stderr={} workdir={}",
        if args.ignore_stderr {
            "ignored"
        } else {
            "included"
        },
        workdir_mode_label(args.common.workdir_mode)
    );
    println!("  Image      : {}", args.common.container_image);
    println!(
        "  Identity   : uid={} gid={}",
        args.common.target_uid, args.common.target_gid
    );
    println!(
        "  Metrics    : {}",
        args.common
            .metrics_out
            .as_ref()
            .map(|path| format!("{:?}", path))
            .unwrap_or_else(|| "disabled".to_string())
    );
}

fn finish_campaign(
    mut metrics: MetricsRecorder,
    option_coverage: &OptionCoverage,
    semantic_coverage: &SemanticCoverage,
    result: Result<(), String>,
) -> Result<(), String> {
    metrics.set_coverage(coverage_metrics(option_coverage, semantic_coverage));
    let population = metrics.render_population_report();
    let result = match result {
        Ok(()) => metrics.finish(),
        Err(error) => Err(metrics.finish_preserving_error(error)),
    };
    println!("Coverage");
    println!("  {}", option_coverage.render_report());
    println!("  {}", semantic_coverage.render_report());
    println!("Results");
    println!("{population}");
    println!(
        "  Status     : {}",
        if result.is_ok() {
            "PASS - all requested iterations matched; no mismatch found"
        } else {
            "FAIL - campaign did not finish successfully; see error details"
        }
    );
    println!("=== End campaign ===");
    result
}

fn workdir_mode_label(mode: crate::utils::cli::WorkdirMode) -> &'static str {
    match mode {
        crate::utils::cli::WorkdirMode::PerIteration => "per-iteration",
        crate::utils::cli::WorkdirMode::Shared => "shared",
    }
}

#[allow(clippy::too_many_arguments)]
fn run_single_iteration(
    args: &FuzzArgs,
    seed: u64,
    iteration: usize,
    paths: &super::ResolvedPaths,
    option_pool: &[String],
    option_coverage: &mut OptionCoverage,
    semantic_coverage: &mut SemanticCoverage,
    corpus: &mut InterestingCorpus,
    executor: &mut dyn CaseExecutor,
    rng: &mut StdRng,
    case_source: &CaseSource,
    metrics: &mut MetricsRecorder,
) -> Result<(), String> {
    let source_started = Instant::now();
    let sourced = case_source.select_fuzz_case(
        &args.common.util,
        option_pool,
        rng,
        iteration,
        CaseGenerationLimits {
            max_args: args.common.max_args,
            max_fs_entries: args.common.max_fs_entries,
        },
        corpus,
    );
    let source_ns = duration_ns(source_started.elapsed());
    let case_id = sourced.id;
    let case_origin = sourced.origin;
    let transformed_from = sourced.transformed_from;
    let case = sourced.case;
    let fingerprint = case_fingerprint(&case);
    metrics.submit();
    let evaluation_started = Instant::now();
    let evaluation =
        match evaluate_case_with_executor(args, executor, seed, iteration, iteration, &case) {
            Ok(evaluation) => evaluation,
            Err(error) => {
                metrics.complete(CaseMetricsV1 {
                    comparison: None,
                    id: case_id,
                    origin: case_origin,
                    transformed_from,
                    case_fingerprint: fingerprint,
                    outcome: error_outcome(&error),
                    durations: StageDurations {
                        source_ns,
                        evaluation_ns: duration_ns(evaluation_started.elapsed()),
                        ..StageDurations::default()
                    },
                });
                return Err(error);
            }
        };
    let evaluation_ns = duration_ns(evaluation_started.elapsed());
    let coverage_started = Instant::now();
    let discovered_new_semantics = semantic_coverage.observe_case(
        &args.common.util,
        &evaluation.case,
        &evaluation.reference,
        &evaluation.pre_fs,
        &evaluation.reference_fs,
    );
    corpus.maybe_add(&evaluation.case, discovered_new_semantics);
    let coverage_ns = duration_ns(coverage_started.elapsed());

    match evaluation.comparison.verdict() {
        CaseVerdict::Match => {
            option_coverage.observe_case(&evaluation.case.argv);
            metrics.complete(CaseMetricsV1 {
                comparison: Some(evaluation.comparison.clone()),
                id: case_id,
                origin: case_origin,
                transformed_from,
                case_fingerprint: fingerprint,
                outcome: "match".to_string(),
                durations: StageDurations {
                    source_ns,
                    evaluation_ns,
                    coverage_ns,
                    ..StageDurations::default()
                },
            });
            Ok(())
        }
        CaseVerdict::IncompleteCoverage => {
            let persist_started = Instant::now();
            let saved = save_case_evaluation(args, seed, iteration, paths, &evaluation);
            metrics.complete(CaseMetricsV1 {
                comparison: Some(evaluation.comparison.clone()),
                id: case_id,
                origin: case_origin,
                transformed_from,
                case_fingerprint: fingerprint,
                outcome: INCOMPLETE_COVERAGE.to_string(),
                durations: StageDurations {
                    source_ns,
                    evaluation_ns,
                    coverage_ns,
                    persist_ns: duration_ns(persist_started.elapsed()),
                    ..StageDurations::default()
                },
            });
            let evidence = match saved {
                Ok(path) => format!("raw observation bundle: {}", path.display()),
                Err(error) => format!("failed to save raw observation bundle: {error}"),
            };
            Err(format!(
                "{}\ntime coverage is incomplete for util={}: {:?}\n{evidence}",
                fuzzer_outcome_marker(INCOMPLETE_COVERAGE),
                args.common.util,
                evaluation.comparison.time_coverage
            ))
        }
        CaseVerdict::Mismatch => {
            let shrink_started = Instant::now();
            let shrunk = match shrink_mismatch_with_executor(
                args,
                executor,
                seed,
                iteration,
                evaluation,
                args.shrink_attempts,
            ) {
                Ok(shrunk) => shrunk,
                Err(error) => {
                    metrics.complete(CaseMetricsV1 {
                        comparison: None,
                        id: case_id,
                        origin: case_origin,
                        transformed_from,
                        case_fingerprint: fingerprint,
                        outcome: error_outcome(&error),
                        durations: StageDurations {
                            source_ns,
                            evaluation_ns,
                            coverage_ns,
                            shrink_ns: duration_ns(shrink_started.elapsed()),
                            ..StageDurations::default()
                        },
                    });
                    return Err(error);
                }
            };
            let shrink_ns = duration_ns(shrink_started.elapsed());
            option_coverage.observe_case(&shrunk.case.argv);
            report_mismatch(
                seed,
                iteration,
                &args.common.util,
                &shrunk.case.argv,
                &shrunk.reference,
                &shrunk.dut,
                &shrunk.comparison.observable,
            );
            let persist_started = Instant::now();
            if let Err(error) = save_case_evaluation(args, seed, iteration, paths, &shrunk)
                .map_err(|e| format!("failed to save repro bundle: {e}"))
            {
                metrics.complete(CaseMetricsV1 {
                    comparison: None,
                    id: case_id,
                    origin: case_origin,
                    transformed_from,
                    case_fingerprint: fingerprint,
                    outcome: error_outcome(&error),
                    durations: StageDurations {
                        source_ns,
                        evaluation_ns,
                        coverage_ns,
                        shrink_ns,
                        persist_ns: duration_ns(persist_started.elapsed()),
                        ..StageDurations::default()
                    },
                });
                return Err(error);
            }
            let persist_ns = duration_ns(persist_started.elapsed());
            metrics.complete(CaseMetricsV1 {
                comparison: Some(shrunk.comparison.clone()),
                id: case_id,
                origin: case_origin,
                transformed_from,
                case_fingerprint: fingerprint,
                outcome: "mismatch".to_string(),
                durations: StageDurations {
                    source_ns,
                    evaluation_ns,
                    coverage_ns,
                    shrink_ns,
                    persist_ns,
                    ..StageDurations::default()
                },
            });
            Err(format!(
                "{}\nworld mismatch detected",
                fuzzer_outcome_marker(SEMANTIC_MISMATCH)
            ))
        }
    }
}

fn configure_metrics(
    metrics: &mut MetricsRecorder,
    args: &FuzzArgs,
    paths: &super::ResolvedPaths,
    option_pool: &[String],
    seed: u64,
) -> Result<(), String> {
    if !metrics.is_enabled() {
        return Ok(());
    }
    metrics.set_target_configuration("reference", &paths.reference)?;
    metrics.set_target_configuration("dut", &paths.dut)?;
    metrics.set_artifact_configuration(
        "fuzzer_executable",
        &std::env::current_exe()
            .map_err(|error| format!("failed to resolve current fuzzer executable: {error}"))?,
    )?;
    if let Some(case_set) = args.common.case_set.as_deref() {
        metrics.set_input_file_configuration("case_set", case_set)?;
    } else {
        metrics.set_configuration("case_set_path", "generated");
    }
    metrics.set_configuration(
        "option_pool",
        serde_json::to_string(option_pool)
            .map_err(|error| format!("failed to serialize option pool for metrics: {error}"))?,
    );
    metrics.set_configuration("ignore_stderr", args.ignore_stderr);
    metrics.set_configuration("shrink_attempts", args.shrink_attempts);
    if args.common.util == "chmod" {
        let schedule: Vec<String> = (0..args.common.iterations)
            .map(|iteration| format!("{:#05o}", selected_chmod_umask(seed, iteration)))
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
            args.process_umask
                .map(|value| format!("{value:#05o}"))
                .unwrap_or_else(|| "unavailable".to_string()),
        );
    }
    metrics.set_configuration(
        "read_only_time_anchor_seconds",
        args.read_only_time_anchor_seconds
            .map(|value| value.to_string())
            .unwrap_or_else(|| "none".to_string()),
    );
    Ok(())
}

fn coverage_metrics(
    option_coverage: &OptionCoverage,
    semantic_coverage: &SemanticCoverage,
) -> CoverageMetricsV1 {
    let (option_singles_seen, option_singles_total, option_pairs_seen, option_pairs_total) =
        option_coverage.counts();
    let (semantic_buckets_seen, semantic_buckets_total) = semantic_coverage.counts();
    CoverageMetricsV1 {
        option_singles_seen,
        option_singles_total,
        option_pairs_seen,
        option_pairs_total,
        semantic_buckets_seen,
        semantic_buckets_total,
    }
}

#[cfg(test)]
mod tests {
    use super::run_fuzzer;
    use crate::fuzz::case_source::{CaseSetV1, ExplicitCaseV1, CASE_SET_SCHEMA_V1};
    use crate::fuzz::{FixtureBlueprint, GeneratedCase};
    use crate::utils::cli::{Cli, CliCommand};
    use clap::Parser;
    use std::fs;
    use std::path::PathBuf;

    // A real target timeout remains a completed case with its exact input and reproducible settings.
    #[cfg(target_os = "linux")]
    #[test]
    fn target_timeout_writes_completed_error_metrics() {
        let root = tempfile::tempdir().unwrap();
        let case_set = root.path().join("cases.json");
        let metrics = root.path().join("metrics.json");
        let set = CaseSetV1 {
            schema_version: CASE_SET_SCHEMA_V1.to_string(),
            util: "cat".to_string(),
            cases: vec![ExplicitCaseV1 {
                id: "timeout-input".to_string(),
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
        };
        fs::write(&case_set, serde_json::to_vec(&set).unwrap()).unwrap();
        let cli = Cli::try_parse_from([
            "coreutils_fuzzer",
            "fuzz",
            "--util",
            "cat",
            "--ref-bin",
            "/bin/cat",
            "--dut-bin",
            "/usr/bin/yes",
            "--dut-kind",
            "native",
            "--iterations",
            "1",
            "--seed",
            "9",
            "--process-timeout-seconds",
            "1",
            "--case-set",
            case_set.to_str().unwrap(),
            "--metrics-out",
            metrics.to_str().unwrap(),
        ])
        .unwrap();
        let CliCommand::Fuzz(args) = cli.command else {
            unreachable!()
        };

        let error = run_fuzzer(args).unwrap_err();
        let document: serde_json::Value =
            serde_json::from_slice(&fs::read(metrics).unwrap()).unwrap();

        assert!(error.contains("FUZZER_OUTCOME=fuzzer_timeout"));
        assert_eq!(document["requested"], 1);
        assert_eq!(document["submitted"], 1);
        assert_eq!(document["completed"], 1);
        assert_eq!(document["outcomes"]["fuzzer_timeout"], 1);
        assert_eq!(document["cases"][0]["id"], "timeout-input");
        assert_eq!(document["cases"][0]["origin"], "explicit");
        assert!(document["cases"][0]["case_fingerprint"]
            .as_str()
            .unwrap()
            .starts_with("fnv1a64:"));
        for key in [
            "reference_path",
            "reference_kind",
            "reference_artifact_fingerprint",
            "dut_path",
            "dut_kind",
            "dut_artifact_fingerprint",
            "fuzzer_executable_artifact_fingerprint",
            "ignore_stderr",
            "option_pool",
            "shrink_attempts",
            "case_set_path",
            "case_set_artifact_fingerprint",
            "process_umask",
            "read_only_time_anchor_seconds",
        ] {
            assert!(document["configuration"].get(key).is_some(), "{key}");
        }
    }
    // A completed campaign cannot pass when its requested evidence file would overwrite a run.
    #[test]
    fn completed_campaign_rejects_existing_metrics_file() {
        let root = tempfile::tempdir().unwrap();
        let path = root.path().join("metrics.json");
        fs::write(&path, "original evidence").unwrap();
        let mut metrics =
            super::MetricsRecorder::new(Some(path.clone()), super::CampaignMode::Fuzz, "cat", 1, 1);
        metrics.submit();
        metrics.complete(super::CaseMetricsV1 {
            id: "completed".to_string(),
            origin: crate::fuzz::case_source::CaseOrigin::Explicit,
            transformed_from: None,
            case_fingerprint: "test-input".to_string(),
            outcome: "match".to_string(),
            comparison: None,
            durations: super::StageDurations::default(),
        });
        let error =
            super::finish_campaign(metrics, &Default::default(), &Default::default(), Ok(()))
                .unwrap_err();
        assert!(error.contains("refusing to overwrite"));
        assert_eq!(fs::read_to_string(path).unwrap(), "original evidence");
    }
}
