use crate::fuzz::input::{self, InputGenerator};
use crate::{fuzzer_outcome_marker, FUZZER_UNSUPPORTED_CAPABILITY};
use serde::Serialize;

pub(crate) const TIME_BEHAVIOR_LIMITATION: &str = "Time-related bugs are outside fuzzer coverage. Raw output differences caused by clocks or file timestamps are inconclusive.";

pub const CAPABILITY_SCHEMA_VERSION: u32 = 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PathOperandPolicy {
    Default,
    Chmod,
    First,
    Tail,
}

/// Chooses supplied-byte delivery independently from whether a utility reads stdin.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StdinDeliveryPolicy {
    WhenConsumed,
    Supplied,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StdinPolicy {
    Never,
    Stream,
    Comm,
    Csplit,
    Tail,
    Uniq,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct UtilityCapability {
    pub(crate) utility: &'static str,
    pub(crate) input_generator: &'static dyn InputGenerator,
    pub(crate) help_exit_code: i32,
    pub(crate) generated_options: Option<&'static [&'static str]>,

    pub(crate) requires_root_cwd: bool,
    pub(crate) extra_runtime_files: &'static [&'static str],
    pub(crate) coverage_time_buckets: bool,
    pub(crate) path_operand_policy: PathOperandPolicy,
    pub(crate) stdin_policy: StdinPolicy,
    pub(crate) stdin_delivery: StdinDeliveryPolicy,
    pub(crate) controlled_fixture_times: bool,
    pub(crate) option_value_flags: &'static [&'static str],
}

macro_rules! capability {
    ($utility:literal, $generator:ident) => {
        UtilityCapability {
            utility: $utility,
            input_generator: &input::generators::$generator::GENERATOR,
            help_exit_code: 0,
            generated_options: None,
            requires_root_cwd: false,
            extra_runtime_files: &[],
            coverage_time_buckets: false,
            path_operand_policy: PathOperandPolicy::Default,
            stdin_policy: StdinPolicy::Never,
            stdin_delivery: StdinDeliveryPolicy::WhenConsumed,
            controlled_fixture_times: false,
            option_value_flags: &[],
        }
    };
}

pub(crate) static UTILITY_CAPABILITIES: &[UtilityCapability] = &[
    capability!("base64", base64),
    capability!("basename", basename),
    UtilityCapability {
        stdin_policy: StdinPolicy::Stream,
        ..capability!("cat", cat)
    },
    UtilityCapability {
        path_operand_policy: PathOperandPolicy::Chmod,
        stdin_delivery: StdinDeliveryPolicy::Supplied,
        option_value_flags: &["--reference"],
        controlled_fixture_times: true,
        ..capability!("chmod", chmod)
    },
    UtilityCapability {
        stdin_policy: StdinPolicy::Comm,
        option_value_flags: &["--output-delimiter"],
        ..capability!("comm", comm)
    },
    UtilityCapability {
        path_operand_policy: PathOperandPolicy::First,
        stdin_policy: StdinPolicy::Csplit,
        option_value_flags: &["-f", "--prefix", "-b", "--suffix-format", "-n", "--digits"],
        ..capability!("csplit", csplit)
    },
    UtilityCapability {
        stdin_policy: StdinPolicy::Stream,
        option_value_flags: &["-b", "--bytes", "-c", "--characters", "--output-delimiter"],
        ..capability!("cut", cut)
    },
    capability!("dirname", dirname),
    UtilityCapability {
        option_value_flags: &["-B", "--block-size"],
        requires_root_cwd: true,
        ..capability!("du", du)
    },
    capability!("echo", echo),
    UtilityCapability {
        stdin_policy: StdinPolicy::Stream,
        option_value_flags: &["-t", "--tabs"],
        ..capability!("expand", expand)
    },
    capability!("expr", expr),
    capability!("factor", factor),
    UtilityCapability {
        help_exit_code: 1,
        ..capability!("false", r#false)
    },
    UtilityCapability {
        generated_options: Some(&[
            "-b",
            "--bytes",
            "-s",
            "--spaces",
            "-w",
            "--width",
            "--help",
            "--version",
        ]),
        ..capability!("fold", fold)
    },
    UtilityCapability {
        stdin_policy: StdinPolicy::Stream,
        option_value_flags: &["-c", "--bytes", "-n", "--lines"],
        ..capability!("head", head)
    },
    capability!("link", link),
    capability!("ln", ln),
    capability!("logname", logname),
    UtilityCapability {
        option_value_flags: &["--block-size", "--time", "--time-style"],
        generated_options: Some(&[
            "-a",
            "--all",
            "-A",
            "--almost-all",
            "-d",
            "--directory",
            "-n",
            "--numeric-uid-gid",
            "-s",
            "--size",
            "--block-size",
            "--time-style",
            "-S",
            "-t",
            "-r",
            "--reverse",
            "-u",
            "-c",
            "--time",
            "-H",
            "--dereference-command-line",
            "-L",
            "--dereference",
            "-R",
            "--recursive",
            "--help",
            "--version",
        ]),
        requires_root_cwd: true,
        ..capability!("ls", ls)
    },
    UtilityCapability {
        option_value_flags: &["-t", "--target-directory", "-S", "--suffix"],
        ..capability!("mv", mv)
    },
    UtilityCapability {
        stdin_policy: StdinPolicy::Stream,
        option_value_flags: &[
            "-b",
            "--body-numbering",
            "-n",
            "--number-format",
            "-s",
            "--number-separator",
        ],
        ..capability!("nl", nl)
    },
    UtilityCapability {
        stdin_policy: StdinPolicy::Stream,
        option_value_flags: &["-d", "--delimiters"],
        ..capability!("paste", paste)
    },
    capability!("printenv", printenv),
    capability!("printf", printf),
    capability!("pwd", pwd),
    capability!("readlink", readlink),
    UtilityCapability {
        generated_options: Some(&[
            "-s",
            "--separator",
            "-w",
            "--equal-width",
            "--help",
            "--version",
        ]),
        ..capability!("seq", seq)
    },
    UtilityCapability {
        option_value_flags: &["-c", "--format"],
        generated_options: Some(&[
            "-L",
            "--dereference",
            "-c",
            "--format",
            "--help",
            "--version",
        ]),
        requires_root_cwd: true,
        ..capability!("stat", stat)
    },
    UtilityCapability {
        stdin_policy: StdinPolicy::Stream,
        ..capability!("tac", tac)
    },
    UtilityCapability {
        path_operand_policy: PathOperandPolicy::Tail,
        stdin_policy: StdinPolicy::Tail,
        option_value_flags: &["-c", "--bytes", "-n", "--lines"],
        ..capability!("tail", tail)
    },
    UtilityCapability {
        generated_options: Some(&[
            "-a",
            "--append",
            "-i",
            "--ignore-interrupts",
            "--help",
            "--version",
        ]),
        ..capability!("tee", tee)
    },
    UtilityCapability {
        option_value_flags: &["-d", "--date", "-r", "--reference", "-t", "--time"],
        extra_runtime_files: &["touch_time_parser"],
        coverage_time_buckets: true,
        ..capability!("touch", touch)
    },
    UtilityCapability {
        generated_options: Some(&[
            "-d",
            "--delete",
            "-s",
            "--squeeze-repeats",
            "--help",
            "--version",
        ]),
        ..capability!("tr", tr)
    },
    capability!("true", r#true),
    capability!("unlink", unlink),
    UtilityCapability {
        path_operand_policy: PathOperandPolicy::First,
        stdin_policy: StdinPolicy::Uniq,
        ..capability!("uniq", uniq)
    },
    UtilityCapability {
        stdin_policy: StdinPolicy::Stream,
        generated_options: Some(&[
            "-l",
            "--lines",
            "-w",
            "--words",
            "-m",
            "--chars",
            "-c",
            "--bytes",
            "-L",
            "--max-line-length",
            "--help",
            "--version",
        ]),
        ..capability!("wc", wc)
    },
];

pub(crate) fn capability_for(utility: &str) -> Option<&'static UtilityCapability> {
    UTILITY_CAPABILITIES
        .iter()
        .find(|capability| capability.utility == utility)
}

pub(crate) fn require_fuzz_capability(utility: &str) -> Result<&'static UtilityCapability, String> {
    capability_for(utility).ok_or_else(|| {
        format!(
            "{}\nunsupported fuzz utility `{utility}`; inspect `capabilities` for registered utilities",
            fuzzer_outcome_marker(FUZZER_UNSUPPORTED_CAPABILITY)
        )
    })
}

#[derive(Serialize)]
struct CapabilityDocument {
    schema_version: u32,
    utilities: Vec<CapabilityView>,
    limitations: Vec<&'static str>,
}

#[derive(Serialize)]
struct CapabilityView {
    utility: &'static str,
    fuzz_strategy: &'static str,
    deterministic_scenarios: bool,
}

pub(crate) fn render_capabilities_json() -> Result<String, String> {
    let document = CapabilityDocument {
        schema_version: CAPABILITY_SCHEMA_VERSION,
        limitations: vec![TIME_BEHAVIOR_LIMITATION],
        utilities: UTILITY_CAPABILITIES
            .iter()
            .map(|capability| CapabilityView {
                utility: capability.utility,
                fuzz_strategy: if capability.input_generator.has_utility_pattern() {
                    "custom"
                } else {
                    "generic"
                },
                deterministic_scenarios: true,
            })
            .collect(),
    };
    serde_json::to_string_pretty(&document)
        .map_err(|error| format!("failed to serialize capability registry: {error}"))
}

pub(crate) fn render_capabilities_text() -> String {
    UTILITY_CAPABILITIES
        .iter()
        .map(|capability| {
            let fuzz = if capability.input_generator.has_utility_pattern() {
                "custom"
            } else {
                "generic"
            };
            format!("{} fuzz={fuzz} scenarios=yes", capability.utility)
        })
        .chain(std::iter::once(format!(
            "Limitation: {TIME_BEHAVIOR_LIMITATION}"
        )))
        .collect::<Vec<_>>()
        .join("\n")
}

#[cfg(test)]
mod tests {
    use super::{render_capabilities_json, UTILITY_CAPABILITIES};
    use std::collections::BTreeSet;

    // The public capability document is versioned and each utility is registered once.
    #[test]
    fn capability_document_has_unique_versioned_entries() {
        let json: serde_json::Value =
            serde_json::from_str(&render_capabilities_json().unwrap()).unwrap();
        let utilities = json["utilities"].as_array().unwrap();
        let names: BTreeSet<_> = utilities
            .iter()
            .map(|entry| entry["utility"].as_str().unwrap())
            .collect();

        assert_eq!(json["schema_version"], super::CAPABILITY_SCHEMA_VERSION);
        assert!(!json.to_string().contains("descriptor"));
        assert!(!json.to_string().contains("events"));
        assert!(!json.to_string().contains("syscall"));
        assert_eq!(names.len(), UTILITY_CAPABILITIES.len());
        assert_eq!(json["limitations"][0], super::TIME_BEHAVIOR_LIMITATION);
    }

    // The unified generator registry preserves the complete utility-specific pattern allowlist.
    #[test]
    fn utility_argv_patterns_match_the_registered_utility_set() {
        let patterned: BTreeSet<_> = UTILITY_CAPABILITIES
            .iter()
            .filter(|capability| capability.input_generator.has_utility_pattern())
            .map(|capability| capability.utility)
            .collect();

        assert_eq!(
            patterned,
            BTreeSet::from([
                "cat", "chmod", "comm", "csplit", "cut", "du", "expand", "head", "link", "ln",
                "ls", "mv", "nl", "paste", "readlink", "stat", "tac", "tail", "touch", "uniq",
                "unlink", "wc",
            ])
        );
    }

    // Every advertised deterministic scenario reaches its registered scenario adapter.
    #[test]
    fn registered_scenario_adapters_produce_seed_cases() {
        for capability in UTILITY_CAPABILITIES {
            assert!(
                (0..128).any(|iteration| {
                    crate::fuzz::input::scenario_case(capability.utility, iteration).is_some()
                }),
                "{} has no deterministic scenario",
                capability.utility
            );
        }
    }
}
