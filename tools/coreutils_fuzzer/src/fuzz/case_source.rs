use super::corpus::InterestingCorpus;
use super::fixture::validate_fixture;
use super::input::scenario_case;
use super::mutation::{generate_case, mutate_case_from_corpus};
use super::GeneratedCase;
use rand::rngs::StdRng;
use rand::Rng;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Component, Path};

pub(crate) const CASE_SET_SCHEMA_V1: &str = "coreutils-fuzzer.case-set.v1";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct ExplicitCaseV1 {
    pub(crate) id: String,
    pub(crate) case: GeneratedCase,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct CaseSetV1 {
    pub(crate) schema_version: String,
    pub(crate) util: String,
    pub(crate) cases: Vec<ExplicitCaseV1>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum CaseOrigin {
    Explicit,
    Scenario,
    CorpusMutation,
    Random,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SourcedCase {
    pub(crate) id: String,
    pub(crate) origin: CaseOrigin,
    pub(crate) case: GeneratedCase,
    pub(crate) transformed_from: Option<String>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct CaseGenerationLimits {
    pub(crate) max_args: usize,
    pub(crate) max_fs_entries: usize,
}

#[derive(Debug, Clone)]
pub(crate) struct CaseSource {
    explicit: Option<CaseSetV1>,
}

impl CaseSource {
    pub(crate) fn load(path: Option<&Path>, util: &str, iterations: usize) -> Result<Self, String> {
        let explicit = match path {
            Some(path) => Some(load_case_set(path, util, iterations)?),
            None => None,
        };
        Ok(Self { explicit })
    }

    pub(crate) fn select_fuzz_case(
        &self,
        util: &str,
        option_pool: &[String],
        rng: &mut StdRng,
        iteration: usize,
        limits: CaseGenerationLimits,
        corpus: &InterestingCorpus,
    ) -> SourcedCase {
        if let Some(case) = self.explicit_case(iteration) {
            return case;
        }
        if let Some(case) = scenario_case(util, iteration) {
            return SourcedCase {
                id: format!("scenario-{iteration}"),
                origin: CaseOrigin::Scenario,
                case,
                transformed_from: None,
            };
        }
        if rng.random_bool(0.35) {
            if let Some(base) = corpus.choose(rng) {
                return SourcedCase {
                    id: format!("generated-{iteration}"),
                    origin: CaseOrigin::CorpusMutation,
                    case: mutate_case_from_corpus(
                        util,
                        option_pool,
                        rng,
                        limits.max_args,
                        limits.max_fs_entries,
                        &base,
                    ),
                    transformed_from: None,
                };
            }
        }
        SourcedCase {
            id: format!("generated-{iteration}"),
            origin: CaseOrigin::Random,
            case: generate_case(
                util,
                option_pool,
                rng,
                limits.max_args,
                limits.max_fs_entries,
            ),
            transformed_from: None,
        }
    }

    fn explicit_case(&self, iteration: usize) -> Option<SourcedCase> {
        let entry = self.explicit.as_ref()?.cases.get(iteration)?;
        Some(SourcedCase {
            id: entry.id.clone(),
            origin: CaseOrigin::Explicit,
            case: entry.case.clone(),
            transformed_from: None,
        })
    }
}

pub(crate) fn load_case_set(
    path: &Path,
    util: &str,
    iterations: usize,
) -> Result<CaseSetV1, String> {
    let bytes = fs::read(path)
        .map_err(|error| format!("failed to read case set `{}`: {error}", path.display()))?;
    let set: CaseSetV1 = serde_json::from_slice(&bytes)
        .map_err(|error| format!("failed to decode case set `{}`: {error}", path.display()))?;
    validate_case_set(&set, util, iterations)?;
    Ok(set)
}

fn validate_case_set(set: &CaseSetV1, util: &str, iterations: usize) -> Result<(), String> {
    if set.schema_version != CASE_SET_SCHEMA_V1 {
        return Err(format!(
            "unsupported case-set schema `{}`; expected `{CASE_SET_SCHEMA_V1}`",
            set.schema_version
        ));
    }
    if set.util != util {
        return Err(format!(
            "case-set utility `{}` does not match requested utility `{util}`",
            set.util
        ));
    }
    if set.cases.is_empty() {
        return Err("case set must contain at least one case".to_string());
    }
    if set.cases.len() != iterations {
        return Err(format!(
            "case-set cardinality mismatch: --iterations is {iterations}, but the case set contains {} cases",
            set.cases.len()
        ));
    }
    let mut ids = BTreeSet::new();
    for entry in &set.cases {
        if entry.id.is_empty() {
            return Err("case-set case id must not be empty".to_string());
        }
        if !ids.insert(entry.id.as_str()) {
            return Err(format!("duplicate case-set case id `{}`", entry.id));
        }
        validate_fixture(&entry.case.fixture)
            .map_err(|error| format!("invalid case `{}` fixture: {error}", entry.id))?;
        validate_case_cwd(&entry.case.cwd)
            .map_err(|error| format!("invalid case `{}`: {error}", entry.id))?;
    }
    Ok(())
}

fn validate_case_cwd(cwd: &Path) -> Result<(), String> {
    if cwd == Path::new(".") {
        return Ok(());
    }
    if cwd.as_os_str().is_empty()
        || cwd.is_absolute()
        || cwd.components().any(|component| {
            matches!(
                component,
                Component::CurDir
                    | Component::ParentDir
                    | Component::RootDir
                    | Component::Prefix(_)
            )
        })
    {
        return Err(format!(
            "cwd must be `.` or a normalized relative path: `{}`",
            cwd.display()
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{CaseGenerationLimits, CaseSetV1, CaseSource, ExplicitCaseV1, CASE_SET_SCHEMA_V1};
    use crate::fuzz::corpus::InterestingCorpus;
    use crate::fuzz::{FixtureBlueprint, GeneratedCase};
    use rand::SeedableRng;
    use std::fs;
    use std::path::PathBuf;

    fn case_set(count: usize) -> CaseSetV1 {
        CaseSetV1 {
            schema_version: CASE_SET_SCHEMA_V1.to_string(),
            util: "cat".to_string(),
            cases: (0..count)
                .map(|index| ExplicitCaseV1 {
                    id: format!("case-{index}"),
                    case: GeneratedCase {
                        argv: Vec::new(),
                        fixture: FixtureBlueprint {
                            directories: Vec::new(),
                            files: Vec::new(),
                            symlinks: Vec::new(),
                            hardlinks: Vec::new(),
                        },
                        stdin: format!("input-{index}\n").into_bytes(),
                        cwd: PathBuf::from("."),
                    },
                })
                .collect(),
        }
    }

    fn write_set(set: &CaseSetV1) -> tempfile::NamedTempFile {
        let file = tempfile::NamedTempFile::new().unwrap();
        fs::write(file.path(), serde_json::to_vec(set).unwrap()).unwrap();
        file
    }

    // An explicit case set preserves its ordered IDs and exact generated-case values.
    #[test]
    fn explicit_cases_are_loaded_without_transformation() {
        let expected = case_set(2);
        let file = write_set(&expected);
        let source = CaseSource::load(Some(file.path()), "cat", 2).unwrap();

        assert_eq!(source.explicit_case(0).unwrap().id, "case-0");
        assert_eq!(
            source.explicit_case(1).unwrap().case,
            expected.cases[1].case
        );
    }

    // A campaign cannot silently omit or repeat mandatory explicit cases.
    #[test]
    fn explicit_case_count_must_equal_iterations() {
        let file = write_set(&case_set(2));

        let too_few = CaseSource::load(Some(file.path()), "cat", 1).unwrap_err();
        let too_many = CaseSource::load(Some(file.path()), "cat", 3).unwrap_err();

        assert!(too_few.contains("cardinality mismatch"));
        assert!(too_many.contains("cardinality mismatch"));
    }

    // Duplicate IDs cannot produce ambiguous regression or metrics records.
    #[test]
    fn duplicate_explicit_case_ids_are_rejected() {
        let mut set = case_set(2);
        set.cases[1].id = set.cases[0].id.clone();
        let file = write_set(&set);

        let error = CaseSource::load(Some(file.path()), "cat", 2).unwrap_err();

        assert!(error.contains("duplicate case-set case id"));
    }

    // Fuzz receives the stored value rather than regenerating it by seed.
    #[test]
    fn fuzz_selects_the_explicit_case() {
        let set = case_set(1);
        let file = write_set(&set);
        let source = CaseSource::load(Some(file.path()), "cat", 1).unwrap();
        let mut fuzz_rng = rand::rngs::StdRng::seed_from_u64(1);

        let fuzz = source.select_fuzz_case(
            "cat",
            &[],
            &mut fuzz_rng,
            0,
            CaseGenerationLimits {
                max_args: 8,
                max_fs_entries: 12,
            },
            &InterestingCorpus::default(),
        );

        assert_eq!(fuzz.case, set.cases[0].case);
    }
}
