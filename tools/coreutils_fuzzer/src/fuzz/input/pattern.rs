use super::support;
use crate::fuzz::mutation::generate_missing_operands;
use crate::fuzz::{FixtureBlueprint, UtilityProfile};
use rand::rngs::StdRng;
use rand::Rng;

pub(crate) type ValueGenerator = fn(&ValueContext<'_>, &mut StdRng) -> String;

#[derive(Debug)]
pub(crate) struct ArgvPattern {
    alternatives: &'static [Alternative],
}

impl ArgvPattern {
    pub(crate) const fn new(alternatives: &'static [Alternative]) -> Self {
        Self { alternatives }
    }
}

#[derive(Debug)]
pub(crate) struct Alternative {
    weight: u32,
    required_options: &'static [&'static str],
    elements: &'static [Element],
}

impl Alternative {
    pub(crate) const fn new(elements: &'static [Element]) -> Self {
        Self {
            weight: 1,
            required_options: &[],
            elements,
        }
    }

    pub(crate) const fn weighted(weight: u32, elements: &'static [Element]) -> Self {
        Self {
            weight,
            required_options: &[],
            elements,
        }
    }

    pub(crate) const fn requiring(
        weight: u32,
        required_options: &'static [&'static str],
        elements: &'static [Element],
    ) -> Self {
        Self {
            weight,
            required_options,
            elements,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct Element {
    occurrence: Occurrence,
    atom: Atom,
    capture: Option<usize>,
    reuse_percent: u8,
}

impl Element {
    pub(crate) const fn once(atom: Atom) -> Self {
        Self {
            occurrence: Occurrence::Once,
            atom,
            capture: None,
            reuse_percent: 0,
        }
    }

    pub(crate) const fn optional(percent: u8, atom: Atom) -> Self {
        Self {
            occurrence: Occurrence::Optional { percent },
            atom,
            capture: None,
            reuse_percent: 0,
        }
    }

    pub(crate) const fn repeated(min: usize, max: usize, atom: Atom) -> Self {
        Self {
            occurrence: Occurrence::Range { min, max },
            atom,
            capture: None,
            reuse_percent: 0,
        }
    }

    pub(crate) const fn up_to_budget(min: usize, atom: Atom) -> Self {
        Self {
            occurrence: Occurrence::UpToBudget { min },
            atom,
            capture: None,
            reuse_percent: 0,
        }
    }

    pub(crate) const fn captured(mut self, slot: usize) -> Self {
        self.capture = Some(slot);
        self
    }

    pub(crate) const fn reusing(mut self, percent: u8) -> Self {
        self.reuse_percent = percent;
        self
    }
}

#[derive(Debug, Clone, Copy)]
enum Occurrence {
    Once,
    Optional { percent: u8 },
    Range { min: usize, max: usize },
    UpToBudget { min: usize },
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum Atom {
    Literal(&'static str),
    Option(OptionChoice),
    OptionValue(OptionValue),
    Value(ValueSource),
    Operand(OperandSource),
    OptionOrOperand {
        option_percent: u8,
        operand: OperandSource,
    },
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct OptionChoice {
    candidates: &'static [&'static str],
    fallback: Option<&'static str>,
}

impl OptionChoice {
    pub(crate) const fn available(candidates: &'static [&'static str]) -> Self {
        Self {
            candidates,
            fallback: None,
        }
    }

    pub(crate) const fn with_fallback(
        candidates: &'static [&'static str],
        fallback: &'static str,
    ) -> Self {
        Self {
            candidates,
            fallback: Some(fallback),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct OptionValue {
    forms: &'static [OptionValueForm],
    values: ValueSource,
}

impl OptionValue {
    pub(crate) const fn new(forms: &'static [OptionValueForm], values: ValueSource) -> Self {
        Self { forms, values }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct OptionValueForm {
    option: &'static str,
    spelling: ValueSpelling,
}

impl OptionValueForm {
    pub(crate) const fn separate(option: &'static str) -> Self {
        Self {
            option,
            spelling: ValueSpelling::Separate,
        }
    }

    pub(crate) const fn attached(option: &'static str) -> Self {
        Self {
            option,
            spelling: ValueSpelling::Attached,
        }
    }

    pub(crate) const fn equals(option: &'static str) -> Self {
        Self {
            option,
            spelling: ValueSpelling::Equals,
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum ValueSpelling {
    Separate,
    Attached,
    Equals,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ValueSource {
    Values(&'static [&'static str]),
    Generated(ValueGenerator),
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum OperandSource {
    ExistingFile,
    ExistingFileUnique,
    Existing,
    Missing,
    FileOrMissing {
        existing_percent: u8,
    },
    Target {
        existing_percent: u8,
    },
    Stream {
        existing_weight: u8,
        missing_weight: u8,
        stdin_weight: u8,
        allow_repeated_stdin: bool,
    },
    Generated(ValueGenerator),
}

pub(crate) struct ValueContext<'a> {
    option_pool: &'a [String],
    fixture: &'a FixtureBlueprint,
    argv: &'a [String],
    captures: &'a [Option<String>],
}

const GENERIC_ARGUMENTS_WITH_EXISTING: Element = Element::up_to_budget(
    0,
    Atom::OptionOrOperand {
        option_percent: 65,
        operand: OperandSource::Target {
            existing_percent: 100,
        },
    },
);
const GENERIC_ARGUMENTS_WITH_MIXED_PATHS: Element = Element::up_to_budget(
    0,
    Atom::OptionOrOperand {
        option_percent: 65,
        operand: OperandSource::Target {
            existing_percent: 50,
        },
    },
);
const PATH_ARGUMENTS_WITH_EXISTING: Element = Element::up_to_budget(
    0,
    Atom::OptionOrOperand {
        option_percent: 45,
        operand: OperandSource::Target {
            existing_percent: 100,
        },
    },
);
const PATH_ARGUMENTS_WITH_MIXED_PATHS: Element = Element::up_to_budget(
    0,
    Atom::OptionOrOperand {
        option_percent: 45,
        operand: OperandSource::Target {
            existing_percent: 50,
        },
    },
);
const REQUIRED_EXISTING_PATH: Element = Element::once(Atom::Operand(OperandSource::Target {
    existing_percent: 100,
}));
const REQUIRED_MIXED_PATH: Element = Element::once(Atom::Operand(OperandSource::Target {
    existing_percent: 50,
}));

static GENERIC_OPTIONAL_EXISTING: ArgvPattern =
    ArgvPattern::new(&[Alternative::new(&[GENERIC_ARGUMENTS_WITH_EXISTING])]);
static GENERIC_OPTIONAL_MIXED: ArgvPattern =
    ArgvPattern::new(&[Alternative::new(&[GENERIC_ARGUMENTS_WITH_MIXED_PATHS])]);
static GENERIC_REQUIRED_EXISTING: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    PATH_ARGUMENTS_WITH_EXISTING,
    REQUIRED_EXISTING_PATH,
])]);
static GENERIC_REQUIRED_MIXED: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
    PATH_ARGUMENTS_WITH_MIXED_PATHS,
    REQUIRED_MIXED_PATH,
])]);

pub(crate) fn generate_generic(
    profile: &UtilityProfile,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
) -> Vec<String> {
    let pattern = match (
        profile.requires_path_operand,
        profile.prefers_existing_paths,
    ) {
        (true, true) => &GENERIC_REQUIRED_EXISTING,
        (true, false) => &GENERIC_REQUIRED_MIXED,
        (false, true) => &GENERIC_OPTIONAL_EXISTING,
        (false, false) => &GENERIC_OPTIONAL_MIXED,
    };
    generate(pattern, option_pool, rng, max_args, fixture)
}

impl<'a> ValueContext<'a> {
    pub(crate) fn option_pool(&self) -> &'a [String] {
        self.option_pool
    }

    pub(crate) fn fixture(&self) -> &'a FixtureBlueprint {
        self.fixture
    }

    pub(crate) fn argv(&self) -> &'a [String] {
        self.argv
    }

    pub(crate) fn capture(&self, slot: usize) -> Option<&str> {
        self.captures.get(slot)?.as_deref()
    }
}

struct RenderedAtom {
    tokens: Vec<String>,
    value: String,
}

pub(crate) fn generate(
    pattern: &ArgvPattern,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
) -> Vec<String> {
    let eligible: Vec<&Alternative> = pattern
        .alternatives
        .iter()
        .filter(|alternative| {
            alternative.weight > 0
                && alternative
                    .required_options
                    .iter()
                    .all(|option| support::has_option(option_pool, option))
                && alternative.elements.iter().all(|element| {
                    !occurrence_is_required(element.occurrence)
                        || atom_is_supported(element.atom, option_pool)
                })
        })
        .collect();
    assert!(
        !eligible.is_empty(),
        "argv pattern has no alternative supported by the option pool"
    );

    let total_weight: u32 = eligible.iter().map(|alternative| alternative.weight).sum();
    let mut selected = rng.random_range(0..total_weight);
    let alternative = eligible
        .into_iter()
        .find(|alternative| {
            if selected < alternative.weight {
                true
            } else {
                selected -= alternative.weight;
                false
            }
        })
        .expect("positive pattern weight must select an alternative");

    render(alternative, option_pool, rng, max_args, fixture)
}

fn occurrence_is_required(occurrence: Occurrence) -> bool {
    match occurrence {
        Occurrence::Once => true,
        Occurrence::Optional { .. } => false,
        Occurrence::Range { min, .. } => min > 0,
        Occurrence::UpToBudget { min } => min > 0,
    }
}

fn atom_is_supported(atom: Atom, option_pool: &[String]) -> bool {
    match atom {
        Atom::Option(choice) => {
            choice.fallback.is_some()
                || choice
                    .candidates
                    .iter()
                    .any(|option| support::has_option(option_pool, option))
        }
        Atom::OptionValue(option_value) => option_value
            .forms
            .iter()
            .any(|form| support::has_option(option_pool, form.option)),
        _ => true,
    }
}

fn render(
    alternative: &Alternative,
    option_pool: &[String],
    rng: &mut StdRng,
    max_args: usize,
    fixture: &FixtureBlueprint,
) -> Vec<String> {
    let minimum = minimum_tokens(alternative.elements, option_pool);
    let budget = max_args.max(minimum);
    let mut argv = Vec::with_capacity(budget);
    let mut captures = Vec::<Option<String>>::new();

    for (index, element) in alternative.elements.iter().enumerate() {
        let reserved = minimum_tokens(&alternative.elements[index + 1..], option_pool);
        let allowance = budget.saturating_sub(argv.len() + reserved);
        let min_tokens = atom_minimum_tokens(element.atom, option_pool);
        let max_count = allowance.checked_div(min_tokens).unwrap_or(0);
        let requested = if atom_is_supported(element.atom, option_pool) {
            occurrence_count(element.occurrence, max_count, rng)
        } else {
            0
        };
        let count = requested.min(max_count);
        let mut previous_values: Vec<String> = Vec::new();

        for _ in 0..count {
            let remaining = budget.saturating_sub(argv.len() + reserved);
            let rendered = if !previous_values.is_empty()
                && element.reuse_percent > 0
                && rng.random_bool(f64::from(element.reuse_percent) / 100.0)
            {
                let value = previous_values[rng.random_range(0..previous_values.len())].clone();
                RenderedAtom {
                    tokens: vec![value.clone()],
                    value,
                }
            } else {
                let context = ValueContext {
                    option_pool,
                    fixture,
                    argv: &argv,
                    captures: &captures,
                };
                render_atom(element.atom, &context, rng, remaining)
                    .expect("eligible argv pattern atom must be renderable")
            };
            if rendered.tokens.len() > remaining {
                break;
            }
            previous_values.push(rendered.value.clone());
            if let Some(slot) = element.capture {
                if captures.len() <= slot {
                    captures.resize(slot + 1, None);
                }
                captures[slot] = Some(rendered.value);
            }
            argv.extend(rendered.tokens);
        }
    }

    debug_assert!(argv.len() <= budget);
    argv
}

fn occurrence_count(occurrence: Occurrence, max_count: usize, rng: &mut StdRng) -> usize {
    match occurrence {
        Occurrence::Once => 1,
        Occurrence::Optional { percent } => usize::from(
            percent >= 100 || (percent > 0 && rng.random_bool(f64::from(percent) / 100.0)),
        ),
        Occurrence::Range { min, max } => {
            assert!(min <= max, "pattern occurrence minimum exceeds maximum");
            let max = max.min(max_count).max(min);
            if min == max {
                min
            } else {
                rng.random_range(min..=max)
            }
        }
        Occurrence::UpToBudget { min } => {
            let max = max_count.max(min);
            if min == max {
                min
            } else {
                rng.random_range(min..=max)
            }
        }
    }
}

fn minimum_tokens(elements: &[Element], option_pool: &[String]) -> usize {
    elements
        .iter()
        .map(|element| {
            let count = match element.occurrence {
                Occurrence::Once => 1,
                Occurrence::Optional { .. } => 0,
                Occurrence::Range { min, .. } => min,
                Occurrence::UpToBudget { min } => min,
            };
            count * atom_minimum_tokens(element.atom, option_pool)
        })
        .sum()
}

fn atom_minimum_tokens(atom: Atom, option_pool: &[String]) -> usize {
    match atom {
        Atom::OptionValue(option_value) => option_value
            .forms
            .iter()
            .filter(|form| support::has_option(option_pool, form.option))
            .map(|form| match form.spelling {
                ValueSpelling::Separate => 2,
                ValueSpelling::Attached | ValueSpelling::Equals => 1,
            })
            .min()
            .unwrap_or(1),
        _ => 1,
    }
}

fn render_atom(
    atom: Atom,
    context: &ValueContext<'_>,
    rng: &mut StdRng,
    allowance: usize,
) -> Option<RenderedAtom> {
    match atom {
        Atom::Literal(value) => Some(single(value.to_string())),
        Atom::Option(choice) => render_option(choice, context.option_pool, rng).map(single),
        Atom::OptionValue(option_value) => {
            render_option_value(option_value, context, rng, allowance)
        }
        Atom::Value(source) => Some(single(generate_value(source, context, rng))),
        Atom::Operand(source) => Some(single(generate_operand(source, context, rng))),
        Atom::OptionOrOperand {
            option_percent,
            operand,
        } => {
            let choose_option = !context.option_pool.is_empty()
                && (option_percent >= 100
                    || (option_percent > 0 && rng.random_bool(f64::from(option_percent) / 100.0)));
            if choose_option {
                let option = &context.option_pool[rng.random_range(0..context.option_pool.len())];
                Some(single(option.clone()))
            } else {
                Some(single(generate_operand(operand, context, rng)))
            }
        }
    }
}

fn render_option(choice: OptionChoice, option_pool: &[String], rng: &mut StdRng) -> Option<String> {
    let available: Vec<&str> = choice
        .candidates
        .iter()
        .copied()
        .filter(|option| support::has_option(option_pool, option))
        .collect();
    if available.is_empty() {
        choice.fallback.map(str::to_string)
    } else {
        Some(available[rng.random_range(0..available.len())].to_string())
    }
}

fn render_option_value(
    option_value: OptionValue,
    context: &ValueContext<'_>,
    rng: &mut StdRng,
    allowance: usize,
) -> Option<RenderedAtom> {
    let available: Vec<OptionValueForm> = option_value
        .forms
        .iter()
        .copied()
        .filter(|form| support::has_option(context.option_pool, form.option))
        .filter(|form| {
            allowance
                >= match form.spelling {
                    ValueSpelling::Separate => 2,
                    ValueSpelling::Attached | ValueSpelling::Equals => 1,
                }
        })
        .collect();
    let form = available
        .get(rng.random_range(0..available.len()))
        .copied()?;
    let value = generate_value(option_value.values, context, rng);
    let tokens = match form.spelling {
        ValueSpelling::Separate => vec![form.option.to_string(), value.clone()],
        ValueSpelling::Attached => vec![format!("{}{value}", form.option)],
        ValueSpelling::Equals => vec![format!("{}={value}", form.option)],
    };
    Some(RenderedAtom { tokens, value })
}

fn generate_value(source: ValueSource, context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    match source {
        ValueSource::Values(values) => values[rng.random_range(0..values.len())].to_string(),
        ValueSource::Generated(generate) => generate(context, rng),
    }
}

fn generate_operand(source: OperandSource, context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    match source {
        OperandSource::ExistingFile => {
            pick_or(support::existing_file_operands(context.fixture), ".", rng)
        }
        OperandSource::ExistingFileUnique => {
            let unused: Vec<String> = support::existing_file_operands(context.fixture)
                .into_iter()
                .filter(|candidate| !context.argv.contains(candidate))
                .collect();
            pick_or(unused, ".", rng)
        }
        OperandSource::Existing => pick_or(context.fixture.existing_operands(), ".", rng),
        OperandSource::Missing => pick_or(generate_missing_operands(rng), "missing", rng),
        OperandSource::FileOrMissing { existing_percent } => {
            let files = support::existing_file_operands(context.fixture);
            if !files.is_empty()
                && (existing_percent >= 100
                    || (existing_percent > 0
                        && rng.random_bool(f64::from(existing_percent) / 100.0)))
            {
                support::pick_string(&files, rng)
            } else {
                pick_or(generate_missing_operands(rng), "missing", rng)
            }
        }
        OperandSource::Target { existing_percent } => {
            let targets = context.fixture.existing_operands();
            if !targets.is_empty()
                && (existing_percent >= 100
                    || (existing_percent > 0
                        && rng.random_bool(f64::from(existing_percent) / 100.0)))
            {
                support::pick_string(&targets, rng)
            } else {
                pick_or(generate_missing_operands(rng), "missing", rng)
            }
        }
        OperandSource::Stream {
            existing_weight,
            missing_weight,
            stdin_weight,
            allow_repeated_stdin,
        } => {
            let files = support::existing_file_operands(context.fixture);
            let missing = generate_missing_operands(rng);
            let stdin_available =
                allow_repeated_stdin || !context.argv.iter().any(|arg| arg == "-");
            let effective_stdin_weight = if stdin_available { stdin_weight } else { 0 };
            let effective_existing_weight = if files.is_empty() { 0 } else { existing_weight };
            let effective_missing_weight = if missing.is_empty() {
                0
            } else {
                missing_weight
            };
            let total = u16::from(effective_existing_weight)
                + u16::from(effective_missing_weight)
                + u16::from(effective_stdin_weight);
            if total == 0 {
                return "-".to_string();
            }
            let selected = rng.random_range(0..total);
            if selected < u16::from(effective_stdin_weight) {
                "-".to_string()
            } else if selected
                < u16::from(effective_stdin_weight) + u16::from(effective_missing_weight)
            {
                support::pick_string(&missing, rng)
            } else {
                support::pick_string(&files, rng)
            }
        }
        OperandSource::Generated(generate) => generate(context, rng),
    }
}

fn pick_or(values: Vec<String>, fallback: &str, rng: &mut StdRng) -> String {
    if values.is_empty() {
        fallback.to_string()
    } else {
        support::pick_string(&values, rng)
    }
}

fn single(value: String) -> RenderedAtom {
    RenderedAtom {
        tokens: vec![value.clone()],
        value,
    }
}

#[cfg(test)]
mod tests {
    use super::{
        generate, Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice,
        OptionValue, OptionValueForm, ValueSource,
    };
    use crate::fuzz::{FileSpec, FixtureBlueprint};
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use std::path::PathBuf;

    fn fixture() -> FixtureBlueprint {
        FixtureBlueprint {
            directories: Vec::new(),
            files: vec![FileSpec {
                relative_path: PathBuf::from("input.txt"),
                bytes: Vec::new(),
                mode: 0o644,
            }],
            symlinks: Vec::new(),
            hardlinks: Vec::new(),
        }
    }

    // A required operand remains present even when an optional option-value group uses the budget.
    #[test]
    fn interpreter_reserves_required_tail_budget() {
        static PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
            Element::optional(
                100,
                Atom::OptionValue(OptionValue::new(
                    &[OptionValueForm::separate("-n")],
                    ValueSource::Values(&["2"]),
                )),
            ),
            Element::once(Atom::Operand(OperandSource::ExistingFile)),
        ])]);
        let mut rng = StdRng::seed_from_u64(1);

        let argv = generate(&PATTERN, &["-n".to_string()], &mut rng, 3, &fixture());

        assert_eq!(argv, vec!["-n", "2", "input.txt"]);
    }

    // Alternatives requiring unavailable schema options are removed before weighted selection.
    #[test]
    fn interpreter_filters_unavailable_alternatives() {
        static PATTERN: ArgvPattern = ArgvPattern::new(&[
            Alternative::requiring(
                100,
                &["--special"],
                &[Element::once(Atom::Literal("special"))],
            ),
            Alternative::new(&[Element::once(Atom::Literal("fallback"))]),
        ]);
        let mut rng = StdRng::seed_from_u64(2);

        let argv = generate(&PATTERN, &[], &mut rng, 1, &fixture());

        assert_eq!(argv, vec!["fallback"]);
    }

    // Option-value forms are selected structurally and never emit an option without its value.
    #[test]
    fn interpreter_emits_only_available_option_value_forms() {
        static PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[Element::once(
            Atom::OptionValue(OptionValue::new(
                &[
                    OptionValueForm::separate("-n"),
                    OptionValueForm::equals("--lines"),
                ],
                ValueSource::Values(&["2"]),
            )),
        )])]);
        let mut rng = StdRng::seed_from_u64(3);

        let argv = generate(&PATTERN, &["--lines".to_string()], &mut rng, 1, &fixture());

        assert_eq!(argv, vec!["--lines=2"]);
    }

    // The same seed, fixture and pattern produce the same argv sequence.
    #[test]
    fn interpreter_is_seed_deterministic() {
        static PATTERN: ArgvPattern = ArgvPattern::new(&[Alternative::new(&[
            Element::repeated(0, 3, Atom::Option(OptionChoice::available(&["-a", "-b"]))),
            Element::repeated(
                0,
                2,
                Atom::Operand(OperandSource::Stream {
                    existing_weight: 3,
                    missing_weight: 1,
                    stdin_weight: 1,
                    allow_repeated_stdin: true,
                }),
            ),
        ])]);
        let options = vec!["-a".to_string(), "-b".to_string()];
        let mut left = StdRng::seed_from_u64(4);
        let mut right = StdRng::seed_from_u64(4);

        assert_eq!(
            generate(&PATTERN, &options, &mut left, 5, &fixture()),
            generate(&PATTERN, &options, &mut right, 5, &fixture())
        );
    }

    // Generic path profiles reserve one operand even when options fill the variable prefix.
    #[test]
    fn generic_pattern_keeps_a_required_path_operand() {
        let mut rng = StdRng::seed_from_u64(5);
        let profile = crate::fuzz::UtilityProfile {
            requires_path_operand: true,
            prefers_existing_paths: true,
        };

        let argv =
            super::generate_generic(&profile, &["--flag".to_string()], &mut rng, 3, &fixture());

        assert!((1..=3).contains(&argv.len()));
        assert!(matches!(
            argv.last().map(String::as_str),
            Some("." | "input.txt")
        ));
    }
}
