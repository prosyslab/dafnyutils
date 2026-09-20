use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueContext, ValueSource,
};
use super::super::{mutation, support, PatternInputGenerator};
use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, GeneratedCase, HardlinkSpec, SymlinkSpec};
use rand::rngs::StdRng;
use std::path::PathBuf;

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutation::regenerate_argv);

const BLOCK_SIZES: &[&str] = &["0", "1", "512", "1024", "4096"];
// Long ctime output stays limited to a direct host-validated record because clone ctimes differ.
// Short ctime sorting is validated independently against each clone's host-controlled order.
const ACCESS_TIME_FIELDS: &[&str] = &["atime", "access", "use"];
const MODIFICATION_TIME_FIELDS: &[&str] = &["mtime", "modification"];
const CHANGE_TIME_FIELDS: &[&str] = &["ctime", "status"];
const INVALID_TIME_FIELDS: &[&str] = &["XX"];
const TIME_STYLES: &[&str] = &[
    "XX",
    "+%s",
    "full-iso",
    "long-iso",
    "iso",
    "locale",
    "posix-full-iso",
    "posix-long-iso",
    "posix-iso",
    "posix-locale",
];

const HIDDEN: Element = Element::optional(
    30,
    Atom::Option(OptionChoice::available(&[
        "-a",
        "--all",
        "-A",
        "--almost-all",
    ])),
);
const DIRECTORY: Element = Element::optional(
    18,
    Atom::Option(OptionChoice::available(&["-d", "--directory"])),
);
const REVERSE: Element = Element::optional(
    25,
    Atom::Option(OptionChoice::available(&["-r", "--reverse"])),
);
const FOLLOW: Element = Element::optional(
    24,
    Atom::Option(OptionChoice::available(&[
        "-H",
        "--dereference-command-line",
        "-L",
        "--dereference",
    ])),
);
const RECURSIVE: Element = Element::optional(
    22,
    Atom::Option(OptionChoice::available(&["-R", "--recursive"])),
);
const OPERANDS: Element = Element::repeated(
    0,
    3,
    Atom::Operand(OperandSource::Target {
        existing_percent: 78,
    }),
);
const TIME_FIELD: Element =
    Element::optional(35, Atom::Value(ValueSource::Generated(ls_time_field)));
const TIME_STYLE: Element = Element::optional(
    45,
    Atom::OptionValue(OptionValue::new(
        &[OptionValueForm::equals("--time-style")],
        ValueSource::Values(TIME_STYLES),
    )),
);
const BLOCK_SIZE: Element = Element::optional(
    45,
    Atom::OptionValue(OptionValue::new(
        &[OptionValueForm::equals("--block-size")],
        ValueSource::Values(BLOCK_SIZES),
    )),
);

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::requiring(2, &["--help"], &[Element::once(Atom::Literal("--help"))]),
    Alternative::requiring(
        2,
        &["--version"],
        &[Element::once(Atom::Literal("--version"))],
    ),
    Alternative::requiring(
        1,
        &["-t", "-c"],
        &[
            Element::once(Atom::Literal("-t")),
            Element::once(Atom::Literal("-c")),
            REVERSE,
        ],
    ),
    Alternative::requiring(
        1,
        &["-t", "--time"],
        &[
            Element::once(Atom::Literal("-t")),
            Element::once(Atom::OptionValue(OptionValue::new(
                &[OptionValueForm::equals("--time")],
                ValueSource::Values(CHANGE_TIME_FIELDS),
            ))),
            REVERSE,
        ],
    ),
    Alternative::weighted(
        8,
        &[
            HIDDEN,
            DIRECTORY,
            Element::once(Atom::Option(OptionChoice::available(&[
                "-n",
                "--numeric-uid-gid",
            ]))),
            TIME_FIELD,
            TIME_STYLE,
            BLOCK_SIZE,
            REVERSE,
            FOLLOW,
            RECURSIVE,
            OPERANDS,
        ],
    ),
    Alternative::requiring(
        6,
        &["-t"],
        &[
            HIDDEN,
            DIRECTORY,
            Element::once(Atom::Literal("-t")),
            TIME_FIELD,
            REVERSE,
            FOLLOW,
            RECURSIVE,
            OPERANDS,
        ],
    ),
    Alternative::requiring(
        6,
        &["-t"],
        &[
            HIDDEN,
            DIRECTORY,
            Element::once(Atom::Option(OptionChoice::available(&[
                "-n",
                "--numeric-uid-gid",
            ]))),
            Element::once(Atom::Literal("-t")),
            TIME_FIELD,
            TIME_STYLE,
            BLOCK_SIZE,
            REVERSE,
            FOLLOW,
            RECURSIVE,
            OPERANDS,
        ],
    ),
    Alternative::weighted(
        6,
        &[
            HIDDEN,
            DIRECTORY,
            Element::once(Atom::Option(OptionChoice::available(&["-s", "--size"]))),
            BLOCK_SIZE,
            REVERSE,
            FOLLOW,
            RECURSIVE,
            OPERANDS,
        ],
    ),
    Alternative::requiring(
        4,
        &["-S"],
        &[
            HIDDEN,
            DIRECTORY,
            Element::once(Atom::Literal("-S")),
            REVERSE,
            FOLLOW,
            RECURSIVE,
            OPERANDS,
        ],
    ),
    Alternative::weighted(
        12,
        &[HIDDEN, DIRECTORY, REVERSE, FOLLOW, RECURSIVE, OPERANDS],
    ),
]);

fn ls_time_field(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let sort_time = context.argv().iter().any(|arg| arg == "-t");
    let allow_access_time = !sort_time || context.fixture().symlinks.is_empty();
    let mut candidates = Vec::new();
    if allow_access_time && support::has_option(context.option_pool(), "-u") {
        candidates.push("-u".to_string());
    }
    if support::has_option(context.option_pool(), "--time") {
        candidates.extend(
            MODIFICATION_TIME_FIELDS
                .iter()
                .chain(INVALID_TIME_FIELDS)
                .map(|value| format!("--time={value}")),
        );
        if allow_access_time {
            candidates.extend(
                ACCESS_TIME_FIELDS
                    .iter()
                    .map(|value| format!("--time={value}")),
            );
        }
    }
    if candidates.is_empty() {
        "-u".to_string()
    } else {
        support::pick_string(&candidates, rng)
    }
}

pub(crate) fn ls_argv_respects_mode_dependencies(argv: &[String]) -> bool {
    let Some(modes) = parse_ls_arg_modes(argv) else {
        return false;
    };

    (!modes.selects_time || modes.numeric_long || modes.sort_time)
        && (!modes.sets_time_style || modes.numeric_long)
        && (!modes.sets_block_size || modes.show_blocks || modes.numeric_long)
        && (!modes.selects_change_time
            || ls_direct_ctime_case(argv).is_some()
            || ls_short_ctime_sort_case(argv).is_some())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LsShortCtimeSortCase {
    pub(crate) reverse: bool,
}

// Host ctimes may differ across clones, so only a no-operand short listing is independently checkable.
pub(crate) fn ls_short_ctime_sort_case(argv: &[String]) -> Option<LsShortCtimeSortCase> {
    let mut sort_time = false;
    let mut reverse = false;
    let mut selects_change_time = None;
    let mut options = true;
    let mut index = 0;

    while index < argv.len() {
        let arg = argv[index].as_str();
        if options && arg == "--" {
            options = false;
            index += 1;
            continue;
        }
        if !options || !arg.starts_with('-') || arg == "-" {
            return None;
        }

        match arg {
            "--reverse" => reverse = true,
            "--time" => {
                index += 1;
                selects_change_time = Some(ls_change_time_value(argv.get(index)?.as_str())?);
            }
            _ => {
                if let Some(value) = arg.strip_prefix("--time=") {
                    selects_change_time = Some(ls_change_time_value(value)?);
                } else if let Some(shorts) =
                    arg.strip_prefix('-').filter(|_| !arg.starts_with("--"))
                {
                    if shorts.is_empty()
                        || !shorts
                            .chars()
                            .all(|short| matches!(short, 't' | 'r' | 'u' | 'c'))
                    {
                        return None;
                    }
                    for short in shorts.chars() {
                        match short {
                            't' => sort_time = true,
                            'r' => reverse = true,
                            'u' => selects_change_time = Some(false),
                            'c' => selects_change_time = Some(true),
                            _ => unreachable!("validated short ctime sort option"),
                        }
                    }
                } else {
                    return None;
                }
            }
        }
        index += 1;
    }

    (sort_time && selects_change_time == Some(true)).then_some(LsShortCtimeSortCase { reverse })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LsDirectOperandFollow {
    NoFollow,
    Follow,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct LsDirectCtimeCase<'a> {
    pub(crate) operand: &'a str,
    pub(crate) follow: LsDirectOperandFollow,
}

// Cross-clone ctime normalization is deliberately limited to one direct epoch-seconds record.
pub(crate) fn ls_direct_ctime_case(argv: &[String]) -> Option<LsDirectCtimeCase<'_>> {
    let mut numeric_long = false;
    let mut list_directories = false;
    let mut selects_change_time = false;
    let mut epoch_seconds = false;
    let mut follow = LsDirectOperandFollow::NoFollow;
    let mut operands = Vec::new();
    let mut options = true;
    let mut index = 0;

    while index < argv.len() {
        let arg = argv[index].as_str();
        if options && arg == "--" {
            options = false;
            index += 1;
            continue;
        }
        if !options || !arg.starts_with('-') || arg == "-" {
            operands.push(arg);
            index += 1;
            continue;
        }

        match arg {
            "--numeric-uid-gid" => numeric_long = true,
            "--directory" => list_directories = true,
            "--dereference-command-line" | "--dereference" => {
                follow = LsDirectOperandFollow::Follow
            }
            "--time" => {
                index += 1;
                selects_change_time = ls_change_time_value(argv.get(index)?.as_str())?;
            }
            "--time-style" => {
                index += 1;
                epoch_seconds = ls_epoch_seconds_style(argv.get(index)?.as_str())?;
            }
            _ => {
                if let Some(value) = arg.strip_prefix("--time=") {
                    selects_change_time = ls_change_time_value(value)?;
                } else if let Some(value) = arg.strip_prefix("--time-style=") {
                    epoch_seconds = ls_epoch_seconds_style(value)?;
                } else if let Some(shorts) =
                    arg.strip_prefix('-').filter(|_| !arg.starts_with("--"))
                {
                    if shorts.is_empty()
                        || !shorts
                            .chars()
                            .all(|short| matches!(short, 'n' | 'd' | 'u' | 'c' | 'H' | 'L'))
                    {
                        return None;
                    }
                    for short in shorts.chars() {
                        match short {
                            'n' => numeric_long = true,
                            'd' => list_directories = true,
                            'u' => selects_change_time = false,
                            'c' => selects_change_time = true,
                            'H' | 'L' => follow = LsDirectOperandFollow::Follow,
                            _ => unreachable!("validated direct ctime option"),
                        }
                    }
                } else {
                    return None;
                }
            }
        }
        index += 1;
    }

    (numeric_long
        && list_directories
        && selects_change_time
        && epoch_seconds
        && operands.len() == 1)
        .then(|| LsDirectCtimeCase {
            operand: operands[0],
            follow,
        })
}

fn ls_change_time_value(value: &str) -> Option<bool> {
    match value {
        "ctime" | "status" => Some(true),
        "atime" | "access" | "use" | "mtime" | "modification" => Some(false),
        _ => None,
    }
}

fn ls_epoch_seconds_style(value: &str) -> Option<bool> {
    match value {
        "+%s" => Some(true),
        // Sub-second/full date layouts cannot be mapped safely to one metadata field yet.
        "full-iso" | "long-iso" | "iso" | "locale" | "posix-full-iso" | "posix-long-iso"
        | "posix-iso" | "posix-locale" => Some(false),
        _ => None,
    }
}

pub(crate) fn ls_argv_requires_followed_entry_metadata(argv: &[String]) -> bool {
    let Some(modes) = parse_ls_arg_modes(argv) else {
        return false;
    };

    !modes.early_exit
        && modes.follow_always
        && !modes.list_directories
        && (modes.numeric_long
            || modes.show_blocks
            || modes.sort_size
            || modes.sort_time
            || modes.recursive)
}

#[derive(Default)]
struct LsArgModes {
    numeric_long: bool,
    show_blocks: bool,
    sort_size: bool,
    sort_time: bool,
    selects_time: bool,
    selects_change_time: bool,
    sets_time_style: bool,
    sets_block_size: bool,
    follow_always: bool,
    list_directories: bool,
    recursive: bool,
    early_exit: bool,
}

fn parse_ls_arg_modes(argv: &[String]) -> Option<LsArgModes> {
    let mut modes = LsArgModes::default();
    let mut index = 0;
    let mut options = true;

    while index < argv.len() {
        let arg = argv[index].as_str();
        if options && arg == "--" {
            options = false;
            index += 1;
            continue;
        }
        if !options || !arg.starts_with('-') || arg == "-" {
            index += 1;
            continue;
        }

        match arg {
            "--numeric-uid-gid" => modes.numeric_long = true,
            "--size" => modes.show_blocks = true,
            "--directory" => modes.list_directories = true,
            "--recursive" => modes.recursive = true,
            "--dereference" => modes.follow_always = true,
            "--dereference-command-line" => modes.follow_always = false,
            "--help" | "--version" => modes.early_exit = true,
            "--time" => {
                let value = argv.get(index + 1)?;
                modes.selects_time = true;
                modes.selects_change_time = matches!(value.as_str(), "ctime" | "status");
                index += 1;
            }
            "--time-style" => {
                argv.get(index + 1)?;
                modes.sets_time_style = true;
                index += 1;
            }
            "--block-size" => {
                argv.get(index + 1)?;
                modes.sets_block_size = true;
                index += 1;
            }
            _ => {
                if arg.starts_with("--time=") {
                    modes.selects_time = true;
                    modes.selects_change_time =
                        matches!(arg.strip_prefix("--time=")?, "ctime" | "status");
                } else if arg.starts_with("--time-style=") {
                    modes.sets_time_style = true;
                } else if arg.starts_with("--block-size=") {
                    modes.sets_block_size = true;
                } else if let Some(shorts) =
                    arg.strip_prefix('-').filter(|_| !arg.starts_with("--"))
                {
                    modes.numeric_long |= shorts.contains('n');
                    modes.show_blocks |= shorts.contains('s');
                    modes.sort_size |= shorts.contains('S');
                    modes.sort_time |= shorts.contains('t');
                    modes.selects_time |= shorts.contains('u') || shorts.contains('c');
                    for short in shorts.chars() {
                        if short == 'u' {
                            modes.selects_change_time = false;
                        } else if short == 'c' {
                            modes.selects_change_time = true;
                        }
                    }
                    modes.list_directories |= shorts.contains('d');
                    modes.recursive |= shorts.contains('R');
                    for short in shorts.chars() {
                        if short == 'L' {
                            modes.follow_always = true;
                        } else if short == 'H' {
                            modes.follow_always = false;
                        }
                    }
                }
            }
        }
        index += 1;
    }

    Some(modes)
}

#[cfg(test)]
mod tests {
    use super::{
        ls_argv_requires_followed_entry_metadata, ls_argv_respects_mode_dependencies,
        ls_direct_ctime_case, ls_short_ctime_sort_case, LsDirectOperandFollow, ARGV_PATTERN,
    };
    use crate::fuzz::input::pattern;
    use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, SymlinkSpec};
    use rand::rngs::StdRng;
    use rand::SeedableRng;
    use std::collections::BTreeSet;
    use std::path::PathBuf;

    fn fixture() -> FixtureBlueprint {
        FixtureBlueprint {
            directories: vec![DirSpec {
                relative_path: PathBuf::from("dir"),
                mode: 0o755,
            }],
            files: vec![FileSpec {
                relative_path: PathBuf::from("file"),
                bytes: b"payload".to_vec(),
                mode: 0o644,
            }],
            symlinks: vec![SymlinkSpec {
                relative_path: PathBuf::from("link"),
                target: PathBuf::from("file"),
            }],
            hardlinks: Vec::new(),
        }
    }

    fn option_pool() -> Vec<String> {
        [
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
        ]
        .into_iter()
        .map(str::to_string)
        .collect()
    }

    fn render_pattern(
        option_pool: &[String],
        rng: &mut StdRng,
        max_args: usize,
        fixture: &FixtureBlueprint,
    ) -> Vec<String> {
        pattern::generate(&ARGV_PATTERN, option_pool, rng, max_args, fixture)
    }

    // The generator reaches every modeled option domain without emitting incomplete value options.
    #[test]
    fn generated_arguments_cover_modeled_domains() {
        let fixture = fixture();
        let pool = option_pool();
        let mut domains = BTreeSet::new();

        for seed in 0..8192 {
            let mut rng = StdRng::seed_from_u64(seed);
            let argv = render_pattern(&pool, &mut rng, 12, &fixture);
            assert!(argv.len() <= 12);
            assert!(!argv
                .iter()
                .any(|arg| { matches!(arg.as_str(), "--block-size" | "--time" | "--time-style") }));
            for arg in argv {
                let domain = if matches!(arg.as_str(), "-a" | "--all" | "-A" | "--almost-all") {
                    Some("hidden")
                } else if matches!(arg.as_str(), "-d" | "--directory") {
                    Some("directory")
                } else if matches!(arg.as_str(), "-n" | "--numeric-uid-gid") {
                    Some("long")
                } else if matches!(arg.as_str(), "-s" | "--size") {
                    Some("blocks")
                } else if arg.starts_with("--block-size=") {
                    Some("block-size")
                } else if matches!(arg.as_str(), "-S" | "-t") {
                    Some("sort")
                } else if matches!(arg.as_str(), "-r" | "--reverse") {
                    Some("reverse")
                } else if matches!(arg.as_str(), "-u" | "-c") || arg.starts_with("--time=") {
                    Some("time-field")
                } else if arg.starts_with("--time-style=") {
                    Some("time-style")
                } else if matches!(
                    arg.as_str(),
                    "-H" | "--dereference-command-line" | "-L" | "--dereference"
                ) {
                    Some("follow")
                } else if matches!(arg.as_str(), "-R" | "--recursive") {
                    Some("recursive")
                } else if matches!(arg.as_str(), "--help" | "--version") {
                    Some("early-exit")
                } else {
                    Some("operand")
                };
                domains.insert(domain.expect("every argument has a domain"));
            }
        }

        assert_eq!(
            domains,
            BTreeSet::from([
                "hidden",
                "directory",
                "long",
                "blocks",
                "block-size",
                "sort",
                "reverse",
                "time-field",
                "time-style",
                "follow",
                "recursive",
                "early-exit",
                "operand",
            ])
        );
    }

    // Time selectors stay paired with an output or sorting mode where GNU and the benchmark agree.
    #[test]
    fn generated_time_selectors_stay_in_supported_context() {
        let fixture = fixture();
        let pool = option_pool();

        for seed in 0..8192 {
            let mut rng = StdRng::seed_from_u64(seed);
            let argv = render_pattern(&pool, &mut rng, 12, &fixture);
            assert!(ls_argv_respects_mode_dependencies(&argv));
            let has_time_selector = argv
                .iter()
                .any(|arg| matches!(arg.as_str(), "-u" | "-c") || arg.starts_with("--time="));
            let selects_change_time = argv
                .iter()
                .any(|arg| matches!(arg.as_str(), "-c" | "--time=ctime" | "--time=status"));
            if selects_change_time {
                assert!(ls_short_ctime_sort_case(&argv).is_some(), "{argv:?}");
            }
            if has_time_selector {
                assert!(argv
                    .iter()
                    .any(|arg| { matches!(arg.as_str(), "-n" | "--numeric-uid-gid" | "-t") }));
            }
            if argv.iter().any(|arg| arg.starts_with("--time-style=")) {
                assert!(argv
                    .iter()
                    .any(|arg| matches!(arg.as_str(), "-n" | "--numeric-uid-gid")));
            }
            if argv.iter().any(|arg| arg.starts_with("--block-size=")) {
                assert!(argv.iter().any(|arg| matches!(
                    arg.as_str(),
                    "-n" | "--numeric-uid-gid" | "-s" | "--size"
                )));
            }
        }
    }

    // 변경 시각 생성기는 값이 출력되지 않는 짧은 -ct 정렬 조합에 도달한다.
    #[test]
    fn generated_time_fields_reach_short_ctime_sorting() {
        let fixture = fixture();
        let pool = option_pool();

        let reached = (0..8192).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let argv = render_pattern(&pool, &mut rng, 12, &fixture);
            ls_short_ctime_sort_case(&argv).is_some()
        });

        assert!(reached);
    }

    // A safe short ctime sort honors the last time selector and the reverse flag.
    #[test]
    fn short_ctime_sort_case_parses_last_selector_and_reverse() {
        let argv = ["-tu", "--time=status", "--reverse"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();

        let parsed = ls_short_ctime_sort_case(&argv).expect("safe short ctime sort");

        assert!(parsed.reverse);
        assert!(ls_argv_respects_mode_dependencies(&argv));
    }

    // A later access-time selector keeps the listing outside ctime normalization.
    #[test]
    fn short_ctime_sort_case_rejects_later_access_selector() {
        let argv = ["-tc", "-u"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();

        assert!(ls_short_ctime_sort_case(&argv).is_none());
    }

    // A command-line operand makes ctime sorting too broad for independent directory validation.
    #[test]
    fn short_ctime_sort_case_rejects_operand() {
        let argv = ["-tc", "file"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();

        assert!(ls_short_ctime_sort_case(&argv).is_none());
        assert!(!ls_argv_respects_mode_dependencies(&argv));
    }

    // 블록 크기 생성기는 명세의 잘못된 양의 정수 오류 모드에 실제로 도달한다.
    #[test]
    fn generated_block_sizes_reach_zero_error_mode() {
        let fixture = fixture();
        let pool = option_pool();

        let reached = (0..8192).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            render_pattern(&pool, &mut rng, 12, &fixture)
                .iter()
                .any(|arg| arg == "--block-size=0")
        });

        assert!(reached);
    }

    // 시각 선택자 생성기는 명세의 잘못된 --time 값 오류 모드에 실제로 도달한다.
    #[test]
    fn generated_time_fields_reach_invalid_value_error_mode() {
        let fixture = fixture();
        let pool = option_pool();

        let reached = (0..8192).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            render_pattern(&pool, &mut rng, 12, &fixture)
                .iter()
                .any(|arg| arg == "--time=XX")
        });

        assert!(reached);
    }

    // 시각 형식 생성기는 숫자 긴 출력에서 명세의 잘못된 형식 오류 모드에 도달한다.
    #[test]
    fn generated_time_styles_reach_invalid_value_error_mode() {
        let fixture = fixture();
        let pool = option_pool();

        let reached = (0..8192).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            render_pattern(&pool, &mut rng, 12, &fixture)
                .iter()
                .any(|arg| arg == "--time-style=XX")
        });

        assert!(reached);
    }

    // Direct epoch ctime comparison accepts one operand and records command-line dereference.
    #[test]
    fn direct_ctime_case_parses_supported_shape_and_follow_policy() {
        let argv = ["-ndc", "-H", "--time-style=+%s", "link"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();

        let parsed = ls_direct_ctime_case(&argv).expect("supported direct ctime case");

        assert_eq!(parsed.operand, "link");
        assert_eq!(parsed.follow, LsDirectOperandFollow::Follow);
        assert!(ls_argv_respects_mode_dependencies(&argv));
    }

    // 직접 변경 시각 사례는 앞선 -u보다 뒤의 -c 선택자를 최종 값으로 사용한다.
    #[test]
    fn direct_ctime_case_honors_last_short_time_selector() {
        let argv = ["-nduc", "--time-style=+%s", "file"]
            .into_iter()
            .map(str::to_string)
            .collect::<Vec<_>>();

        assert!(ls_direct_ctime_case(&argv).is_some());
        assert!(ls_argv_respects_mode_dependencies(&argv));
    }

    // Change-time sorting, full date output, and multiple operands stay outside normalization.
    #[test]
    fn direct_ctime_case_rejects_unverifiable_shapes() {
        for argv in [
            vec!["-ndtc", "--time-style=+%s", "file"],
            vec!["-ndc", "--time-style=full-iso", "file"],
            vec!["-ndc", "--time-style=+%s", "left", "right"],
        ] {
            let argv = argv.into_iter().map(str::to_string).collect::<Vec<_>>();
            assert!(ls_direct_ctime_case(&argv).is_none(), "{argv:?}");
            assert!(!ls_argv_respects_mode_dependencies(&argv), "{argv:?}");
        }
    }

    fn selects_access_time_sort(argv: &[String]) -> bool {
        argv.iter().any(|arg| arg == "-t")
            && argv.iter().any(|arg| {
                matches!(
                    arg.as_str(),
                    "-u" | "--time=atime" | "--time=access" | "--time=use"
                )
            })
    }

    // Access-time sorting excludes symbolic-link fixtures whose reads can mutate host atime.
    #[test]
    fn generated_access_time_sort_excludes_symlink_fixtures() {
        let pool = option_pool();
        let symlink_fixture = fixture();

        for seed in 0..8192 {
            let mut rng = StdRng::seed_from_u64(seed);
            let argv = render_pattern(&pool, &mut rng, 12, &symlink_fixture);
            assert!(!selects_access_time_sort(&argv), "seed {seed}: {argv:?}");
        }
    }

    // Access-time sorting remains reachable for fixtures whose reads preserve modeled timestamps.
    #[test]
    fn generated_access_time_sort_reaches_plain_file_fixtures() {
        let pool = option_pool();
        let mut file_fixture = fixture();
        file_fixture.symlinks.clear();

        for seed in 0..8192 {
            let mut rng = StdRng::seed_from_u64(seed);
            let argv = render_pattern(&pool, &mut rng, 12, &file_fixture);
            if selects_access_time_sort(&argv) {
                return;
            }
        }

        panic!("access-time sorting did not reach a plain-file fixture");
    }

    // Metadata-producing logical listings require every implicit symlink target to resolve.
    #[test]
    fn followed_entry_metadata_contexts_are_detected() {
        for argv in [
            vec!["-Ln".to_string()],
            vec!["--dereference".to_string(), "-S".to_string()],
            vec!["-LR".to_string()],
        ] {
            assert!(ls_argv_requires_followed_entry_metadata(&argv));
        }
    }

    // Name-only, command-line-only, and directory-self listings do not inspect implicit targets.
    #[test]
    fn non_followed_entry_metadata_contexts_are_rejected() {
        for argv in [
            vec!["--dereference".to_string()],
            vec!["-Hn".to_string()],
            vec!["-Lnd".to_string()],
        ] {
            assert!(!ls_argv_requires_followed_entry_metadata(&argv));
        }
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = ls_fixture();
    Some(match iteration {
        0 => case(&[], fixture),
        1 => case(&["-a"], fixture),
        2 => case(&["-A"], fixture),
        3 => case(&["-d", "visible", "tree"], fixture),
        4 => case(&["-n"], fixture),
        5 => case(&["-s", "--block-size=1024"], fixture),
        6 => case(&["-S", "visible", "large"], fixture),
        7 => case(&["-t", "-r", "visible", "large"], fixture),
        8 => case(&["-n", "--time-style=+%s", "-H", "file-link"], fixture),
        9 => case(&["-L", "dir-link"], fixture),
        10 => case(&["-R", "tree"], fixture),
        11 => case(&["-R", "-L", "tree"], fixture),
        12 => case(&["missing", "empty"], fixture),
        13 => case(&["empty", "empty"], fixture),
        14 => case(&["dangling-link"], fixture),
        15 => case(&["--all", "-t", "-L", "dir-link"], fixture),
        16 => case(&["-n", "--size", "--block-size=512"], fixture),
        17 => case(&["--all", "-S", "dir-link"], fixture),
        18 => case(&["--dereference"], fixture),
        19 => case(&["--dereference", "dangling-link"], fixture),
        20 => case(
            &["-n", "-d", "--time=status", "--time-style=+%s", "visible"],
            fixture,
        ),
        21 => case(&["-n", "--time-style=XX"], fixture),
        22 => case(&["--time=XX"], fixture),
        23 => case(&["--block-size=0"], fixture),
        24 => case(&["-a", "-A"], fixture),
        25 => case(&["-S", "-t", "zzz-large", "aaa-small"], fixture),
        26 => case(
            &["-n", "-d", "-u", "-c", "--time-style=+%s", "visible"],
            fixture,
        ),
        27 => case(
            &["-n", "--time-style=+%s", "-H", "-L", "tree/child"],
            fixture,
        ),
        28 => case(
            &[
                "-n",
                "--time-style=+%s",
                "--block-size=512",
                "--block-size=1024",
                "zzz-large",
            ],
            fixture,
        ),
        29 => case(
            &["-n", "--time-style=long-iso", "--time-style=+%s", "visible"],
            fixture,
        ),
        30 => case(&["visible", "-n", "--time-style=+%s"], fixture),
        31 => case(&["-n", "--time=XX", "--block-size=0"], fixture),
        _ => return None,
    })
}

fn ls_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![
            DirSpec {
                relative_path: PathBuf::from("empty"),
                mode: 0o755,
            },
            DirSpec {
                relative_path: PathBuf::from("tree"),
                mode: 0o755,
            },
            DirSpec {
                relative_path: PathBuf::from("tree/child"),
                mode: 0o755,
            },
        ],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("zzz-large"),
                bytes: vec![b'x'; 600],
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("aaa-small"),
                bytes: b"x".to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("visible"),
                bytes: b"x".to_vec(),
                mode: 0o640,
            },
            FileSpec {
                relative_path: PathBuf::from("large"),
                bytes: b"larger payload".to_vec(),
                mode: 0o755,
            },
            FileSpec {
                relative_path: PathBuf::from(".hidden"),
                bytes: b"hidden".to_vec(),
                mode: 0o600,
            },
            FileSpec {
                relative_path: PathBuf::from("tree/child/leaf"),
                bytes: b"leaf".to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: vec![
            SymlinkSpec {
                relative_path: PathBuf::from("file-link"),
                target: PathBuf::from("visible"),
            },
            SymlinkSpec {
                relative_path: PathBuf::from("dir-link"),
                target: PathBuf::from("tree/child"),
            },
            SymlinkSpec {
                relative_path: PathBuf::from("dangling-link"),
                target: PathBuf::from("missing-target"),
            },
            SymlinkSpec {
                relative_path: PathBuf::from("tree/child/back"),
                target: PathBuf::from(".."),
            },
        ],
        hardlinks: vec![HardlinkSpec {
            relative_path: PathBuf::from("visible-hard"),
            source_relative_path: PathBuf::from("visible"),
        }],
    }
}

fn case(argv: &[&str], fixture: FixtureBlueprint) -> GeneratedCase {
    GeneratedCase {
        argv: argv.iter().map(|arg| (*arg).to_string()).collect(),
        fixture,
        stdin: Vec::new(),
        cwd: PathBuf::from("."),
    }
}

#[cfg(test)]
mod scenario_tests {
    use super::scenario_case;

    // Deterministic seeds cover every high-value modeled listing behavior before mutation begins.
    #[test]
    fn scenarios_cover_modeled_listing_shapes() {
        let scenarios: Vec<_> = (0..32)
            .map(|iteration| scenario_case(iteration).expect("registered ls scenario"))
            .collect();

        assert!(scenarios.iter().any(|case| case.argv.is_empty()));
        assert!(scenarios.iter().any(|case| case.argv == ["-a"]));
        assert!(scenarios.iter().any(|case| case.argv == ["-A"]));
        assert!(scenarios
            .iter()
            .any(|case| case.argv.iter().any(|arg| arg == "--time-style=+%s")));
        assert!(scenarios
            .iter()
            .any(|case| case.argv.iter().any(|arg| arg == "--block-size=1024")));
        assert!(scenarios.iter().any(|case| case.argv == ["-R", "tree"]));
        assert!(scenarios
            .iter()
            .any(|case| case.argv == ["-R", "-L", "tree"]));
        assert!(scenarios
            .iter()
            .any(|case| case.argv == ["missing", "empty"]));
        assert!(scenarios.iter().any(|case| case.argv == ["empty", "empty"]));
        assert!(scenarios.iter().any(|case| case.argv == ["dangling-link"]));
        assert!(scenarios
            .iter()
            .any(|case| case.argv == ["--all", "-t", "-L", "dir-link"]));
        assert!(scenarios
            .iter()
            .any(|case| { case.argv == ["-n", "--size", "--block-size=512"] }));
        assert!(scenarios
            .iter()
            .any(|case| case.argv == ["--all", "-S", "dir-link"]));
        assert!(scenarios.iter().any(|case| case.argv == ["--dereference"]));
        assert!(scenarios
            .iter()
            .any(|case| case.argv == ["--dereference", "dangling-link"]));
        assert!(scenarios.iter().any(|case| {
            case.argv == ["-n", "-d", "--time=status", "--time-style=+%s", "visible"]
        }));
        assert!(scenario_case(32).is_none());
    }

    // 숫자 긴 출력의 잘못된 시각 형식은 명세의 오류 모드를 고정 실행한다.
    #[test]
    fn invalid_time_style_scenario_is_registered() {
        let scenario = scenario_case(21).expect("invalid time-style scenario");

        assert_eq!(scenario.argv, ["-n", "--time-style=XX"]);
    }

    // 잘못된 시각 선택자는 명세의 --time 오류 모드를 고정 실행한다.
    #[test]
    fn invalid_time_field_scenario_is_registered() {
        let scenario = scenario_case(22).expect("invalid time-field scenario");

        assert_eq!(scenario.argv, ["--time=XX"]);
    }

    // 0 블록 크기는 명세의 양수 검사 오류 모드를 고정 실행한다.
    #[test]
    fn zero_block_size_scenario_is_registered() {
        let scenario = scenario_case(23).expect("zero block-size scenario");

        assert_eq!(scenario.argv, ["--block-size=0"]);
    }

    // 숨김 옵션 우선순위 사례는 뒤의 -A가 -a를 덮어쓰는 순서를 보존한다.
    #[test]
    fn hidden_mode_precedence_scenario_keeps_option_order() {
        let scenario = scenario_case(24).expect("hidden precedence scenario");

        assert_eq!(scenario.argv, ["-a", "-A"]);
    }

    // 정렬 우선순위 사례는 크기와 시각 정렬이 서로 다른 순서를 만들 수 있다.
    #[test]
    fn sort_precedence_scenario_has_distinguishable_files() {
        let scenario = scenario_case(25).expect("sort precedence scenario");
        let large = scenario
            .fixture
            .files
            .iter()
            .find(|file| file.relative_path == std::path::Path::new("zzz-large"))
            .expect("large sort fixture");
        let small = scenario
            .fixture
            .files
            .iter()
            .find(|file| file.relative_path == std::path::Path::new("aaa-small"))
            .expect("small sort fixture");

        assert_eq!(scenario.argv, ["-S", "-t", "zzz-large", "aaa-small"]);
        assert!(large.bytes.len() > small.bytes.len());
    }

    // 시각 필드 우선순위 사례는 뒤의 -c를 검증 가능한 직접 변경 시각 형태로 유지한다.
    #[test]
    fn time_field_precedence_scenario_keeps_direct_ctime_shape() {
        let scenario = scenario_case(26).expect("time-field precedence scenario");

        assert_eq!(
            scenario.argv,
            ["-n", "-d", "-u", "-c", "--time-style=+%s", "visible"]
        );
    }

    // 링크 추적 우선순위 사례는 뒤의 -L이 암시적 링크에 적용될 디렉터리를 나열한다.
    #[test]
    fn follow_precedence_scenario_lists_an_implicit_symlink() {
        let scenario = scenario_case(27).expect("follow precedence scenario");

        assert_eq!(
            scenario.argv,
            ["-n", "--time-style=+%s", "-H", "-L", "tree/child"]
        );
        assert!(scenario
            .fixture
            .symlinks
            .iter()
            .any(|link| link.relative_path == std::path::Path::new("tree/child/back")));
    }

    // 반복 블록 크기 사례는 서로 다른 결과를 내는 두 값을 명령행 순서대로 유지한다.
    #[test]
    fn repeated_block_size_scenario_keeps_distinct_values() {
        let scenario = scenario_case(28).expect("repeated block-size scenario");

        assert_eq!(
            scenario.argv,
            [
                "-n",
                "--time-style=+%s",
                "--block-size=512",
                "--block-size=1024",
                "zzz-large"
            ]
        );
    }

    // 반복 시각 형식 사례는 뒤의 시대 초 형식이 앞선 긴 ISO 형식을 덮어쓴다.
    #[test]
    fn repeated_time_style_scenario_keeps_distinct_values() {
        let scenario = scenario_case(29).expect("repeated time-style scenario");

        assert_eq!(
            scenario.argv,
            ["-n", "--time-style=long-iso", "--time-style=+%s", "visible"]
        );
    }

    // GNU 순열 구문 사례는 피연산자 뒤의 지원 옵션을 그대로 보존한다.
    #[test]
    fn operand_before_options_scenario_is_registered() {
        let scenario = scenario_case(30).expect("permuted option scenario");

        assert_eq!(scenario.argv, ["visible", "-n", "--time-style=+%s"]);
    }

    // 먼저 나온 즉시 오류 사례는 뒤의 다른 오류 옵션보다 시각 선택자 오류를 우선한다.
    #[test]
    fn immediate_error_precedence_scenario_keeps_argument_order() {
        let scenario = scenario_case(31).expect("immediate error precedence scenario");

        assert_eq!(scenario.argv, ["-n", "--time=XX", "--block-size=0"]);
    }

    // Recursive logical traversal receives an ancestor symlink cycle in its fixture.
    #[test]
    fn logical_recursive_scenario_contains_cycle_fixture() {
        let case = scenario_case(11).expect("logical recursive ls scenario");
        let cycle = case
            .fixture
            .symlinks
            .iter()
            .find(|link| link.relative_path == std::path::Path::new("tree/child/back"))
            .expect("ancestor cycle symlink");

        assert_eq!(cycle.target, std::path::Path::new(".."));
    }
}
