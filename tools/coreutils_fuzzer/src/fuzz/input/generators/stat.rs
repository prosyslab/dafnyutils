use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueContext, ValueSource,
};
use super::super::{mutation, PatternInputGenerator};
use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, GeneratedCase, HardlinkSpec, SymlinkSpec};
use rand::prelude::SliceRandom;
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutation::regenerate_argv);

const STAT_DIRECTIVES: &[char] = &[
    'a', 'b', 'B', 'd', 'D', 'f', 'g', 'h', 'i', 'o', 's', 'u', 'X', 'Y', 'Z', 'Q', '%',
];

const DEREFERENCE: Element = Element::optional(
    35,
    Atom::Option(OptionChoice::available(&["-L", "--dereference"])),
);
const FIRST_OPERAND: Element = Element::once(Atom::Operand(OperandSource::Existing));
const MORE_OPERANDS: Element = Element::repeated(
    0,
    3,
    Atom::Operand(OperandSource::Target {
        existing_percent: 80,
    }),
)
.reusing(15);
const FORMAT: Element = Element::once(Atom::OptionValue(OptionValue::new(
    &[
        OptionValueForm::separate("-c"),
        OptionValueForm::attached("-c"),
        OptionValueForm::separate("--format"),
        OptionValueForm::equals("--format"),
    ],
    ValueSource::Generated(generate_stat_format),
)));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::requiring(1, &["--help"], &[Element::once(Atom::Literal("--help"))]),
    Alternative::requiring(
        1,
        &["--version"],
        &[Element::once(Atom::Literal("--version"))],
    ),
    Alternative::weighted(13, &[FORMAT, DEREFERENCE, FIRST_OPERAND, MORE_OPERANDS]),
    Alternative::weighted(13, &[FIRST_OPERAND, FORMAT, DEREFERENCE, MORE_OPERANDS]),
    Alternative::weighted(13, &[FIRST_OPERAND, DEREFERENCE, FORMAT, MORE_OPERANDS]),
    Alternative::new(&[
        Element::once(Atom::Literal("-c")),
        Element::once(Atom::Value(ValueSource::Generated(generate_stat_format))),
        DEREFERENCE,
        FIRST_OPERAND,
        MORE_OPERANDS,
    ]),
]);

fn generate_stat_format(_context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let mut directives = STAT_DIRECTIVES.to_vec();
    directives.shuffle(rng);
    let count = rng.random_range(1..=usize::min(6, directives.len()));
    directives
        .into_iter()
        .take(count)
        .enumerate()
        .map(|(index, directive)| {
            let label = match directive {
                '%' => "pct".to_string(),
                'Q' => "q".to_string(),
                _ => directive.to_string(),
            };
            let rendered = if directive == '%' {
                "%%".to_string()
            } else {
                format!("%{directive}")
            };
            format!("{index}_{label}={rendered}")
        })
        .collect::<Vec<_>>()
        .join("|")
}

#[cfg(test)]
mod tests {
    use super::{ARGV_PATTERN, STAT_DIRECTIVES};
    use crate::fuzz::input::pattern;
    use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, HardlinkSpec, SymlinkSpec};
    use crate::utils::arg_semantics::positional_args;
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
                relative_path: PathBuf::from("regular"),
                bytes: b"payload".to_vec(),
                mode: 0o640,
            }],
            symlinks: vec![SymlinkSpec {
                relative_path: PathBuf::from("regular-link"),
                target: PathBuf::from("regular"),
            }],
            hardlinks: vec![HardlinkSpec {
                relative_path: PathBuf::from("regular-hard"),
                source_relative_path: PathBuf::from("regular"),
            }],
        }
    }

    fn option_pool() -> Vec<String> {
        [
            "-L",
            "--dereference",
            "-c",
            "--format",
            "--help",
            "--version",
        ]
        .into_iter()
        .map(str::to_string)
        .collect()
    }

    fn format_arg(argv: &[String]) -> Option<&str> {
        for (index, arg) in argv.iter().enumerate() {
            if matches!(arg.as_str(), "-c" | "--format") {
                return argv.get(index + 1).map(String::as_str);
            }
            if let Some(format) = arg.strip_prefix("--format=") {
                return Some(format);
            }
            if let Some(format) = arg.strip_prefix("-c").filter(|format| !format.is_empty()) {
                return Some(format);
            }
        }
        None
    }

    fn render_pattern(
        option_pool: &[String],
        rng: &mut StdRng,
        max_args: usize,
        fixture: &FixtureBlueprint,
    ) -> Vec<String> {
        pattern::generate(&ARGV_PATTERN, option_pool, rng, max_args, fixture)
    }

    // 실행 모드의 무작위 stat 명령은 필수 형식과 하나 이상의 경로를 항상 유지한다.
    #[test]
    fn generated_run_commands_keep_format_and_operand_roles() {
        let options = option_pool();
        let fixture = fixture();
        for seed in 0..2048 {
            let mut rng = StdRng::seed_from_u64(seed);
            let argv = render_pattern(&options, &mut rng, 8, &fixture);
            if argv
                .iter()
                .any(|arg| matches!(arg.as_str(), "--help" | "--version"))
            {
                continue;
            }
            assert!(format_arg(&argv).is_some(), "seed {seed}: {argv:?}");
            assert!(
                !positional_args("stat", &argv).is_empty(),
                "seed {seed}: {argv:?}"
            );
        }
    }

    // 형식 생성기 불변식은 모든 모델 지시자가 무작위 탐색에서 도달 가능함을 보장한다.
    #[test]
    fn generated_formats_reach_every_modeled_directive() {
        let options = option_pool();
        let fixture = fixture();
        let mut seen = BTreeSet::new();
        for seed in 0..8192 {
            let mut rng = StdRng::seed_from_u64(seed);
            let argv = render_pattern(&options, &mut rng, 8, &fixture);
            let Some(format) = format_arg(&argv) else {
                continue;
            };
            for directive in STAT_DIRECTIVES {
                let marker = if *directive == '%' {
                    "%%".to_string()
                } else {
                    format!("%{directive}")
                };
                if format.contains(&marker) {
                    seen.insert(*directive);
                }
            }
        }

        assert_eq!(seen, STAT_DIRECTIVES.iter().copied().collect());
    }

    // GNU tests/split/filter.sh의 stat -c%s 호출과 같은 결합형 짧은 옵션에 도달한다.
    #[test]
    fn generated_formats_reach_attached_short_option() {
        let options = option_pool();
        let fixture = fixture();
        let reached = (0..8192).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let argv = render_pattern(&options, &mut rng, 8, &fixture);
            argv.iter().any(|arg| arg.starts_with("-c") && arg != "-c")
        });

        assert!(reached);
    }

    // GNU option permutation remains reachable by placing the format production after an operand.
    #[test]
    fn generated_formats_reach_positions_after_operands() {
        let options = option_pool();
        let fixture = fixture();
        let reached = (0..8192).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let argv = render_pattern(&options, &mut rng, 8, &fixture);
            argv.first().is_some_and(|arg| !arg.starts_with('-'))
                && argv.iter().skip(1).any(|arg| {
                    matches!(arg.as_str(), "-c" | "--format")
                        || arg.starts_with("-c")
                        || arg.starts_with("--format=")
                })
        });

        assert!(reached);
    }

    // GNU tests/stat/stat-printf.pl의 f-nl2처럼 같은 피연산자를 반복 조회하는 형태에 도달한다.
    #[test]
    fn generated_operands_reach_duplicates() {
        let options = option_pool();
        let fixture = fixture();
        let reached = (0..8192).any(|seed| {
            let mut rng = StdRng::seed_from_u64(seed);
            let argv = render_pattern(&options, &mut rng, 8, &fixture);
            let operands = positional_args("stat", &argv);
            operands
                .iter()
                .enumerate()
                .any(|(index, operand)| operands[..index].contains(operand))
        });

        assert!(reached);
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = stat_fixture();
    Some(match iteration {
        // GNU tests/stat/stat-nanoseconds.sh의 stat -c %Y k 명령의 옵션·형식 조합을 모델 파일에 적용한다.
        0 => case(vec!["-c", "%Y", "regular"], fixture),
        // GNU tests/stat/stat-slash.sh의 link1 비추적 조회를 수치 모드 형식으로 실행한다.
        1 => case(vec!["--format=%f", "regular-link"], fixture),
        // GNU tests/stat/stat-slash.sh의 link1/ 실패를 수치 모드 형식으로 실행한다.
        2 => case(vec!["--format=%f", "regular-link/"], fixture),
        // GNU tests/stat/stat-slash.sh의 link2 비추적 조회를 수치 모드 형식으로 실행한다.
        3 => case(vec!["--format=%f", "dir-link"], fixture),
        // GNU tests/stat/stat-slash.sh의 stat -L link2 조회를 수치 모드 형식으로 실행한다.
        4 => case(vec!["-L", "--format=%f", "dir-link"], fixture),
        // GNU tests/stat/stat-slash.sh의 link2/ 암시적 추적 조회를 수치 모드 형식으로 실행한다.
        5 => case(vec!["--format=%f", "dir-link/"], fixture),
        // GNU tests/stat/stat-printf.pl의 f-nl2처럼 같은 피연산자의 줄바꿈을 두 번 관찰한다.
        6 => case(vec!["--format=%s", "regular", "regular"], fixture),
        // GNU tests/help/help-version.sh의 도움말 실행을 그대로 사용한다.
        7 => case(vec!["--help"], fixture),
        // GNU tests/help/help-version.sh의 버전 실행을 그대로 사용한다.
        8 => case(vec!["--version"], fixture),
        // GNU tests/stat/stat-fmt.sh의 끝 백분율 형식을 --format 모드로 실행한다.
        9 => case(vec!["-c", "%", "regular"], fixture),
        // GNU tests/stat/stat-printf.pl의 pct-pct 형식을 --format 모드로 실행한다.
        10 => case(vec!["-c", "%%", "regular"], fixture),
        // GNU tests/split/filter.sh의 결합형 -c%s 표기를 모델 파일에 적용한다.
        11 => case(vec!["-c%s", "regular"], fixture),
        // GNU tests/du/basic.sh의 할당 블록 수 형식을 모델 디렉터리에 적용한다.
        12 => case(vec!["--format=%b", "dir/child"], fixture),
        // GNU tests/du/basic.sh의 블록 단위 형식을 모델 디렉터리에 적용한다.
        13 => case(vec!["--format=%B", "dir/child"], fixture),
        // GNU tests/mv/childproof.sh의 아이노드 동치 검사를 하드 링크 이름에 적용한다.
        14 => case(vec!["--format=%i", "regular", "regular-hard"], fixture),
        // GNU tests/stat/stat-birthtime.sh의 접근 시각 초 형식을 실행한다.
        15 => case(vec!["--format=%X", "regular"], fixture),
        // GNU tests/stat/stat-birthtime.sh의 변경 시각 초 형식을 실행한다.
        16 => case(vec!["--format=%Z", "regular"], fixture),
        _ => return None,
    })
}

fn stat_fixture() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![
            DirSpec {
                relative_path: PathBuf::from("dir"),
                mode: 0o2755,
            },
            DirSpec {
                relative_path: PathBuf::from("dir/child"),
                mode: 0o755,
            },
        ],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("regular"),
                bytes: b"payload".to_vec(),
                mode: 0o4640,
            },
            FileSpec {
                relative_path: PathBuf::from("empty"),
                bytes: Vec::new(),
                mode: 0o600,
            },
        ],
        symlinks: vec![
            SymlinkSpec {
                relative_path: PathBuf::from("regular-link"),
                target: PathBuf::from("regular"),
            },
            SymlinkSpec {
                relative_path: PathBuf::from("dangling-link"),
                target: PathBuf::from("missing-stat-target"),
            },
            SymlinkSpec {
                relative_path: PathBuf::from("dir-link"),
                target: PathBuf::from("dir"),
            },
        ],
        hardlinks: vec![HardlinkSpec {
            relative_path: PathBuf::from("regular-hard"),
            source_relative_path: PathBuf::from("regular"),
        }],
    }
}

fn case(argv: Vec<&str>, fixture: FixtureBlueprint) -> GeneratedCase {
    GeneratedCase {
        argv: argv.into_iter().map(str::to_string).collect(),
        fixture,
        stdin: Vec::new(),
        cwd: PathBuf::from("."),
    }
}

#[cfg(test)]
mod scenario_tests {
    use super::scenario_case;
    use std::path::Path;

    // GNU tests/stat/stat-nanoseconds.sh의 -c %Y 옵션·형식 조합을 보존한다.
    #[test]
    fn nanosecond_scenario_keeps_gnu_whole_second_format() {
        let scenario = scenario_case(0).expect("stat nanosecond scenario");

        assert_eq!(scenario.argv, ["-c", "%Y", "regular"]);
    }

    // GNU tests/stat/stat-slash.sh처럼 일반 파일 대상 심볼릭 링크의 뒤 슬래시 실패 구조를 보존한다.
    #[test]
    fn file_symlink_trailing_slash_scenario_keeps_gnu_fixture() {
        let scenario = scenario_case(2).expect("stat file-link slash scenario");

        assert_eq!(
            scenario.argv.last().map(String::as_str),
            Some("regular-link/")
        );
        assert!(scenario.fixture.symlinks.iter().any(|link| {
            link.relative_path.as_path() == Path::new("regular-link")
                && link.target.as_path() == Path::new("regular")
        }));
    }

    // GNU tests/stat/stat-printf.pl의 f-nl2처럼 같은 피연산자를 두 번 유지한다.
    #[test]
    fn repeated_operand_scenario_keeps_gnu_record_count_shape() {
        let scenario = scenario_case(6).expect("stat repeated operand scenario");

        assert_eq!(scenario.argv, ["--format=%s", "regular", "regular"]);
    }

    // GNU tests/stat/stat-fmt.sh의 끝 백분율 형식을 그대로 보존한다.
    #[test]
    fn trailing_percent_scenario_keeps_gnu_format() {
        let scenario = scenario_case(9).expect("stat trailing percent scenario");

        assert_eq!(scenario.argv, ["-c", "%", "regular"]);
    }

    // GNU tests/split/filter.sh의 결합형 -c%s 표기를 보존한다.
    #[test]
    fn attached_short_format_scenario_keeps_gnu_spelling() {
        let scenario = scenario_case(11).expect("stat attached-format scenario");

        assert_eq!(scenario.argv, ["-c%s", "regular"]);
    }

    // GNU tests/mv/childproof.sh의 아이노드 동치 검사를 하드 링크 이름에 적용한다.
    #[test]
    fn inode_scenario_keeps_hardlink_identity_fixture() {
        let scenario = scenario_case(14).expect("stat inode scenario");

        assert_eq!(scenario.argv, ["--format=%i", "regular", "regular-hard"]);
        assert!(scenario.fixture.hardlinks.iter().any(|link| {
            link.relative_path.as_path() == Path::new("regular-hard")
                && link.source_relative_path.as_path() == Path::new("regular")
        }));
    }
}
