use super::capabilities::{capability_for, PathOperandPolicy, StdinPolicy};

pub(crate) fn path_operand_args<'a>(util: &str, argv: &'a [String]) -> Vec<&'a str> {
    let policy = capability_for(util)
        .map(|capability| capability.path_operand_policy)
        .unwrap_or(PathOperandPolicy::Default);
    if policy == PathOperandPolicy::Tail {
        return tail_path_operand_args(argv);
    }
    let positionals = positional_args(util, argv);
    match policy {
        PathOperandPolicy::Chmod
            if !argv
                .iter()
                .any(|arg| arg == "--reference" || arg.starts_with("--reference=")) =>
        {
            positionals.into_iter().skip(1).collect()
        }
        PathOperandPolicy::First => positionals.into_iter().take(1).collect(),
        _ => positionals,
    }
}

pub(crate) fn positional_args<'a>(util: &str, argv: &'a [String]) -> Vec<&'a str> {
    let mut operands = Vec::new();
    let mut in_operands = false;
    let mut skip_next = false;
    for arg in argv {
        if skip_next {
            skip_next = false;
            continue;
        }
        if in_operands {
            operands.push(arg.as_str());
            continue;
        }
        if arg == "--" {
            in_operands = true;
            continue;
        }
        if arg == "-" {
            operands.push(arg.as_str());
            continue;
        }
        if option_takes_value(util, arg) {
            skip_next = true;
            continue;
        }
        if !arg.starts_with('-') {
            operands.push(arg.as_str());
        }
    }
    operands
}

pub(crate) fn option_takes_value(util: &str, arg: &str) -> bool {
    if arg.contains('=') {
        return false;
    }
    capability_for(util).is_some_and(|capability| capability.option_value_flags.contains(&arg))
}

pub(crate) fn should_consume_stdin_from_argv(util: &str, argv: &[String]) -> bool {
    if requests_help_or_version(util, argv) {
        return false;
    }

    let positionals = positional_args(util, argv);
    match capability_for(util)
        .map(|capability| capability.stdin_policy)
        .unwrap_or(StdinPolicy::Never)
    {
        StdinPolicy::Stream => positionals.is_empty() || positionals.contains(&"-"),
        StdinPolicy::Comm => positionals.iter().filter(|arg| **arg == "-").count() == 1,
        StdinPolicy::Csplit => positionals.first().is_some_and(|arg| *arg == "-"),
        StdinPolicy::Tail => {
            !tail_prevents_reads(argv)
                && (tail_path_operand_args(argv).is_empty()
                    || tail_path_operand_args(argv).contains(&"-"))
        }
        StdinPolicy::Uniq => match positionals.first() {
            Some(arg) => *arg == "-",
            None => true,
        },
        StdinPolicy::Never => false,
    }
}

pub(crate) fn requests_help_or_version(util: &str, argv: &[String]) -> bool {
    let mut skip_next = false;
    for arg in argv {
        if skip_next {
            skip_next = false;
            continue;
        }
        if arg == "--" {
            return false;
        }
        if option_takes_value(util, arg) {
            skip_next = true;
            continue;
        }
        if matches!(arg.as_str(), "--help" | "--version") {
            return true;
        }
    }
    false
}

fn tail_path_operand_args(argv: &[String]) -> Vec<&str> {
    let mut operands = Vec::new();
    let mut in_operands = false;
    let mut skip_next = false;

    for (index, arg) in argv.iter().enumerate() {
        if skip_next {
            skip_next = false;
            continue;
        }
        if in_operands {
            operands.push(arg.as_str());
            continue;
        }
        if arg == "--" {
            in_operands = true;
            continue;
        }
        if index == 0 && tail_legacy_plus_count(arg) {
            continue;
        }
        if arg == "-" {
            operands.push(arg.as_str());
            continue;
        }
        if option_takes_value("tail", arg) {
            skip_next = true;
            continue;
        }
        if !arg.starts_with('-') {
            operands.push(arg.as_str());
        }
    }

    operands
}

fn tail_legacy_plus_count(arg: &str) -> bool {
    let Some(rest) = arg.strip_prefix('+') else {
        return false;
    };
    tail_count_body_is_valid(rest)
}

fn tail_count_body_is_valid(body: &str) -> bool {
    if body.is_empty() {
        return false;
    }
    let digits_len = body.bytes().take_while(u8::is_ascii_digit).count();
    if digits_len == 0 {
        matches!(body, "c" | "l" | "b")
    } else if digits_len == body.len() {
        true
    } else {
        matches!(&body[digits_len..], "c" | "l" | "b")
    }
}

fn tail_prevents_reads(argv: &[String]) -> bool {
    let mut index = 0;
    while index < argv.len() {
        let arg = argv[index].as_str();
        if arg == "--" {
            return false;
        }
        if matches!(arg, "-c" | "--bytes" | "-n" | "--lines") {
            return argv.get(index + 1).is_some_and(|value| {
                !tail_count_value_is_valid(value) || tail_count_is_zero_trailing(value)
            });
        }
        if let Some(value) = arg
            .strip_prefix("--bytes=")
            .or_else(|| arg.strip_prefix("--lines="))
        {
            return !tail_count_value_is_valid(value) || tail_count_is_zero_trailing(value);
        }
        if index == 0 && tail_legacy_zero_trailing_count(arg) {
            return true;
        }
        index += 1;
    }
    false
}

fn tail_count_value_is_valid(value: &str) -> bool {
    let body = value
        .strip_prefix('+')
        .or_else(|| value.strip_prefix('-'))
        .unwrap_or(value);
    let digits_len = body.bytes().take_while(u8::is_ascii_digit).count();
    let suffix = &body[digits_len..];
    tail_count_suffix_is_valid(suffix) && (digits_len > 0 || !suffix.is_empty())
}

fn tail_count_suffix_is_valid(suffix: &str) -> bool {
    matches!(
        suffix,
        "" | "b"
            | "K"
            | "k"
            | "kB"
            | "KB"
            | "KiB"
            | "m"
            | "M"
            | "MiB"
            | "MB"
            | "G"
            | "GiB"
            | "GB"
            | "T"
            | "TiB"
            | "TB"
            | "P"
            | "PiB"
            | "PB"
            | "E"
            | "EiB"
            | "EB"
    )
}

fn tail_count_is_zero_trailing(value: &str) -> bool {
    matches!(value, "0" | "-0")
}

fn tail_legacy_zero_trailing_count(arg: &str) -> bool {
    matches!(arg, "-0" | "-0c" | "-0l" | "-0b")
}

#[cfg(test)]
mod tests {
    use super::{path_operand_args, requests_help_or_version, should_consume_stdin_from_argv};

    // An option terminator makes a following help token an operand.
    #[test]
    fn help_after_option_terminator_is_not_requested() {
        let argv = vec!["--".to_string(), "--help".to_string(), "input".to_string()];

        assert!(!requests_help_or_version("ls", &argv));
    }

    // A stat format that spells --help remains an option value rather than an early-exit request.
    #[test]
    fn help_as_structured_option_value_is_not_requested() {
        let argv = vec![
            "-c".to_string(),
            "--help".to_string(),
            "regular".to_string(),
        ];

        assert!(!requests_help_or_version("stat", &argv));
    }

    // A separate chmod --reference value is metadata, not a target operand.
    #[test]
    fn chmod_reference_value_is_not_a_path_operand() {
        let argv = [
            "--reference".to_string(),
            "source".to_string(),
            "target".to_string(),
        ];

        assert_eq!(path_operand_args("chmod", &argv), ["target"]);
    }

    #[test]
    fn path_operands_skip_structured_option_values() {
        let head = vec!["-n".to_string(), "2".to_string(), "input.txt".to_string()];
        assert_eq!(path_operand_args("head", &head), vec!["input.txt"]);

        let cut = vec![
            "-b".to_string(),
            "1-3".to_string(),
            "--output-delimiter".to_string(),
            ":".to_string(),
            "input.txt".to_string(),
        ];
        assert_eq!(path_operand_args("cut", &cut), vec!["input.txt"]);

        let tail = vec!["+2c".to_string(), "input.txt".to_string()];
        assert_eq!(path_operand_args("tail", &tail), vec!["input.txt"]);

        let expand = vec!["-t".to_string(), "4".to_string(), "input.txt".to_string()];
        assert_eq!(path_operand_args("expand", &expand), vec!["input.txt"]);

        let csplit = vec![
            "-f".to_string(),
            "yy".to_string(),
            "input.txt".to_string(),
            "2".to_string(),
        ];
        assert_eq!(path_operand_args("csplit", &csplit), vec!["input.txt"]);

        let comm = vec![
            "--output-delimiter".to_string(),
            ",".to_string(),
            "left.txt".to_string(),
            "right.txt".to_string(),
        ];
        assert_eq!(
            path_operand_args("comm", &comm),
            vec!["left.txt", "right.txt"]
        );
    }

    // stat의 분리된 형식 값은 파일 경로가 아니라 선택지 인자로 분류한다.
    #[test]
    fn stat_format_value_is_not_a_path_operand() {
        let argv = vec![
            "-c".to_string(),
            "size=%s".to_string(),
            "first".to_string(),
            "second".to_string(),
        ];

        assert_eq!(path_operand_args("stat", &argv), vec!["first", "second"]);
    }

    // ls의 분리형 선택지 값은 나열할 파일 피연산자로 분류하지 않는다.
    #[test]
    fn ls_separate_option_values_are_not_path_operands() {
        let argv = vec![
            "--block-size".to_string(),
            "1024".to_string(),
            "--time".to_string(),
            "mtime".to_string(),
            "--time-style".to_string(),
            "+%s".to_string(),
            "payload".to_string(),
        ];

        assert_eq!(path_operand_args("ls", &argv), vec!["payload"]);
    }

    #[test]
    fn stdin_policy_covers_stream_utilities_and_csplit_input() {
        assert!(should_consume_stdin_from_argv("head", &[]));
        assert!(should_consume_stdin_from_argv("tail", &["+2c".to_string()]));
        assert!(!should_consume_stdin_from_argv(
            "tail",
            &["-c".to_string(), "9x".to_string(), "-".to_string()]
        ));
        assert!(!should_consume_stdin_from_argv(
            "tail",
            &["-n".to_string(), "0".to_string(), "-".to_string()]
        ));
        assert!(should_consume_stdin_from_argv("expand", &[]));
        assert!(should_consume_stdin_from_argv(
            "expand",
            &["-t4".to_string(), "-".to_string()]
        ));
        assert!(should_consume_stdin_from_argv("paste", &["-".to_string()]));
        assert!(should_consume_stdin_from_argv("uniq", &[]));
        assert!(should_consume_stdin_from_argv(
            "csplit",
            &["-".to_string(), "2".to_string()]
        ));
        assert!(!should_consume_stdin_from_argv(
            "csplit",
            &["input.txt".to_string(), "2".to_string()]
        ));
        assert!(should_consume_stdin_from_argv(
            "comm",
            &["-".to_string(), "right.txt".to_string()]
        ));
        assert!(!should_consume_stdin_from_argv(
            "comm",
            &["-".to_string(), "-".to_string()]
        ));
    }
}
