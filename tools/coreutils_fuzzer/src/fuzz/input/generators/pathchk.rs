use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, ValueContext, ValueSource};
use super::super::{support, PatternInputGenerator};
use crate::fuzz::{FixtureBlueprint, GeneratedCase};
use rand::{rngs::StdRng, Rng};

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_system_state(|_, _| empty_state())
        .with_candidate_guard(in_scope)
        .with_mutation_guard(in_scope);

const MODE: Atom = Atom::Value(ValueSource::Values(&["-p", "-pP", "-Pp", "--portability"]));
const OPTION: Atom = Atom::Value(ValueSource::Values(&[
    "-p",
    "-P",
    "--portability",
    "--help",
    "--version",
    "--po",
    "--he",
    "--ver",
]));
const NAME: Atom = Atom::Value(ValueSource::Generated(name));
const INVALID: Atom = Atom::Value(ValueSource::Values(&[
    "-x",
    "-pPx",
    "-pé",
    "--bad",
    "--po=x",
    "--help=x",
    "--version=x",
    "--=x",
]));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::new(&[
        Element::once(MODE),
        Element::repeated(0, 2, OPTION),
        Element::repeated(0, 4, NAME),
    ]),
    Alternative::new(&[
        Element::once(MODE),
        Element::once(Atom::Literal("--")),
        Element::repeated(1, 4, NAME),
    ]),
    Alternative::new(&[Element::once(INVALID)]),
    Alternative::new(&[
        Element::once(Atom::Literal("--help")),
        Element::once(INVALID),
    ]),
]);

fn in_scope(argv: &[String]) -> bool {
    let mut basic = false;
    for (index, token) in argv.iter().enumerate() {
        if token == "--" {
            return basic || index + 1 == argv.len();
        }
        if token == "-" || !token.starts_with('-') {
            return basic;
        }
        if let Some(name) = token.strip_prefix("--") {
            if !"portability".starts_with(name) {
                return true;
            }
            basic = true;
        } else if token[1..].bytes().any(|b| !matches!(b, b'p' | b'P')) {
            return true;
        } else {
            basic |= token.contains('p');
        }
    }
    true
}

fn name(_context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let mut chars: Vec<_> = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789._-/"
        .chars()
        .collect();
    if rng.random_bool(0.5) {
        chars.extend(" @'\"\\\n\té".chars());
    }
    (0..rng.random_range(0..=32))
        .map(|_| chars[rng.random_range(0..chars.len())])
        .collect()
}

fn empty_state() -> FixtureBlueprint {
    FixtureBlueprint {
        directories: Vec::new(),
        files: Vec::new(),
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = empty_state();
    Some(match iteration {
        0 => support::case(vec!["-p", "foo/bar.txt"], fixture, b""),
        1 => support::case(vec!["-p", ""], fixture, b""),
        2 => support::case(vec!["--portability", "foo/-bar"], fixture, b""),
        3 => support::case(vec!["-p", "a@b"], fixture, b""),
        4 => support::case(vec!["-p", &"a".repeat(14)], fixture, b""),
        5 => support::case(vec!["-p", &"a".repeat(15)], fixture, b""),
        6 => support::case(vec!["-p", &("a/".repeat(127) + "a")], fixture, b""),
        7 => support::case(vec!["-p", &"a/".repeat(128)], fixture, b""),
        8 => support::case(vec!["-p", &("a".repeat(15) + "/bad@")], fixture, b""),
        9 => support::case(vec!["--portability", "foo/-bad@"], fixture, b""),
        10 => support::case(vec!["-p", "good", "bad@", ""], fixture, b""),
        11 => support::case(vec!["-p", "///"], fixture, b""),
        12 => support::case(vec!["-p", "foo", "--help"], fixture, b""),
        13 => support::case(vec!["--portability", "foo", "-p"], fixture, b""),
        14 => support::case(vec!["-pP", "foo/-bar"], fixture, b""),
        15 => support::case(vec!["-Pp", "foo/-bar"], fixture, b""),
        16 => support::case(vec!["--help", "--bad"], fixture, b""),
        17 => support::case(vec!["--bad", "--help"], fixture, b""),
        18 => support::case(vec!["--version", "--help"], fixture, b""),
        19 => support::case(vec!["--help", "--version"], fixture, b""),
        20 => support::case(vec!["-pPx"], fixture, b""),
        21 => support::case(vec!["--po=x"], fixture, b""),
        22 => support::case(vec!["--=x"], fixture, b""),
        23 => support::case(vec![], fixture, b""),
        24 => support::case(vec!["-p"], fixture, b""),
        25 => support::case(vec!["-p", "é"], fixture, b""),
        26 => support::case(vec!["-p", "a\nb"], fixture, b""),
        27 => support::case(vec!["-p", "a'b"], fixture, b""),
        28 => support::case(vec!["--portability", "--", "-"], fixture, b""),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::in_scope;

    // The portability slice follows GNU's stop-at-first-operand option boundary.
    #[test]
    fn scope_guard_observes_the_first_operand() {
        let args = |values: &[&str]| {
            values
                .iter()
                .map(|value| (*value).to_string())
                .collect::<Vec<_>>()
        };
        assert!(in_scope(&args(&["-p", "foo", "--help"])));
        assert!(in_scope(&args(&["--portability", "foo", "-p"])));
        assert!(!in_scope(&args(&["foo", "-p"])));
        assert!(!in_scope(&args(&["-P", "foo", "-p"])));
        assert!(!in_scope(&args(&["--", "-p"])));
    }
}
