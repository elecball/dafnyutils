use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, ValueSource,
};
use super::super::PatternInputGenerator;
use super::super::{support, system_state};
use crate::fuzz::{DirSpec, GeneratedCase, SymlinkSpec};
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

const VERBOSE: Atom = Atom::Option(OptionChoice::available(&["-v", "--verbose"]));
const INFORMATION: Atom = Atom::Option(OptionChoice::available(&["--help", "--version"]));
const TARGET: Atom = Atom::Operand(OperandSource::Generated(directory_operand));
const MALFORMED: Atom = Atom::Value(ValueSource::Values(&[
    "--bogus",
    "-Q",
    "-vQ",
    "--verbose=value",
    "--help=value",
    "--ver",
    "--v",
    "-é",
    "--=x",
]));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::weighted(
        7,
        &[
            Element::repeated(0, 2, VERBOSE),
            Element::up_to_budget(0, TARGET).captured(0).reusing(25),
        ],
    ),
    Alternative::weighted(2, &[Element::once(MALFORMED)]),
    Alternative::weighted(
        2,
        &[
            Element::optional(50, TARGET),
            Element::repeated(1, 2, INFORMATION),
            Element::optional(30, MALFORMED),
        ],
    ),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

fn directory_operand(
    context: &super::super::pattern::ValueContext<'_>,
    rng: &mut StdRng,
) -> String {
    let existing = context.fixture().existing_operands();
    if !existing.is_empty() && rng.random_bool(0.3) {
        return support::pick_string(&existing, rng);
    }
    let name = format!("new-dir-{}", rng.random_range(0..10000));
    match rng.random_range(0..6) {
        0 => format!("absent-parent/{name}"),
        1 if !context.fixture().directories.is_empty() => {
            let directory = &context.fixture().directories
                [rng.random_range(0..context.fixture().directories.len())];
            directory.relative_path.join(name).display().to_string()
        }
        2 => format!("{name}/"),
        _ => name,
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let mut fixture = system_state::basic_fixture();
    let args = match iteration {
        0 => vec!["new-directory"],
        1 => vec!["-v", "first", "first", "last"],
        2 => vec!["first", "absent/child", "last"],
        3 => vec!["parent", "parent/child"],
        4 => vec![],
        5 => vec!["-v"],
        6 => vec!["trailing///"],
        7 => vec!["-vv", "one", "two"],
        8 => vec!["--verb", "abbreviated"],
        9 => vec!["--ver"],
        10 => vec!["--v"],
        11 => vec!["--help", "--bogus"],
        12 => vec!["--bogus", "--help"],
        13 => vec!["--version", "--help"],
        14 => vec!["--help", "--version"],
        15 => vec!["--verbose=value"],
        16 => vec!["-vQ"],
        17 => vec!["-é"],
        18 => vec!["-v", "--", "--help", "-v"],
        19 => vec![""],
        20 => vec!["."],
        21 => vec![".."],
        22 => vec!["a.txt/child"],
        23 => vec!["dir"],
        24 => vec!["-v", "a'b", "line\nbreak", "tab\tname", "한글"],
        25 => {
            fixture.symlinks.push(SymlinkSpec {
                relative_path: PathBuf::from("slink"),
                target: PathBuf::from("."),
            });
            vec!["slink/new"]
        }
        26 => {
            fixture.symlinks.push(SymlinkSpec {
                relative_path: PathBuf::from("dangling"),
                target: PathBuf::from("absent"),
            });
            vec!["dangling/"]
        }
        27 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("blocked"),
                mode: 0o555,
            });
            vec!["first", "blocked/new", "last"]
        }
        28 => vec!["--=x"],
        29 => vec!["-v", "a'b", "a'b"],
        30 => vec!["a'b/child"],
        _ => return None,
    };
    Some(support::case(args, fixture, b""))
}
