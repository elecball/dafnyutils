use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueContext, ValueSource,
};
use super::super::PatternInputGenerator;
use super::super::{support, system_state};
use super::chmod::random_chmod_mode;
use crate::fuzz::{DirSpec, GeneratedCase, SymlinkSpec};
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

const MODE: Atom = Atom::OptionValue(OptionValue::new(
    &[
        OptionValueForm::separate("-m"),
        OptionValueForm::attached("-m"),
        OptionValueForm::separate("--mode"),
        OptionValueForm::equals("--mode"),
    ],
    ValueSource::Generated(mode_value),
));
const INFORMATION: Atom = Atom::Option(OptionChoice::available(&["--help", "--version"]));
const TARGET: Atom = Atom::Operand(OperandSource::Generated(fifo_operand));
const MALFORMED: Atom = Atom::Value(ValueSource::Values(&[
    "--bogus",
    "-Q",
    "-Qm",
    "--help=value",
    "--version=1",
    "--he=x",
    "-é",
    "--=",
    "--=x",
]));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::weighted(
        7,
        &[
            Element::repeated(0, 2, MODE),
            Element::up_to_budget(0, TARGET).captured(0).reusing(25),
        ],
    ),
    // GNU getopt permutes options after operands.
    Alternative::weighted(
        2,
        &[
            Element::once(TARGET),
            Element::once(MODE),
            Element::up_to_budget(0, TARGET),
        ],
    ),
    Alternative::weighted(
        2,
        &[Element::once(MALFORMED), Element::optional(50, TARGET)],
    ),
    // Information requests win over a later MODE or malformed option.
    Alternative::weighted(
        2,
        &[
            Element::optional(40, MODE),
            Element::optional(50, TARGET),
            Element::repeated(1, 2, INFORMATION),
            Element::optional(40, MODE),
            Element::optional(30, MALFORMED),
        ],
    ),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

// MODE strings: chmod's generator plus cases specific to mkfifo's 0666 start,
// octal actions inside symbolic modes, and malformed clause lists.
fn mode_value(_context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    const MKFIFO_MODES: &[&str] = &[
        "+644,u+x",
        "=644,+x",
        "+0",
        "u=g",
        "g=u,o-r",
        "a=",
        "=",
        "+",
        "uu+r",
        "+X",
        "u+x,+X",
        "o+s",
        "g+t",
        "u+s",
        "+t",
        "4644",
        "00000000644",
        "u+r,",
        ",u+r",
        "u+r,,g+w",
        "+ur",
        "u+644",
        "+644u",
        "+644+r",
        "",
        "8",
    ];
    if rng.random_bool(0.4) {
        MKFIFO_MODES[rng.random_range(0..MKFIFO_MODES.len())].to_string()
    } else {
        random_chmod_mode(rng)
    }
}

fn fifo_operand(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let existing = context.fixture().existing_operands();
    if !existing.is_empty() && rng.random_bool(0.3) {
        return support::pick_string(&existing, rng);
    }
    let name = format!("new-fifo-{}", rng.random_range(0..10000));
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
        0 => vec!["fifo"],
        1 => vec!["-m", "734", "f2"],
        2 => vec!["--mode=ug+rw,o+r", "f5"],
        3 => vec!["-m", "+644,u+x", "p"],
        4 => vec!["-m", "bad", "p", "q"],
        5 => vec!["-m", "u+s", "p"],
        6 => vec!["-m", "bad"],
        7 => vec![],
        8 => vec!["first", "absent/child", "last"],
        9 => vec!["-m", "600", "first", "absent/child", "last"],
        10 => vec!["-m", "640", "p", "p"],
        11 => vec!["x", "-m", "640", "y"],
        12 => vec!["-m", "600", "-m", "640", "z"],
        13 => vec!["-m600", "p"],
        14 => vec!["--mo=700", "p"],
        15 => vec!["--", "-j", "--help"],
        16 => vec!["--help", "--bogus"],
        17 => vec!["--bogus", "--help"],
        18 => vec!["-m", "bad", "--help"],
        19 => vec!["--=x"],
        20 => vec![""],
        21 => vec!["."],
        22 => vec!["a.txt/child"],
        23 => vec!["dir"],
        24 => vec!["a'b/p", "line\nbreak/p", "tab\tname/p", "한글/p"],
        25 => {
            fixture.symlinks.push(SymlinkSpec {
                relative_path: PathBuf::from("dangling"),
                target: PathBuf::from("absent"),
            });
            vec!["-m", "600", "dangling"]
        }
        26 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("blocked"),
                mode: 0o555,
            });
            vec!["first", "blocked/new", "last"]
        }
        27 => vec!["-m", "=", "p"],
        28 => vec!["-m", "00000000644", "p"],
        _ => return None,
    };
    Some(support::case(args, fixture, b""))
}
