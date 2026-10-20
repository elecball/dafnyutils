use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, ValueContext, ValueSource,
};
use super::super::{mutations, support, system_state, PatternInputGenerator};
use crate::fuzz::{GeneratedCase, HardlinkSpec, UtilityProfile};
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

const TARGET: Atom = Atom::Operand(OperandSource::Target {
    existing_percent: 65,
});
const SIZE: Element = Element::once(Atom::Value(ValueSource::Generated(size_value)));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::weighted(
        5,
        &[
            Element::repeated(0, 2, Atom::Option(OptionChoice::available(&["-c", "-o"]))),
            Element::once(Atom::Literal("-s")),
            SIZE,
            Element::up_to_budget(1, TARGET),
        ],
    ),
    Alternative::new(&[
        Element::once(Atom::Literal("-r")),
        Element::once(Atom::Operand(OperandSource::ExistingFile)),
        Element::up_to_budget(1, TARGET),
    ]),
    Alternative::new(&[
        Element::once(Atom::Literal("-r")),
        Element::once(Atom::Operand(OperandSource::ExistingFile)),
        Element::once(Atom::Literal("-s")),
        Element::once(Atom::Value(ValueSource::Generated(relative_value))),
        Element::up_to_budget(1, TARGET),
    ]),
    Alternative::new(&[
        Element::once(Atom::Option(OptionChoice::available(&[
            "--help",
            "--version",
        ]))),
        Element::up_to_budget(0, TARGET),
    ]),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutations::regenerate_argv)
        .with_case_regeneration_on_argv_mutation()
        .with_profile(UtilityProfile {
            requires_path_operand: true,
            prefers_existing_paths: true,
        });

fn size_value(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    // Keep every materialized result bounded, including --io-blocks multiplication.
    let choices = if context.argv().iter().any(|arg| arg == "-o") {
        &["0", "1", "2", "+1", "-1", "<1", ">1", "/1", "%1"][..]
    } else {
        &[
            "0", "1", "3", "9", "+2", "-2", "-99", "<3", ">9", "/4", "%4", "1K", "1KB", "1KiB",
            "bad", "/0", "<+2", "1 ",
        ][..]
    };
    choices[rng.random_range(0..choices.len())].to_string()
}

fn relative_value(_context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let choices = ["+2", "-2", "<3", ">9", "/4", "%4"];
    choices[rng.random_range(0..choices.len())].to_string()
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let mut fixture = system_state::failure_fixture();
    fixture.hardlinks.push(HardlinkSpec {
        relative_path: PathBuf::from("alias"),
        source_relative_path: PathBuf::from("a.txt"),
    });
    let args = match iteration {
        0 => vec!["-c", "-s", "3", "a.txt"],
        1 => vec!["-s", "10", "created"],
        2 => vec!["-c", "-s", "10", "missing"],
        3 => vec!["-s", "2", "a-link"],
        4 => vec!["-s", "2", "dangling"],
        5 => vec!["-c", "-s", "2", "dangling"],
        6 => vec!["-s", "+2", "alias", "a.txt"],
        7 => vec!["-s", "2", "dir", "a.txt", "missing/child", "b.txt"],
        8 => vec!["-s", "2", "loop"],
        9 => vec!["-s", "2", "new/"],
        10 => vec!["-s", "2", "a.txt/"],
        11 => vec!["-s", "2", ""],
        12 => vec!["-r", "b.txt", "a.txt"],
        13 => vec!["-r", "b.txt", "-s", "+2", "a.txt"],
        14 => vec!["-r", "missing", "a.txt"],
        15 => vec!["-o", "-s", "1", "a.txt"],
        16 => vec!["-o", "-s", "9223372036854775807", "new"],
        17 => vec!["-c", "-s", "9223372036854775807", "missing"],
        18 => vec!["-c", "-s", "-9223372036854775808", "missing"],
        19 => vec!["-s", "9223372036854775808", "a.txt"],
        20 => vec!["-s", "+1", "-s", "+2", "a.txt"],
        21 => vec!["-s", "/2", "-s", "3", "a.txt"],
        22 => vec!["--help", "--bad"],
        23 => vec!["--bad", "--help"],
        24 => vec!["-s", "bad", "--help"],
        25 => vec!["--help", "-s", "bad"],
        26 => vec!["-s", "bad", "--bad"],
        27 => vec!["--n=value"],
        28 => vec!["--s"],
        29 => vec!["-cz"],
        30 => vec!["--help"],
        31 => vec!["--version"],
        32 => vec!["--si=3", "--", "a.txt"],
        33 => vec!["-s", "%4", "a.txt"],
        34 => vec!["-s", "/4", "a.txt"],
        35 => vec!["-s", "<3", "a.txt"],
        36 => vec!["-s", ">9", "a.txt"],
        37 => vec!["--=x"],
        38 => vec!["-s", "+9223372036854775807", "a.txt"],
        39 => vec!["-s", "-9223372036854775808", "a.txt"],
        40 => vec!["-r", "b.txt", "-s", "+9223372036854775807", "new"],
        41 => vec!["--no-create", "--size=2", "missing"],
        42 => vec!["--io-blocks", "--size=1", "a.txt"],
        43 => vec!["--reference=b.txt", "a.txt"],
        44 => vec!["-s", "  <  3", "a.txt"],
        45 => vec!["-s", "1KiB", "a.txt"],
        46 => vec!["-cs", "2", "missing", "a.txt"],
        47 => vec!["-s", "2", "quote' space"],
        48 => vec!["-s", "2", "--", "-"],
        49 => vec!["-r", "#can't", "a.txt"],
        50 => vec!["-r", "~can't", "a.txt"],
        51 => vec!["-r", "at@quote'", "a.txt"],
        _ => return None,
    };
    Some(support::case(args, fixture, b""))
}
