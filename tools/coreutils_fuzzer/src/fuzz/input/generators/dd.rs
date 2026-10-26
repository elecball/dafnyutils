use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, ValueContext, ValueSource};
use super::super::{mutations, support, CwdPolicy, PatternInputGenerator};
use crate::fuzz::{FixtureBlueprint, GeneratedCase};
use rand::rngs::StdRng;
use rand::Rng;

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutations::regenerate_argv)
        .with_system_state(empty_state)
        .with_cwd_policy(CwdPolicy::Root)
        .with_candidate_guard(in_scope)
        .with_mutation_guard(in_scope);

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::weighted(
        8,
        &[
            Element::once(Atom::Literal("status=none")),
            Element::optional(55, Atom::Literal("iflag=fullblock")),
            Element::repeated(0, 6, Atom::Value(ValueSource::Generated(operand))),
        ],
    ),
    Alternative::new(&[Element::repeated(
        1,
        3,
        Atom::Value(ValueSource::Values(&[
            "--help",
            "--version",
            "--he",
            "--vers",
            "--help=bad",
            "--version=bad",
            "--he=bad",
            "--vers=bad",
            "-é",
            "--unknown",
            "-b",
            "--h",
            "--v",
        ])),
    )]),
    Alternative::new(&[
        Element::once(Atom::Literal("status=none")),
        Element::once(Atom::Literal("--")),
        Element::once(Atom::Value(ValueSource::Values(&[
            "--help",
            "--version",
            "bad",
            "",
        ]))),
    ]),
]);

fn empty_state(_rng: &mut StdRng, _max_fs_entries: usize) -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![],
        files: vec![],
        symlinks: vec![],
        hardlinks: vec![],
    }
}

fn operand(_context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    const NUMBERS: &[&str] = &[
        "1",
        "2",
        "3",
        "5",
        "7",
        "16",
        "31",
        "64",
        "511",
        "512",
        "513",
        "1024",
        "1c",
        "2w",
        "1b",
        "1K",
        "1kB",
        "2x3",
        "1Bx4",
        "+3",
        " 3",
        "0",
        "bad",
        "-1",
        "1x",
        "B",
        "1KBb",
        "9223372036854775808",
        "9223372036854775808bad",
        "9223372036854775807badx1",
        "0x9223372036854775808bad",
        "1KD",
        "1KDB",
        " K",
        "1cBx2",
    ];
    const CONVERSIONS: &[&str] = &[
        "lcase",
        "ucase",
        "swab",
        "sync",
        "lcase,swab",
        "ucase,swab",
        "lcase,sync",
        "ucase,swab,sync",
        "swab,sync",
        "lcase,lcase",
        "lcase,ucase",
        "",
        "swab,",
        "bad",
    ];
    let index = rng.random_range(0..10);
    match index {
        0..=3 => {
            let name = ["bs", "ibs", "obs", "cbs"][index];
            let number = NUMBERS[rng.random_range(0..NUMBERS.len())];
            format!("{name}={number}")
        }
        4 | 5 => format!(
            "conv={}",
            CONVERSIONS[rng.random_range(0..CONVERSIONS.len())]
        ),
        6 => {
            let values = [
                "0",
                "1",
                "2",
                "3",
                "7B",
                "1Bx2",
                "0x1",
                "00x99999999999999999999999",
                "bad",
            ];
            format!("count={}", values[rng.random_range(0..values.len())])
        }
        7 => {
            let values = [
                "fullblock",
                "count_bytes",
                "fullblock,count_bytes",
                "fullblock,fullblock",
                "bad",
                "",
                "fullblock,",
            ];
            format!("iflag={}", values[rng.random_range(0..values.len())])
        }
        8 => {
            let values = [
                "status=none",
                "status=none,none",
                "status=bad",
                "status=",
                "oflag=fullblock",
                "oflag=bad",
            ];
            values[rng.random_range(0..values.len())].to_owned()
        }
        _ => {
            ["unknown=value", "operand", "conv=swab", "count=0"][rng.random_range(0..4)].to_owned()
        }
    }
}

fn in_scope(argv: &[String]) -> bool {
    argv.iter().any(|arg| arg == "status=none")
        || argv
            .iter()
            .take_while(|arg| arg.as_str() != "--")
            .any(|arg| arg.len() > 1 && arg.starts_with('-'))
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = FixtureBlueprint {
        directories: vec![],
        files: vec![],
        symlinks: vec![],
        hardlinks: vec![],
    };
    Some(match iteration {
        0 => support::case(vec!["status=none"], fixture, &[0, 255, 10, 128, 65, 90]),
        1 => support::case(
            vec!["status=none", "bs=3", "conv=lcase,swab", "iflag=fullblock"],
            fixture,
            b"ABCDE\x00\xffxyZ",
        ),
        2 => support::case(
            vec!["status=none", "ibs=3", "obs=5", "conv=ucase,swab,sync"],
            fixture,
            b"abcDefg",
        ),
        3 => support::case(
            vec![
                "status=none",
                "ibs=3",
                "obs=2",
                "count=7B",
                "iflag=fullblock",
            ],
            fixture,
            b"0123456789",
        ),
        4 => support::case(
            vec![
                "status=none",
                "iflag=count_bytes",
                "count=7",
                "ibs=3",
                "conv=swab",
            ],
            fixture,
            b"0123456789",
        ),
        5 => support::case(
            vec!["status=none", "count=0"],
            fixture,
            b"must remain unread",
        ),
        6 => support::case(vec!["status=none", "bs=0"], fixture, b""),
        7 => support::case(vec!["status=none", "conv=lcase,ucase"], fixture, b""),
        8 => support::case(vec!["status=none", "conv=swab,"], fixture, b""),
        9 => support::case(vec!["status=none", "count=0x1"], fixture, b""),
        10 => support::case(vec!["count=bad", "--help"], fixture, b""),
        11 => support::case(vec!["--version", "--bad"], fixture, b""),
        12 => support::case(vec!["status=none", "--", "--help"], fixture, b""),
        13 => support::case(
            vec!["status=none", "bs=3", "ibs=1", "obs=1", "conv=sync"],
            fixture,
            b"xy",
        ),
        14 => support::case(
            vec!["status=none", "ibs=1", "obs=7", "conv=swab"],
            fixture,
            &[0, 1, 2, 3, 255],
        ),
        15 => support::case(
            vec!["status=none", "count=9223372036854775808bad"],
            fixture,
            b"",
        ),
        16 => support::case(
            vec!["status=none", "count=0x9223372036854775808bad"],
            fixture,
            b"must remain unread",
        ),
        _ => return None,
    })
}
