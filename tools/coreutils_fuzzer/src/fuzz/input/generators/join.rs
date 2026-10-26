use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueSource,
};
use super::super::{mutations, support, CwdPolicy, PatternInputGenerator};
use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, GeneratedCase, SymlinkSpec};
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

const ORDER: Element = Element::optional(
    45,
    Atom::Option(OptionChoice::available(&[
        "--check-order",
        "--nocheck-order",
    ])),
);
const IGNORE_CASE: Element = Element::optional(
    30,
    Atom::Option(OptionChoice::available(&["-i", "--ignore-case"])),
);
const HEADER: Element = Element::optional(25, Atom::Option(OptionChoice::available(&["--header"])));
const ZERO: Element = Element::optional(
    30,
    Atom::Option(OptionChoice::available(&["-z", "--zero-terminated"])),
);
const UNPAIRED: Element = Element::repeated(
    0,
    3,
    Atom::OptionValue(OptionValue::new(
        &[
            OptionValueForm::separate("-a"),
            OptionValueForm::separate("-v"),
        ],
        ValueSource::Values(&["1", "2"]),
    )),
);
const FIELD: Element = Element::optional(
    45,
    Atom::OptionValue(OptionValue::new(
        &[
            OptionValueForm::separate("-1"),
            OptionValueForm::separate("-2"),
            OptionValueForm::separate("-j"),
        ],
        ValueSource::Values(&["1", "2", "3", "+1", " 2", "9223372036854775808"]),
    )),
);
const SEPARATOR: Element = Element::optional(
    40,
    Atom::OptionValue(OptionValue::new(
        &[OptionValueForm::separate("-t")],
        ValueSource::Values(&[":", ",", "", "\\0", "\t", "\n"]),
    )),
);
const FILLER: Element = Element::optional(
    35,
    Atom::OptionValue(OptionValue::new(
        &[OptionValueForm::separate("-e")],
        ValueSource::Values(&["", ".", "-", "missing", "x:y"]),
    )),
);
const FORMAT: Element = Element::optional(
    35,
    Atom::OptionValue(OptionValue::new(
        &[OptionValueForm::separate("-o")],
        ValueSource::Values(&["auto", "0", "0,1.2,2.2", "2.3 1.1", "1.1,2.9", "2.1,0,1.2"]),
    )),
);
const STREAM: Atom = Atom::Operand(OperandSource::Stream {
    existing_weight: 7,
    missing_weight: 1,
    stdin_weight: 2,
    allow_repeated_stdin: true,
});
const TWO_STREAMS: Element = Element::repeated(2, 2, STREAM);

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::weighted(
        75,
        &[
            ORDER,
            IGNORE_CASE,
            HEADER,
            ZERO,
            UNPAIRED,
            FIELD,
            SEPARATOR,
            FILLER,
            FORMAT,
            TWO_STREAMS,
        ],
    ),
    Alternative::weighted(10, &[Element::repeated(0, 3, STREAM)]),
    Alternative::weighted(
        10,
        &[
            Element::once(Atom::OptionValue(OptionValue::new(
                &[
                    OptionValueForm::separate("-j"),
                    OptionValueForm::separate("-a"),
                ],
                ValueSource::Values(&["0", "-1", "x", "", "1x", "-9223372036854775808"]),
            ))),
            TWO_STREAMS,
        ],
    ),
    Alternative::weighted(
        5,
        &[
            Element::once(Atom::OptionValue(OptionValue::new(
                &[OptionValueForm::separate("-o")],
                ValueSource::Values(&["3.1", "1.0", "0.1", "1.2,,2.1", ""]),
            ))),
            TWO_STREAMS,
        ],
    ),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_system_state(random_system_state)
        .with_case_normalizer(normalize_stdin)
        .with_mutator(mutations::regenerate_argv)
        .with_cwd_policy(CwdPolicy::Root);

fn fixture(left: &[u8], right: &[u8]) -> FixtureBlueprint {
    FixtureBlueprint {
        directories: vec![DirSpec {
            relative_path: PathBuf::from("dir"),
            mode: 0o755,
        }],
        files: vec![
            FileSpec {
                relative_path: PathBuf::from("left"),
                bytes: left.to_vec(),
                mode: 0o644,
            },
            FileSpec {
                relative_path: PathBuf::from("right"),
                bytes: right.to_vec(),
                mode: 0o644,
            },
        ],
        symlinks: Vec::new(),
        hardlinks: Vec::new(),
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let base = fixture(b"a 1\na 2\nb 3\n", b"a X\na Y\nc Z\n");
    Some(match iteration {
        0 => support::case(vec!["left", "right"], base, b""),
        1 => support::case(vec!["-a1", "-a2", "left", "right"], base, b""),
        2 => support::case(vec!["-v2", "left", "right"], base, b""),
        3 => support::case(
            vec!["-o", "0,1.2,2.2", "-e", ".", "-a1", "-a2", "left", "right"],
            base,
            b"",
        ),
        4 => support::case(
            vec!["--check-order", "left", "right"],
            fixture(b"b 1\na 2\n", b"b X\na Y\n"),
            b"",
        ),
        5 => support::case(vec!["left", "right"], fixture(b"a\nx\no", b"b\ny\np"), b""),
        6 => support::case(
            vec!["--nocheck-order", "left", "right"],
            fixture(b"b 1\na 2\n", b"b X\na Y\n"),
            b"",
        ),
        7 => support::case(
            vec!["--header", "--check-order", "left", "right"],
            fixture(b"ID Name\n2 B\n1 A\n", b"ID Color\n2 blue\n"),
            b"",
        ),
        8 => support::case(
            vec![
                "-t:", "-a1", "-a2", "-o", "auto", "-e", ".", "left", "right",
            ],
            fixture(b"a:1::2\nb:1\n", b"a:3:4\nc:5:6\n"),
            b"",
        ),
        9 => support::case(
            vec!["-z", "-a1", "-a2", "left", "right"],
            fixture(b"a\n\n1\0c 3\0", b"a 2\0b\n8\0c 9\0"),
            b"",
        ),
        10 => support::case(
            vec!["-t", "\\0", "left", "right"],
            fixture(b"a\0L\n", b"a\0R\n"),
            b"",
        ),
        11 => support::case(
            vec!["-t", "", "left", "right"],
            fixture(b"a 1\nb 1\n", b"a 1\nb 2\n"),
            b"",
        ),
        12 => support::case(
            vec!["-i", "left", "right"],
            fixture(b"A 1\na 2\nB 3\n", b"a X\nB Y\n"),
            b"",
        ),
        13 => support::case(vec!["-j1", "2", "left", "right"], base, b""),
        14 => support::case(vec!["-o", "0", "1.2", "2.2", "left", "right"], base, b""),
        15 => support::case(vec!["-", "right"], base, b"a 1\na 2\nb 3\n"),
        16 => support::case(vec!["left", "missing"], base, b""),
        17 => support::case(vec!["dir", "right"], base, b""),
        18 => support::case(
            vec!["-1", "99999999999999999999999", "-2", "2", "left", "right"],
            base,
            b"",
        ),
        19 => support::case(
            vec!["--check-order", "left", "right"],
            fixture(b"b x\na\0hidden\n", b"b Y\n"),
            b"",
        ),
        20 => support::case(vec!["--help"], base, b""),
        21 => support::case(vec!["--version"], base, b""),
        22 => support::case(vec!["-", "-"], base, b"a\n"),
        23 => support::case(vec!["-a", "3", "--help"], base, b""),
        _ => return None,
    })
}

fn random_rows(rng: &mut StdRng, separator: u8, terminator: u8) -> Vec<u8> {
    let mut keys: Vec<u8> = (0..rng.random_range(0..=9))
        .map(|_| rng.random_range(b'a'..=b'd'))
        .collect();
    keys.sort_unstable();
    if rng.random_bool(0.25) {
        keys.reverse();
    }
    let mut bytes = Vec::new();
    for key in keys {
        if separator == b' ' && rng.random_bool(0.3) {
            bytes.extend_from_slice(b" \t");
        }
        bytes.push(if rng.random_bool(0.1) {
            key.to_ascii_uppercase()
        } else {
            key
        });
        for _ in 0..rng.random_range(0..=3) {
            bytes.push(separator);
            if rng.random_bool(0.7) {
                bytes.push(rng.random_range(b'0'..=b'9'));
                if rng.random_bool(0.15) {
                    bytes.push(0xff);
                }
            }
        }
        if rng.random_bool(0.1) {
            bytes.extend_from_slice(b"\nembedded");
        }
        bytes.push(terminator);
    }
    if rng.random_bool(0.25) && !bytes.is_empty() {
        bytes.pop();
    }
    bytes
}

fn random_system_state(rng: &mut StdRng, _max_fs_entries: usize) -> FixtureBlueprint {
    let left = random_rows(rng, b' ', b'\n');
    let right = random_rows(rng, b' ', b'\n');
    let mut state = fixture(&left, &right);
    for (name, separator, terminator) in [
        ("colon-left", b':', b'\n'),
        ("colon-right", b':', b'\n'),
        ("nul-left", 0, b'\n'),
        ("nul-right", 0, b'\n'),
        ("zero-left", b' ', 0),
        ("zero-right", b' ', 0),
    ] {
        state.files.push(FileSpec {
            relative_path: PathBuf::from(name),
            bytes: random_rows(rng, separator, terminator),
            mode: 0o644,
        });
    }
    state.files.push(FileSpec {
        relative_path: PathBuf::from("blank name"),
        bytes: b"a 1\na 2\n".to_vec(),
        mode: 0o644,
    });
    state.symlinks.push(SymlinkSpec {
        relative_path: PathBuf::from("a:b"),
        target: PathBuf::from("left"),
    });
    state.files.push(FileSpec {
        relative_path: PathBuf::from("unreadable"),
        bytes: b"a private\n".to_vec(),
        mode: 0,
    });
    state
}

fn normalize_stdin(case: &mut GeneratedCase) {
    if case.argv.iter().any(|arg| arg == "-") && case.stdin.is_empty() {
        if let Some(file) = case.fixture.files.first() {
            case.stdin = file.bytes.clone();
        }
    }
}
