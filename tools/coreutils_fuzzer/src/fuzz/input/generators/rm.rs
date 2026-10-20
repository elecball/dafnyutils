use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueSource,
};
use super::super::{mutations, support, system_state, CwdPolicy, PatternInputGenerator};
use crate::fuzz::{DirSpec, FileSpec, FixtureBlueprint, GeneratedCase, HardlinkSpec, SymlinkSpec};
use rand::rngs::StdRng;
use std::path::PathBuf;

const FLAGS: Atom = Atom::Option(OptionChoice::available(&[
    "-f",
    "--force",
    "-v",
    "--verbose",
    "-d",
    "--dir",
    "-r",
    "-R",
    "--recursive",
    "--one-file-system",
    "--no-preserve-root",
    "--preserve-root",
    "--help",
    "--version",
]));
const NONRECURSIVE_FLAGS: Atom = Atom::Option(OptionChoice::available(&[
    "-f",
    "--force",
    "-v",
    "--verbose",
    "-d",
    "--dir",
    "--one-file-system",
    "--no-preserve-root",
    "--preserve-root",
    "--help",
    "--version",
]));
const TARGET: Atom = Atom::Operand(OperandSource::Target {
    existing_percent: 80,
});
static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::requiring(
        2,
        &["-I"],
        &[
            Element::once(Atom::Literal("-I")),
            Element::repeated(0, 3, NONRECURSIVE_FLAGS),
            Element::repeated(0, 3, TARGET),
        ],
    ),
    Alternative::new(&[
        Element::repeated(0, 4, FLAGS),
        Element::repeated(0, 4, TARGET),
    ]),
    Alternative::requiring(
        2,
        &["--interactive"],
        &[
            Element::once(Atom::OptionValue(OptionValue::new(
                &[OptionValueForm::equals("--interactive")],
                ValueSource::Values(&["never", "no", "none", "n"]),
            ))),
            Element::repeated(0, 3, FLAGS),
            Element::repeated(0, 3, TARGET),
        ],
    ),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_mutator(mutations::regenerate_argv)
        .with_system_state(bounded_system_state)
        .with_cwd_policy(CwdPolicy::Root);

fn bounded_system_state(rng: &mut StdRng, max_fs_entries: usize) -> FixtureBlueprint {
    let mut fixture = system_state::random_system_state(rng, max_fs_entries.min(12));
    for file in &mut fixture.files {
        file.bytes.truncate(128);
    }
    fixture
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let mut fixture = system_state::failure_fixture();
    let argv = match iteration {
        0 => vec!["-v", "a.txt"],
        1 => vec!["-f", "missing"],
        2 => vec!["-f", "a.txt/child"],
        3 => vec!["-d", "-v", "dir", "b.txt"],
        4 => vec!["-d", "occupied"],
        5 => vec!["-rv", "occupied"],
        6 => vec!["-rv", "dir-link"],
        7 => vec!["-r", "dir-link/"],
        8 => vec!["-v", "dangling"],
        9 => vec!["a.txt", "missing", "b.txt"],
        10 => vec!["-r", ""],
        11 => vec!["-rv", "occupied////"],
        12 => vec!["-r", "."],
        13 => vec!["-r", "occupied/.."],
        14 => vec![],
        15 => vec!["-f"],
        16 => vec!["--interactive=never", "missing"],
        17 => vec!["-f", "--interactive=never", "missing"],
        18 => vec!["--preserve-root=all", "-r", "occupied"],
        19 => vec!["--one-file-system", "-r", "occupied"],
        20 => vec!["--no-preserve-ro", "a.txt"],
        21 => vec!["--preserve-root=no", "a.txt"],
        22 => vec!["--interactive=invalid", "a.txt"],
        23 => vec!["--help", "--bad"],
        24 => vec!["--version", "--help"],
        25 => vec!["--bad", "--help"],
        26 => vec!["--v"],
        27 => vec!["--verbose=value"],
        28 => {
            fixture.hardlinks.push(HardlinkSpec {
                relative_path: PathBuf::from("alias"),
                source_relative_path: PathBuf::from("a.txt"),
            });
            vec!["-v", "alias"]
        }
        29 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("blocked"),
                mode: 0o555,
            });
            fixture.files.push(FileSpec {
                relative_path: PathBuf::from("blocked/keep"),
                bytes: b"keep".to_vec(),
                mode: 0o644,
            });
            vec!["-rf", "blocked", "a.txt"]
        }
        30 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("unreadable"),
                mode: 0o000,
            });
            vec!["-rf", "unreadable"]
        }
        31 => {
            fixture.files.push(FileSpec {
                relative_path: PathBuf::from("--help"),
                bytes: b"remove".to_vec(),
                mode: 0o644,
            });
            vec!["-v", "--", "--help"]
        }
        32 => {
            fixture.symlinks.push(SymlinkSpec {
                relative_path: PathBuf::from("occupied/link"),
                target: PathBuf::from("../a.txt"),
            });
            vec!["-rv", "occupied"]
        }
        33 => vec!["-I", "a.txt"],
        34 => vec!["--interactive=once", "a.txt", "b.txt", "target.txt"],
        35 => vec!["-fz"],
        36 => vec!["-rfz"],
        37 => vec!["-f=1"],
        38 => vec!["-fé"],
        39 => vec!["-f--"],
        40 => vec!["---p=1"],
        41 => vec!["--interactive="],
        42 => vec!["--=value"],
        43 => vec!["--interactive"],
        44 => vec!["-I", "-r"],
        45 => {
            let name = "n".repeat(256);
            return Some(support::case(vec!["-f", &name], fixture, b""));
        }
        _ => return None,
    };
    Some(support::case(argv, fixture, b""))
}
