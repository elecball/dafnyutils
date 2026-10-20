use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice};
use super::super::PatternInputGenerator;
use super::super::{support, system_state};
use crate::fuzz::{DirSpec, FileSpec, GeneratedCase, SymlinkSpec};
use std::path::PathBuf;

const OPTION: Atom = Atom::Option(OptionChoice::available(&[
    "-p",
    "--parents",
    "--path",
    "-v",
    "--verbose",
    "--ignore-fail-on-non-empty",
    "--help",
    "--version",
]));
const TARGET: Atom = Atom::Operand(OperandSource::Target {
    existing_percent: 80,
});
static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::new(&[
        Element::repeated(0, 3, OPTION),
        Element::up_to_budget(0, TARGET),
    ]),
    Alternative::new(&[
        Element::once(TARGET),
        Element::repeated(0, 2, OPTION),
        Element::up_to_budget(0, TARGET),
    ]),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case);

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let mut fixture = system_state::basic_fixture();
    for path in ["empty", "chain", "chain/leaf", "nonempty", "nonempty/child"] {
        fixture.directories.push(DirSpec {
            relative_path: PathBuf::from(path),
            mode: 0o755,
        });
    }
    fixture.symlinks.push(SymlinkSpec {
        relative_path: PathBuf::from("empty-link"),
        target: PathBuf::from("empty"),
    });
    fixture.symlinks.push(SymlinkSpec {
        relative_path: PathBuf::from("missing-link"),
        target: PathBuf::from("missing"),
    });
    let args = match iteration {
        0 => vec!["empty"],
        1 => vec!["-pv", "chain/leaf///"],
        2 => vec!["-pv", "--ignore-fail-on-non-empty", "nonempty/child"],
        3 => vec!["nonempty"],
        4 => vec!["--ignore-fail-on-non-empty", "nonempty"],
        5 => vec!["-v", "missing", "empty"],
        6 => vec!["empty-link/"],
        7 => vec!["missing-link/"],
        8 => vec!["a-link/"],
        9 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("empty/child"),
                mode: 0o755,
            });
            vec!["-p", "empty-link/child"]
        }
        10 => vec!["-pv", "chain", "chain/leaf"],
        11 => vec!["-pv", "chain//leaf///"],
        12 => vec!["--path", "chain/leaf"],
        13 => vec!["--pa", "chain/leaf"],
        14 => vec!["--p", "chain/leaf"],
        15 => vec!["--pat", "chain/leaf"],
        16 => vec!["--v"],
        17 => vec!["-pvx"],
        18 => vec!["--p=1"],
        19 => vec!["--help", "--bad"],
        20 => vec!["--bad", "--help"],
        21 => vec!["--version", "--help"],
        22 => vec!["--help", "--version"],
        23 => vec![],
        24 => vec!["-v", ""],
        25 => vec!["-v", "."],
        26 => vec!["-v", ".."],
        27 => vec!["a.txt/"],
        28 => vec!["a.txt/child"],
        29 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("--help"),
                mode: 0o755,
            });
            vec!["--", "--help"]
        }
        30 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("blocked"),
                mode: 0o555,
            });
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("blocked/empty"),
                mode: 0o755,
            });
            vec!["--ignore-fail-on-non-empty", "blocked/empty"]
        }
        31 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("blocked"),
                mode: 0o555,
            });
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("blocked/nonempty"),
                mode: 0o755,
            });
            fixture.files.push(FileSpec {
                relative_path: PathBuf::from("blocked/nonempty/keep"),
                bytes: b"keep\n".to_vec(),
                mode: 0o644,
            });
            vec!["--ignore-fail-on-non-empty", "blocked/nonempty"]
        }
        32 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("blocked"),
                mode: 0o555,
            });
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("blocked/unreadable"),
                mode: 0o111,
            });
            vec!["--ignore-fail-on-non-empty", "blocked/unreadable"]
        }
        _ => return None,
    };
    Some(support::case(args, fixture, b""))
}
