use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueContext, ValueSource,
};
use super::super::{support, system_state, CwdPolicy, PatternInputGenerator};
use crate::fuzz::{DirSpec, FileSpec, GeneratedCase, HardlinkSpec, SymlinkSpec, UtilityProfile};
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

const SOURCE: Atom = Atom::Operand(OperandSource::Generated(source));
const TARGET: Atom = Atom::Operand(OperandSource::Generated(target));
const POLICY: Atom = Atom::Option(OptionChoice::available(&[
    "-f",
    "-n",
    "-v",
    "-R",
    "-L",
    "-P",
    "--remove-destination",
    "--attributes-only",
    "--force",
    "--no-clobber",
    "--verbose",
    "--recursive",
    "-r",
    "--dereference",
    "--no-dereference",
    "-H",
    "-x",
    "--one-file-system",
    "--keep-directory-symlink",
    "--copy-contents",
    "--strip-trailing-slashes",
    "-T",
    "--no-target-directory",
    "-u",
]));

// GNU's -f link replacement requires a random temporary-name observation that
// this IO model lacks. Ordinary links remain fully generated without -f.
const LINK_POLICY: Atom = Atom::Option(OptionChoice::available(&[
    "-n",
    "-v",
    "-R",
    "-r",
    "-L",
    "-H",
    "-P",
    "-x",
    "-T",
    "--no-clobber",
    "--verbose",
    "--recursive",
    "--dereference",
    "--no-dereference",
    "--remove-destination",
    "--attributes-only",
    "--one-file-system",
    "--keep-directory-symlink",
    "--strip-trailing-slashes",
]));
const FRESH_TARGET: Atom = Atom::Operand(OperandSource::Generated(fresh_target));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::weighted(
        8,
        &[
            Element::repeated(0, 3, POLICY),
            Element::once(SOURCE),
            Element::once(TARGET),
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::once(Atom::Option(OptionChoice::available(&["-l", "-s"]))),
            Element::optional(30, LINK_POLICY),
            Element::once(SOURCE),
            Element::once(TARGET),
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::once(Atom::Literal("-t")),
            Element::once(Atom::Operand(OperandSource::Generated(directory))),
            Element::repeated(1, 3, SOURCE),
        ],
    ),
    Alternative::weighted(
        3,
        &[
            Element::optional(50, POLICY),
            Element::once(Atom::OptionValue(OptionValue::new(
                &[OptionValueForm::equals("--preserve")],
                ValueSource::Values(&["mode", "timestamps", "mode,timestamps", "t,m", "bad", ""]),
            ))),
            Element::once(SOURCE),
            Element::once(TARGET),
        ],
    ),
    Alternative::weighted(
        3,
        &[
            Element::optional(50, POLICY),
            Element::once(Atom::OptionValue(OptionValue::new(
                &[OptionValueForm::equals("--update")],
                ValueSource::Values(&["all", "older", "none", "none-fail", "bad"]),
            ))),
            Element::once(SOURCE),
            Element::once(TARGET),
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::once(Atom::Literal("--parents")),
            Element::optional(50, POLICY),
            Element::once(SOURCE),
            Element::once(Atom::Operand(OperandSource::Generated(directory))),
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::optional(50, POLICY),
            Element::once(Atom::OptionValue(OptionValue::new(
                &[OptionValueForm::equals("--backup")],
                ValueSource::Values(&[
                    "simple", "numbered", "existing", "none", "t", "nil", "never", "n", "bad",
                ]),
            ))),
            Element::once(SOURCE),
            Element::once(TARGET),
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::optional(50, POLICY),
            Element::once(Atom::OptionValue(OptionValue::new(
                &[
                    OptionValueForm::equals("--suffix"),
                    OptionValueForm::separate("-S"),
                ],
                ValueSource::Values(&["~", ".save", "", "bad/path"]),
            ))),
            Element::once(SOURCE),
            Element::once(TARGET),
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::once(Atom::Option(OptionChoice::available(&["-d"]))),
            Element::optional(40, POLICY),
            Element::once(SOURCE),
            Element::once(FRESH_TARGET),
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::once(Atom::OptionValue(OptionValue::new(
                &[OptionValueForm::equals("--preserve")],
                ValueSource::Values(&["links", "links,mode,timestamps", "t,m,l"]),
            ))),
            Element::optional(40, POLICY),
            Element::once(SOURCE),
            Element::once(FRESH_TARGET),
        ],
    ),
    Alternative::weighted(
        1,
        &[
            Element::once(Atom::OptionValue(OptionValue::new(
                &[OptionValueForm::equals("--no-preserve")],
                ValueSource::Values(&[
                    "mode",
                    "timestamps",
                    "links",
                    "all",
                    "ownership,xattr,context",
                    "t,m",
                ]),
            ))),
            Element::optional(50, POLICY),
            Element::once(SOURCE),
            Element::once(TARGET),
        ],
    ),
    Alternative::weighted(1, &[Element::repeated(0, 1, SOURCE)]),
    Alternative::weighted(
        1,
        &[Element::once(Atom::Option(OptionChoice::available(&[
            "--help",
            "--version",
        ])))],
    ),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_cwd_policy(CwdPolicy::Root)
        .with_profile(UtilityProfile {
            requires_path_operand: true,
            prefers_existing_paths: true,
        });

fn source(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let paths = context.fixture().existing_operands();
    support::pick_file_or_missing(&paths, rng)
}

fn target(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let paths = context.fixture().existing_operands();
    if !paths.is_empty() && rng.random_bool(0.5) {
        return support::pick_string(&paths, rng);
    }
    if rng.random_bool(0.2) {
        format!("missing-parent/copy-{}", rng.random_range(0..100))
    } else {
        format!("copy-{}", rng.random_range(0..100))
    }
}

// A fresh destination covers preservation of source aliases without GNU's
// random atomic replacement protocol for an already-existing subsequent alias.
fn fresh_target(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let paths = context.fixture().existing_operands();
    let mut index = rng.random_range(0..100);
    loop {
        let candidate = format!("preserved-copy-{index}");
        if !paths.iter().any(|path| path == &candidate) {
            return candidate;
        }
        index += 1;
    }
}

fn directory(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let directories: Vec<_> = context
        .fixture()
        .directories
        .iter()
        .map(|entry| entry.relative_path.to_string_lossy().into_owned())
        .collect();
    if directories.is_empty() {
        ".".to_owned()
    } else {
        support::pick_string(&directories, rng)
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let mut fixture = system_state::failure_fixture();
    fixture.files.extend([
        FileSpec {
            relative_path: PathBuf::from("dir/nested"),
            bytes: b"nested\0\xff\n".to_vec(),
            mode: 0o640,
        },
        FileSpec {
            relative_path: PathBuf::from("read-only"),
            bytes: b"keep unless forced\n".to_vec(),
            mode: 0o444,
        },
    ]);
    fixture.hardlinks.push(HardlinkSpec {
        relative_path: PathBuf::from("alias"),
        source_relative_path: PathBuf::from("a.txt"),
    });
    let args = match iteration {
        0 => vec!["a.txt", "copied"],
        1 => vec!["a.txt", "target.txt"],
        2 => vec!["a.txt", "alias"],
        3 => vec!["-n", "a.txt", "alias"],
        4 => vec!["-f", "a.txt", "read-only"],
        5 => vec!["a-link", "copied"],
        6 => vec!["-P", "a-link", "copied"],
        7 => vec!["a.txt", "a-link"],
        8 => vec!["a.txt", "dangling"],
        9 => vec!["--remove-destination", "a.txt", "dangling"],
        10 => vec!["--attributes-only", "a.txt", "target.txt"],
        11 => vec!["--preserve=mode", "a.txt", "target.txt"],
        12 => vec!["--preserve=timestamps", "a.txt", "copied"],
        13 => vec!["-R", "dir", "copy-dir"],
        14 => vec!["-Rv", "dir", "copy-dir"],
        15 => vec!["-R", "dir", "dir/inside"],
        16 => vec!["-l", "a-link", "hard-copy"],
        17 => vec!["-s", "a.txt", "symbolic-copy"],
        18 => vec!["-t", "dir", "a.txt", "b.txt"],
        19 => vec!["a.txt", "a.txt", "dir"],
        20 => vec!["missing", "b.txt", "dir"],
        21 => vec!["--help", "--bad"],
        22 => vec!["--version", "--help"],
        23 => vec!["--help=bad"],
        24 => vec!["-T", "a.txt", "b.txt", "dir"],
        25 => vec!["-t", "missing", "a.txt"],
        26 => vec!["a.txt", "missing-parent/out"],
        27 => {
            fixture.symlinks.push(SymlinkSpec {
                relative_path: PathBuf::from("dir/cycle"),
                target: PathBuf::from("."),
            });
            vec!["-RL", "dir", "copy-dir"]
        }
        28 => {
            fixture.directories.push(DirSpec {
                relative_path: PathBuf::from("unreadable"),
                mode: 0o000,
            });
            vec!["-R", "unreadable", "copy-dir"]
        }
        29 => vec!["--remove-destination", "a.txt", "alias"],
        30 => vec!["-l", "a.txt", "alias"],
        31 => vec!["missing", "missing", "dir"],
        32 => vec!["-R", "dir", "dir/nested"],
        33 => vec!["a.txt", "copied"],
        34 => vec!["--parents", "dir/nested", "occupied"],
        35 => vec!["-d", "a.txt", "alias", "occupied"],
        36 => vec!["--backup", "a.txt", "target.txt"],
        37 => {
            fixture.files.extend([
                FileSpec {
                    relative_path: PathBuf::from("target.txt.~3~"),
                    bytes: b"3".to_vec(),
                    mode: 0o600,
                },
                FileSpec {
                    relative_path: PathBuf::from("target.txt.~7~"),
                    bytes: b"7".to_vec(),
                    mode: 0o600,
                },
            ]);
            vec!["--backup=existing", "a.txt", "target.txt"]
        }
        38 => vec!["-vb", "a.txt", "target.txt"],
        39 => vec!["--update", "a.txt", "target.txt"],
        40 => vec!["--no-preserve=all", "a.txt", "copied"],
        41 => {
            fixture.hardlinks.push(HardlinkSpec {
                relative_path: PathBuf::from("dir/alias"),
                source_relative_path: PathBuf::from("a.txt"),
            });
            fixture.hardlinks.push(HardlinkSpec {
                relative_path: PathBuf::from("dir/alias2"),
                source_relative_path: PathBuf::from("a.txt"),
            });
            vec!["-Rd", "dir", "copy-dir"]
        }
        _ => return None,
    };
    let mut case = support::case(args, fixture, b"");
    if iteration == 33 || iteration == 38 {
        case.file_size_limit = Some(2);
    }
    Some(case)
}
