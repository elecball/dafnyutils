use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, OptionValue,
    OptionValueForm, ValueContext, ValueSource,
};
use super::super::{support, system_state, PatternInputGenerator};
use crate::fuzz::{
    DirSpec, FileSpec, FixtureBlueprint, GeneratedCase, SymlinkSpec, UtilityProfile,
};
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

const MODE: Atom = Atom::Option(OptionChoice::available(&[
    "-E",
    "-e",
    "-m",
    "-L",
    "-P",
    "-s",
    "-q",
    "-z",
    "--canonicalize",
    "--canonicalize-existing",
    "--canonicalize-missing",
    "--logical",
    "--physical",
    "--strip",
    "--no-symlinks",
    "--quiet",
    "--zero",
]));
const PATH: Atom = Atom::Operand(OperandSource::Generated(path_operand));
const TO: Atom = Atom::OptionValue(OptionValue::new(
    &[
        OptionValueForm::separate("--relative-to"),
        OptionValueForm::equals("--relative-to"),
    ],
    ValueSource::Generated(path_operand),
));
const BASE: Atom = Atom::OptionValue(OptionValue::new(
    &[
        OptionValueForm::separate("--relative-base"),
        OptionValueForm::equals("--relative-base"),
    ],
    ValueSource::Generated(path_operand),
));
const INFO: Atom = Atom::Option(OptionChoice::available(&["--help", "--version"]));
const MALFORMED: Atom = Atom::Value(ValueSource::Values(&[
    "--not-realpath",
    "-J",
    "-smJ",
    "--zero=value",
    "--help=value",
    "--relative-to",
    "--relative-base",
    "--c",
    "--canonicalize-",
    "--r",
    "--=x",
    "-é",
]));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::weighted(
        8,
        &[
            Element::repeated(0, 6, MODE),
            Element::optional(35, TO),
            Element::optional(30, BASE),
            Element::up_to_budget(0, PATH),
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::optional(60, PATH),
            Element::repeated(1, 2, INFO),
            Element::optional(30, MALFORMED),
            Element::optional(60, PATH),
        ],
    ),
    Alternative::weighted(2, &[Element::once(MALFORMED)]),
    Alternative::weighted(
        2,
        &[
            Element::repeated(0, 4, MODE),
            Element::once(PATH),
            Element::repeated(1, 3, MODE),
            Element::optional(60, PATH),
        ],
    ),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_system_state(random_fixture)
        .with_profile(UtilityProfile {
            requires_path_operand: true,
            prefers_existing_paths: false,
        });

fn path_operand(context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    let fixed = [
        "",
        ".",
        "..",
        "../..",
        "././",
        "/",
        "//",
        "///",
        "missing",
        "missing/child",
        "missing/../absent",
        "missing/",
        "__rp-file/child",
        "__rp-file/./../missing",
        "__rp-file/.//",
        "__rp-file/./.",
        "__rp-dir/child/..",
        "__rp-dir//./child///",
        "__rp-link/..",
        "__rp-link/",
        "__rp-dangling",
        "__rp-loop",
        "__rp-cycle-a",
        "__rp-cycle-a/child",
        "__rp-dot/__rp-file",
        "__rp-link/../child",
        "__rp-blocked/child",
        "__rp-blocked/./../missing",
        "quoted ' missing",
        "a:b",
        "nonascii-한글",
    ];
    if rng.random_bool(0.65) {
        return fixed[rng.random_range(0..fixed.len())].to_string();
    }
    let paths = context.fixture().existing_operands();
    let path = support::pick_string(&paths, rng);
    match rng.random_range(0..6) {
        0 => format!("./{path}"),
        1 => format!("{path}/.."),
        2 => format!("{path}/./../missing"),
        3 => format!("{path}///"),
        _ => path,
    }
}

fn add_path_scenarios(mut fixture: FixtureBlueprint) -> FixtureBlueprint {
    fixture.directories.extend([
        DirSpec {
            relative_path: PathBuf::from("__rp-dir"),
            mode: 0o755,
        },
        DirSpec {
            relative_path: PathBuf::from("__rp-dir/child"),
            mode: 0o755,
        },
        DirSpec {
            relative_path: PathBuf::from("__rp-blocked"),
            mode: 0o000,
        },
    ]);
    fixture.files.push(FileSpec {
        relative_path: PathBuf::from("__rp-file"),
        bytes: b"file\n".to_vec(),
        mode: 0o644,
    });
    for (name, target) in [
        ("__rp-link", "__rp-dir/child"),
        ("__rp-dangling", "missing"),
        ("__rp-loop", "__rp-loop"),
        ("__rp-cycle-a", "__rp-cycle-b"),
        ("__rp-cycle-b", "__rp-cycle-c"),
        ("__rp-cycle-c", "__rp-cycle-a"),
        ("__rp-dot", "."),
    ] {
        fixture.symlinks.push(SymlinkSpec {
            relative_path: PathBuf::from(name),
            target: PathBuf::from(target),
        });
    }
    fixture
}

fn random_fixture(rng: &mut StdRng, max_entries: usize) -> FixtureBlueprint {
    add_path_scenarios(system_state::random_system_state(rng, max_entries))
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let mut fixture = add_path_scenarios(system_state::basic_fixture());
    if iteration == 31 {
        // One finite 48-link chain distinguishes user-space traversal from stat.
        for index in 0..48 {
            fixture.symlinks.push(SymlinkSpec {
                relative_path: PathBuf::from(format!("__rp-chain-{index:02}")),
                target: PathBuf::from(if index == 47 {
                    "__rp-file".to_string()
                } else {
                    format!("__rp-chain-{:02}", index + 1)
                }),
            });
        }
        return Some(support::case(vec!["-eP", "__rp-chain-00"], fixture, b""));
    }
    if iteration == 32 {
        // Repeated links with different remaining suffixes are not a cycle.
        let operand = "__rp-dot/".repeat(48) + "__rp-file";
        return Some(support::case(vec!["-eP", &operand], fixture, b""));
    }
    let argv = match iteration {
        0 => vec!["-ms", "a/../b//./c/", ""],
        1 => vec!["-s", "__rp-link/.."],
        2 => vec!["-s", "-ms", "__rp-link/.."],
        3 => vec!["-s", "__rp-link"],
        4 => vec!["-m", "missing/child", "__rp-file/child"],
        5 => vec!["-e", "missing", "__rp-file"],
        6 => vec!["-E", "missing/"],
        7 => vec!["-s", "__rp-file/./../missing"],
        8 => vec!["-P", "__rp-file/./../missing"],
        9 => vec!["-msz", ".", "a/../b", "/"],
        10 => vec!["-q", "", "__rp-file"],
        11 => vec!["-m", "__rp-cycle-a"],
        12 => vec!["-e", "__rp-cycle-a"],
        13 => vec!["-m", "__rp-loop/child"],
        14 => vec!["-ms", "--relative-to=prefix", "prefixed/1"],
        15 => vec!["-ms", "--relative-to=prefixed", "prefix/1"],
        16 => vec![
            "-ms",
            "--relative-to=/",
            "--relative-base=/",
            "/",
            "//",
            "/usr",
        ],
        17 => vec![
            "-ms",
            "--relative-base=/usr",
            "--relative-to=/usr",
            "/tmp",
            "/usr",
        ],
        18 => vec![
            "-ms",
            "--relative-base=/usr/local",
            "--relative-to=/usr",
            "/usr",
            "/usr/local",
        ],
        19 => vec!["-e", "--relative-to=__rp-file", "."],
        20 => vec!["-eE", "--relative-to=__rp-file", "."],
        21 => vec!["-q", "--relative-base=", "."],
        22 => vec!["--help", "--not-realpath"],
        23 => vec!["-s", "--not-realpath", "--help"],
        24 => vec!["--version", "--help"],
        25 => vec!["-ms", "--", "--help", "-"],
        26 => vec![],
        27 => vec!["__rp-blocked/child"],
        28 => vec!["--zero=value"],
        29 => vec!["-smJ"],
        30 => vec!["__rp-blocked/./../missing"],
        33 => vec!["-P", "__rp-link/.."],
        34 => vec!["-L", "__rp-link/.."],
        35 => vec!["-mL", "__rp-cycle-a", "__rp-dangling"],
        36 => vec!["-mP", "__rp-cycle-a/child"],
        37 => vec!["-eL", "--relative-to=__rp-link", "__rp-dir"],
        38 => vec!["-eP", "--relative-to=__rp-link", "__rp-dir"],
        39 => vec!["-sP", "__rp-link"],
        40 => vec!["-Ps", "__rp-link"],
        _ => return None,
    };
    Some(support::case(argv, fixture, b""))
}
