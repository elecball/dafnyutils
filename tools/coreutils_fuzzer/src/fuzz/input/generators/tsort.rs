use super::super::pattern::{Alternative, ArgvPattern, Atom, Element, ValueSource};
use super::super::CwdPolicy;
use super::super::PatternInputGenerator;
use super::super::{support, system_state};
use crate::fuzz::{FileSpec, FixtureBlueprint, GeneratedCase};
use rand::rngs::StdRng;
use rand::Rng;
use std::path::PathBuf;

const OPTION: Atom = Atom::Value(ValueSource::Values(&[
    "-w",
    "-ww",
    "--help",
    "--version",
    "--he",
    "--ver",
]));
const FILE: Atom = Atom::Value(ValueSource::Values(&[
    "graph", "a.txt", "dir", "missing", "loop", "dangling", "denied", "", "-",
]));
const INVALID: Atom = Atom::Value(ValueSource::Values(&[
    "-x",
    "-wx",
    "-é",
    "--bad",
    "--help=x",
    "--version=x",
    "--=x",
]));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::new(&[
        Element::repeated(0, 2, OPTION),
        Element::repeated(0, 2, FILE),
    ]),
    Alternative::new(&[Element::once(FILE), Element::once(OPTION)]),
    Alternative::new(&[Element::once(INVALID)]),
    Alternative::new(&[Element::once(Atom::Literal("--")), Element::once(FILE)]),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_system_state(random_system_state)
        .with_case_normalizer(supply_graph_stdin)
        .with_cwd_policy(CwdPolicy::Root);

fn graph_fixture(data: &[u8]) -> FixtureBlueprint {
    let mut fixture = system_state::failure_fixture();
    fixture.files.push(FileSpec {
        relative_path: PathBuf::from("denied"),
        bytes: b"a b\n".to_vec(),
        mode: 0o000,
    });
    fixture.files.push(FileSpec {
        relative_path: PathBuf::from("graph"),
        bytes: data.to_vec(),
        mode: 0o644,
    });
    fixture
}

fn random_system_state(rng: &mut StdRng, _max_fs_entries: usize) -> FixtureBlueprint {
    let names: &[&[u8]] = &[
        b"a", b"b", b"c", b"d", b"e", b"z", b"a\0tail", b"\0", b"\x80", b"\xff", b"a\rb",
        b"a\x0bb", b"a\x0cb",
    ];
    let separators: &[&[u8]] = &[b" ", b"\t", b"\n", b" \t\n"];
    let mut data = Vec::new();
    let pairs = rng.random_range(0..=32);
    let odd = usize::from(rng.random_bool(0.15));
    for _ in 0..2 * pairs + odd {
        data.extend_from_slice(names[rng.random_range(0..names.len())]);
        data.extend_from_slice(separators[rng.random_range(0..separators.len())]);
    }
    graph_fixture(&data)
}

fn supply_graph_stdin(case: &mut GeneratedCase) {
    if let Some(file) = case
        .fixture
        .files
        .iter()
        .find(|f| f.relative_path == PathBuf::from("graph"))
    {
        case.stdin = file.bytes.clone();
    }
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let (args, data): (Vec<&str>, &[u8]) = match iteration {
        0 => (vec![], b"a b b c\n"),
        1 => (vec!["graph"], b"a b a z\n"),
        2 => (vec!["-"], b"b a d c z h x h r h\n"),
        3 => (vec![], b"a b a b b c\n"),
        4 => (vec![], b"z z a a z z\n"),
        5 => (vec![], b""),
        6 => (vec![], b"a b c\n"),
        7 => (vec!["graph"], b"t b t s s t\n"),
        8 => (vec!["-w", "graph"], b"a a a b a c c a b a"),
        9 => (vec![], b"a b b a c d d c\n"),
        10 => (vec![], b"a\0tail b a c\n"),
        11 => (vec![], b"\xff \xff \x80 \x80 a a\n"),
        12 => (vec![], b"a\rb c a\x0bb d a\x0cb e\n"),
        13 => (vec!["--help", "--bad"], b""),
        14 => (vec!["--version", "--help"], b""),
        15 => (vec!["-wx"], b""),
        16 => (vec!["-", "a'b"], b""),
        17 => (vec!["missing"], b""),
        18 => (vec!["dir"], b""),
        19 => (vec!["--", "graph"], b"a b c d\n"),
        20 => (vec!["loop"], b""),
        21 => (vec!["dangling"], b""),
        22 => (vec!["--help=x"], b""),
        23 => (vec!["--bad", "--help"], b""),
        24 => (vec!["graph", "--help"], b"a\n"),
        25 => (vec!["denied"], b""),
        _ => return None,
    };
    Some(support::case(args, graph_fixture(data), data))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;

    #[test]
    fn normalization_preserves_arguments_and_graph() {
        let mut case = scenario_case(8).unwrap();
        let argv = case.argv.clone();
        let data = case.stdin.clone();
        case.stdin.clear();
        supply_graph_stdin(&mut case);
        assert_eq!(case.argv, argv);
        assert_eq!(case.stdin, data);
        assert_eq!(case.fixture.files.last().unwrap().bytes, data);
    }

    #[test]
    fn random_graphs_are_reproducible_and_varied() {
        let mut first = StdRng::seed_from_u64(42);
        let mut second = StdRng::seed_from_u64(42);
        let mut inputs = std::collections::BTreeSet::new();
        for _ in 0..32 {
            let left = random_system_state(&mut first, 8);
            let right = random_system_state(&mut second, 8);
            let data = &left.files.last().unwrap().bytes;
            assert_eq!(data, &right.files.last().unwrap().bytes);
            assert!(data.len() <= 65 * 10);
            inputs.insert(data.clone());
        }
        assert!(inputs.len() > 1);
    }
}
