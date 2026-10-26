use super::super::pattern::{
    Alternative, ArgvPattern, Atom, Element, OperandSource, OptionChoice, ValueContext, ValueSource,
};
use super::super::{support, system_state, PatternInputGenerator};
use crate::fuzz::GeneratedCase;
use rand::rngs::StdRng;
use rand::Rng;

const UTC: Element = Element::optional(
    35,
    Atom::Option(OptionChoice::available(&[
        "-u",
        "--utc",
        "--universal",
        "--uct",
    ])),
);
const FORMAT: Element = Element::once(Atom::Value(ValueSource::Generated(random_format)));

static ARGV_PATTERN: ArgvPattern = ArgvPattern::new(&[
    Alternative::requiring(
        5,
        &["-r"],
        &[
            UTC,
            Element::once(Atom::Literal("-r")),
            Element::once(Atom::Operand(OperandSource::Target {
                existing_percent: 80,
            })),
            FORMAT,
        ],
    ),
    Alternative::requiring(
        5,
        &["-d"],
        &[
            UTC,
            Element::once(Atom::Literal("-d")),
            Element::once(Atom::Value(ValueSource::Generated(random_date))),
            FORMAT,
        ],
    ),
    Alternative::weighted(
        2,
        &[
            Element::once(Atom::Value(ValueSource::Values(&[
                "--reference=a.txt",
                "--reference=a-link",
                "--reference=dir",
                "--reference=missing",
                "--reference=",
            ]))),
            FORMAT,
        ],
    ),
    Alternative::weighted(
        1,
        &[Element::once(Atom::Value(ValueSource::Values(&[
            "--help",
            "--version",
        ])))],
    ),
]);

pub(crate) static GENERATOR: PatternInputGenerator =
    PatternInputGenerator::patterned(&ARGV_PATTERN, scenario_case)
        .with_candidate_guard(deterministic_source)
        .with_mutation_guard(deterministic_source);

// A date campaign compares deterministic timestamps; it never pretends to freeze clocks.
fn deterministic_source(argv: &[String]) -> bool {
    let mut source = false;
    let mut index = 0;
    while index < argv.len() {
        let token = argv[index].as_str();
        if token == "--help" || token == "--version" {
            return true;
        }
        if token == "-d" || token == "--date" {
            source = true;
            index += 1;
            if index < argv.len() && !absolute_or_invalid_date(&argv[index]) {
                return false;
            }
        } else if let Some(value) = token.strip_prefix("--date=") {
            source = true;
            if !absolute_or_invalid_date(value) {
                return false;
            }
        } else if token.starts_with("-d") && token.len() > 2 {
            source = true;
            if !absolute_or_invalid_date(&token[2..]) {
                return false;
            }
        } else if token == "-r" || token == "--reference" {
            source = true;
            index += 1;
        } else if token.starts_with("--reference=") || (token.starts_with("-r") && token.len() > 2)
        {
            source = true;
        }
        if token.starts_with('+') && !supported_format(&token[1..]) {
            return false;
        }
        index += 1;
    }
    source
}

fn supported_format(format: &str) -> bool {
    let mut chars = format.chars().peekable();
    while let Some(value) = chars.next() {
        if value != '%' {
            continue;
        }
        let Some(code) = chars.next() else {
            return true;
        };
        if code == ':' {
            let mut colons = 1;
            while chars.peek() == Some(&':') {
                chars.next();
                colons += 1;
            }
            if colons > 3 || chars.next() != Some('z') {
                return false;
            }
        } else if matches!(code, '-' | '_' | '0'..='9' | '^' | '#' | '+' | 'E' | 'O') {
            return false;
        }
    }
    true
}

fn absolute_or_invalid_date(value: &str) -> bool {
    value.starts_with('@') || value == "invalid-date"
}

fn random_date(_context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    match rng.random_range(0..12) {
        0 => "invalid-date".to_string(),
        1 => "@-0.000000001".to_string(),
        2 => "@-62198755200".to_string(),
        3 => "@9223372036854775807".to_string(),
        4 => "@-9223372036854775808".to_string(),
        5 => "@951782400.123456789".to_string(),
        6 => "@-62135596800".to_string(),
        7 => "@-62167219200".to_string(),
        _ => format!(
            "@{}.{:09}",
            rng.random_range(-10_000_000_000_000_i64..=10_000_000_000_000_i64),
            rng.random_range(0..1_000_000_000_u32)
        ),
    }
}

fn random_format(_context: &ValueContext<'_>, rng: &mut StdRng) -> String {
    const DIRECTIVES: &[&str] = &[
        "%s", "%Y-%m-%d", "%H:%M:%S", "%F", "%T", "%R", "%D", "%x", "%X", "%c", "%r", "%a", "%A",
        "%b", "%B", "%C", "%d", "%e", "%g", "%G", "%h", "%H", "%I", "%j", "%k", "%l", "%m", "%M",
        "%N", "%p", "%P", "%q", "%S", "%u", "%U", "%V", "%w", "%W", "%y", "%Y", "%z", "%:z",
        "%::z", "%:::z", "%Z", "%n", "%t", "%%", "%J", "literal", "끝",
    ];
    let mut value = String::from("+");
    for index in 0..rng.random_range(0..=8) {
        if index != 0 {
            value.push('|');
        }
        value.push_str(DIRECTIVES[rng.random_range(0..DIRECTIVES.len())]);
    }
    if rng.random_bool(0.1) {
        value.push('%');
    }
    value
}

pub(super) fn scenario_case(iteration: usize) -> Option<GeneratedCase> {
    let fixture = system_state::failure_fixture();
    Some(match iteration {
        0 => support::case(vec!["--reference=a.txt", "+%s"], fixture, b""),
        1 => support::case(vec!["-u", "--reference=a.txt", "+%Y-%m-%d"], fixture, b""),
        2 => support::case(vec!["-r", "a.txt", "+%H:%M:%S"], fixture, b""),
        3 => support::case(vec!["-r", "a-link", "+%s.%N"], fixture, b""),
        4 => support::case(vec!["--reference=dir"], fixture, b""),
        5 => support::case(vec!["--date=@-1", "+%F %T %s"], fixture, b""),
        6 => support::case(vec!["-d", "@-62198755200", "+%C|%y|%Y|%F"], fixture, b""),
        7 => support::case(
            vec!["-d", "@951782400.123456789", "+%F %T.%N"],
            fixture,
            b"",
        ),
        8 => support::case(vec!["-d", "@-0.000000001", "+%s.%N %F %T"], fixture, b""),
        9 => support::case(vec!["-d", "@9223372036854775807", "+%s"], fixture, b""),
        10 => support::case(vec!["-d", "@-9223372036854775808", "+%F"], fixture, b""),
        11 => support::case(vec!["--reference=missing", "+%s"], fixture, b""),
        12 => support::case(vec!["--reference=loop", "+%s"], fixture, b""),
        13 => support::case(vec!["--reference=", "+%s"], fixture, b""),
        14 => support::case(vec!["--date=invalid-date", "+%F"], fixture, b""),
        15 => support::case(vec!["-d", "@0", "-r", "a.txt", "+%s"], fixture, b""),
        16 => support::case(vec!["--reference"], fixture, b""),
        17 => support::case(vec!["--date"], fixture, b""),
        18 => support::case(vec!["--date=@0", "--iso-8601=ns"], fixture, b""),
        19 => support::case(vec!["--date=@0", "--rfc-3339=seconds"], fixture, b""),
        20 => support::case(vec!["--date=@0", "-R"], fixture, b""),
        21 => support::case(vec!["--date=@0", "-I", "+%s"], fixture, b""),
        22 => support::case(vec!["--date=@0", "no-plus"], fixture, b""),
        23 => support::case(vec!["--date=@0", "+%s", "extra"], fixture, b""),
        24 => support::case(vec!["--help"], fixture, b""),
        25 => support::case(vec!["--version"], fixture, b""),
        26 => support::case(
            vec![
                "--date=@0",
                "+%%H%%I%%k%%l%%M%%N%%p%%P%%r%%R%%s%%S%%T%%X%%z%%Z",
            ],
            fixture,
            b"",
        ),
        27 => support::case(vec!["--iso-8601="], fixture, b""),
        28 => support::case(vec!["--rfc-3339="], fixture, b""),
        29 => support::case(vec!["-d", "@-62198755200", "+%D|%x|%y|%c|%Y"], fixture, b""),
        30 => support::case(vec!["-d", "@-62167219200", "+%c|%Y"], fixture, b""),
        31 => support::case(vec!["-d", "@-62135596800", "+%c|%Y"], fixture, b""),
        32 => support::case(
            vec!["-d", "@-3187056888438.630696753", "+%V|%b|%b|%x|%p|%P"],
            fixture,
            b"",
        ),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::{deterministic_source, supported_format};

    // Compound plain directives, Unicode literals, and colon offsets stay in the accepted grammar.
    #[test]
    fn plain_date_format_grammar() {
        assert!(supported_format(
            "%Y-%m-%d %T.%N|%G-W%V-%u|%:z|%::z|%:::z|%%_d|끝|%"
        ));
    }

    // Modifier syntax cannot leak into mutation or shrinking from the deferred GNU grammar.
    #[test]
    fn date_format_modifier_boundary() {
        assert!(!supported_format("%Y-%m-%d %_H"));
        assert!(!supported_format("%08Y"));
        assert!(!supported_format("%Ec"));
        assert!(!supported_format("%Od"));
    }

    // A reference filename beginning with '+' remains a path, even if its spelling resembles a format.
    #[test]
    fn reference_value_is_not_a_format() {
        let argv = vec![
            "--reference".to_string(),
            "+%_d".to_string(),
            "+%s".to_string(),
        ];
        assert!(deterministic_source(&argv));
    }

    // Relative dates cannot make a campaign claim synchronized current-time comparisons.
    #[test]
    fn relative_date_is_outside_deterministic_campaign() {
        let argv = vec!["--date=next monday".to_string(), "+%F".to_string()];
        assert!(!deterministic_source(&argv));
    }
}
