# GNU date benchmark scope

GNU coreutils `date` is specified at source revision
`2cf491412c199e2211880ec3f4ba387026638a33` (`src/date.c`, GPL-3.0-or-later).

## Accepted input and observations

The required scope is explicit `--reference=FILE`, `-u`, and explicit `+%s`,
`+%Y-%m-%d`, and `+%H:%M:%S`. All remain supported. The expanded scope includes:

- `-r`/`--reference`: select the last modification timestamp, follow a terminal
  symlink, and accept ordinary files and directories. Access time is never
  substituted. Preserve the exact native metadata errno on failure.
- `-d`/`--date`: use the existing trusted gnulib date parser, including absolute
  epochs, fractional seconds, civil dates, and relative expressions under its
  supplied whole-second reference-time contract. Repeated source options use
  the last value. Date and reference selection are mutually exclusive.
- UTC spellings `-u`, `--uct`, `--utc`, `--universal`; execution assumes `TZ=UTC0`.
- `-I`/`--iso-8601` with date, hours, minutes, seconds or ns precision; `-R`,
  `--rfc-email`, `--rfc-822`, `--rfc-2822`; and `--rfc-3339` with date, seconds
  or ns precision. Unique precision abbreviations are accepted.
- Exact GNU help/version, missing option values, unknown options, conflicting
  date sources, extra operands, missing leading `+`, conflicting output formats,
  invalid precision values, invalid dates, metadata errors and calendar overflow.
  GNU long-option abbreviations with one matching declared spelling are accepted;
  aliases that share a prefix are subject to the fixed parser's ambiguity rule.

A format is a finite Unicode string after its leading `+`, consisting of literal
characters, plain percent directives, or the UTC forms `%:z`, `%::z`, `%:::z`.
Plain directives are `%%`, `%a`, `%A`, `%b`, `%B`, `%c`, `%C`, `%d`, `%D`, `%e`,
`%F`, `%g`, `%G`, `%h`, `%H`, `%I`, `%j`, `%k`, `%l`, `%m`, `%M`, `%n`, `%N`,
`%p`, `%P`, `%q`, `%r`, `%R`, `%s`, `%S`, `%t`, `%T`, `%u`, `%U`, `%V`, `%w`,
`%W`, `%x`, `%X`, `%y`, `%Y`, `%z`, `%Z`. Unknown single-character directives
are retained literally; a final `%` is retained. Empty formats are valid and
produce the mandatory final newline. GNU flag, width, `E`, and `O` modifier
syntax is outside this contribution's accepted grammar.

The environment is GNU/Linux with glibc, C locale, UTC0, finite stable trees/arguments and enough
memory. Every modeled stdout/stderr byte and exact exit status is constrained.
Partial writes and their native errno remain linked to the stream observations;
`/dev/full` is covered. Access-time changes, asynchronous faults and concurrency
follow the shared model limits. This utility does not change files or consume
standard input in the accepted scope.

## Mathematical requirements and trust boundary

Calendar fields satisfy the proleptic Gregorian calendar, the 1970-01-01 UTC
epoch, and the timestamp's exact second-of-day decomposition. Decimal fields
use canonical positional digits with the directive's GNU sign and default
padding rules. ISO week-years are the civil year of their week's Thursday.
Negative-year century and short-year representations follow GNU formatting
semantics. `%x` uses the year's nonnegative remainder modulo 100 and `%c` uses an unpadded
signed year, matching the pinned glibc C-locale composite formats; `%D` and
standalone `%y` retain GNU's short-year magnitude for negative years. Format and output partitions constrain every character.
The direct `RunCore` postcondition is the observable `DateSpec.Spec` relation.

Trusted operations are the existing IO stream, errno/argument quoting, file
metadata, whole-second clock and gnulib `ParseDate` contracts. Conditional
filename quoting uses the existing pure `StringEscaping` definitions. CLI
parsing remains the fixed protocol boundary. There is no trusted native calendar
conversion, formatter or utility-answer operation. Shared primitive contracts
remain conditional proof assumptions about the operating environment.

## Limits and remaining coverage


These valid GNU behaviors require missing system observations and are excluded:
current-time nanoseconds (`Now` only observes whole seconds), `--resolution`
(clock resolution), `--debug` (parser diagnostic trace), `--set` and the legacy
numeric clock-setting operand (system clock mutation), and locale/non-UTC
formatting (locale/timezone service). Current-time formats that require `%N` are
outside scope; deterministic reference and parsed instants retain nanoseconds.

Separately, GNU format flags/width/`E`/`O` modifiers and `--file` batch conversion
remain implementation/proof work. They are not claimed as IO API gaps. This
contribution preserves the originally selected minimum and makes a bounded
format/source expansion; it does not claim full GNU date equivalence. The fuzzer
guard enforces this grammar for mutation and shrinking without changing any
comparison or suppressing a mismatch. Long aliases with a shared prefix need a
future fixed-parser compatibility improvement.

## Upstream evidence and examples

Behavior is grounded in `src/date.c`, `gnulib/lib/strftime.c`, and upstream
`tests/date/reference.sh`, `tests/date/date.pl`, `tests/date/percent-percent.sh`,
plus the GNU help/version and write-error interface tests at the pinned revision.
Representative inputs are `date -u --reference=FILE +%Y-%m-%d`,
`date --reference=FILE +%H:%M:%S`, `date -d @-1 +%s`, and
`date --date=@951782400.123456789 --iso-8601=ns`.

The contract must rule out substituting atime for mtime, truncating negative
epoch division toward zero, treating 1900 as a leap year, dropping a negative
century's minus sign, using the civil year for an ISO week-year boundary,
discarding write failures, or returning success after failed metadata lookup.
Contributor implementation notes, failed attempts and validation evidence are
kept outside the public task resources and are not benchmark inputs.
