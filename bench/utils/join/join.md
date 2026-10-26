# GNU join

This maintenance contribution models the pinned GNU coreutils `join`,
`coreutils/src/join.c` at `2cf491412c199e2211880ec3f4ba387026638a33`
(GPL-3.0-or-later). The minimum scope is the `TODOLIST.csv` join row.

## Accepted inputs and environment

Two finite, stable file operands, with at most one `-` for captured standard
input. C locale, UTC0, ordinary Linux files and modeled IO failures. All GNU
options are in scope: `-1`, `-2`, `-j`, `-t`, `-a`, `-v`, `-e`, `-i`, `-o`,
`-z`, `--check-order`, `--nocheck-order`, `--header`, `--help`, `--version`;
long abbreviations, attached values, repeated options, and GNU legacy `-j1` /
`-j2` and continued `-o` operand forms are included. Invalid arguments and
conflicting values produce the pinned C-locale diagnostics.

The observable contract determines exact stdout, stderr, exit status, and
modeled stdin consumption. Record and field partitions, match rectangles,
Cartesian row order and diagnostic positions are mathematical relations.
Algorithms and proof witnesses remain task-local. Fixed diagnostic/help/version
bytes are defined in Spec. The entry point directly ensures `Spec`.

## Scope evidence and limits

Source functions `xfields`, `keycmp`, `check_order`, `get_line`, `prjoin`,
`join`, `string_to_join_field`, `add_file_name`, and `main` determine the scope.
Named upstream scenarios are from `coreutils/tests/join/join.pl` (including
`1a`–`10f`, `v2-order`, `trailing-sp`, `sp-vs-blank`, `bigfield1`, `invalid-j`,
`chkodr-*`, `header-*`, `z1`–`z6`). The C locale treats space/tab/newline as
field blanks; form feed is data. `-t ''` treats a nonempty record as one field;
`-t '\0'` uses NUL. ASCII case folding applies under `-i`.

The existing whole-input API models finite byte acquisition rather than GNU
stdio read-ahead offsets. Kernel descriptor offsets and asynchronous timing are
not compared. Interactive/infinite/device input, concurrent mutations, forced
memory exhaustion, disk spilling, locale collation outside C, and injected late
read/close failures are outside the established repository stream environment.
Returned native read errors and committed write prefixes remain explicit in the
formal relation and implementation. No GNU option is excluded for missing IO
support. No trusted core extension is planned.

## Trust and proof obligations

The existing `ReadFile`, `ProbeReadFile`, `ReadStdin`, `WriteStdout`,
`WriteStderr`, errno text, path quoting, UTF-8 and CLI runtime contracts form the
native boundary. Field parsing, lexical comparison, match groups, formatting,
warning selection and exit policy must be derived and proved locally. Runtime
agreement and Dafny verification are separate acceptance requirements.

## Acceptance checks

Acceptance requires the supported build, test and verification targets, exact
GNU stream and exit-status comparisons, and strict seeded differential fuzzing.
Runtime agreement and Dafny verification establish separate properties.
The existing evaluator and scoring policy apply without utility-specific skips.
