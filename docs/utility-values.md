# Value, path and environment utilities

These notes explain the current implementations and their main specification
relations. See the [utility guide](utility-guide.md) for the shared architecture,
IO trust boundary and final entrypoint obligation. The descriptions concern the
implemented benchmark behavior, not all GNU options or a new verification run.
Unless stated otherwise, a stream write failure makes the final status 1.

## basename

### Implementation

[`ComputeBasenameValue`](../bench/utils/basename/Impl/BasenameCore.dfy) scans backward
past trailing slashes, then backward to the preceding slash. Empty input gives
an empty basename; an all-slash path gives `/`.
`RemoveSuffixIfNeeded` removes a matching, nonempty suffix only when something
would remain. `BuildRunOutput` selects single-operand or multiple-operand
processing and appends newline or NUL separators. Missing operands and excess
operands in single-name mode produce diagnostics and status 1; normal output
has status 0 before emission.

### Proof idea

[`BasenameRelation` and `SuffixRemovalRelation`](../bench/utils/basename/Spec/BasenameSpec.dfy)
describe the maximal slash-free final component and permitted suffix removal.
The proof converts the scan's index bounds into that path decomposition.
[`RenderSummaryGivesRelation`](../bench/utils/basename/Proof/BasenameProof.dfy) then
constructs pieces and output boundaries: each operand contributes exactly its
basename and separator, in order. `RunOutputSummaryGivesRelation` combines this
with command selection and the error branches.

## date

### Implementation

[`Select` and `TimeOutput`](../bench/utils/date/Impl/DateCore.dfy) select an explicit
reference-file timestamp or a parsed instant, then convert epoch seconds into
UTC calendar fields locally. [`DateCalendar`](../bench/utils/date/Proof/DateCalendar.dfy)
uses 400-year Gregorian eras and bounded year/month searches. The renderer
partitions the format into literals and supported directives, including ISO
week dates and C-locale composite fields. GNU format modifiers, batch input,
clock mutation and non-UTC locales are outside
[the declared scope](../bench/utils/date/date.md).

### Proof idea

[`Calendar` and `NumberText`](../bench/utils/date/Spec/DateModel.dfy) characterize the
epoch equation, leap-year/month bounds and positional decimal output. Local
lemmas prove the era conversion and rendering against these relations.
[`DateSpec`](../bench/utils/date/Spec/DateSpec.dfy) requires exact directive meanings,
format/output partitions, timestamp selection and stream outcomes. The final
entry directly ensures `Spec`. File metadata and the existing gnulib date parser
remain trusted observations; calendar conversion and formatting are utility
proof obligations.

## dirname

### Implementation

[`ComputeDirnameValue`](../bench/utils/dirname/Impl/DirnameCore.dfy) trims trailing
slashes, finds the last remaining slash and trims the prefix before it. Empty
input and paths without a directory component produce `.`; all-slash paths
and a root-level prefix produce `/`. `BuildRunOutput` applies this to each
operand, using newline or NUL termination. No operands produce a diagnostic
and status 1; otherwise computation succeeds before stream emission.

### Proof idea

[`DirnameRelation`](../bench/utils/dirname/Spec/DirnameSpec.dfy) requires a decomposition
into a trailing-slash-free path, its final slash-free component and a normalized
directory prefix. It states the `.` and `/` cases separately.
[`DirnameValueSummaryGivesRelation`](../bench/utils/dirname/Proof/DirnameProof.dfy)
turns the trimming and last-slash summaries into those witnesses.
`RenderSummaryGivesRelation` supplies an output partition proving one correctly
terminated result per operand in the original order.

## echo

### Implementation

[`Command`](../bench/utils/echo/Impl/EchoCore.dfy) scans the initial run of valid
`-n`, `-e` and `-E` option tokens. The last escape-setting option determines
that setting; `POSIXLY_CORRECT` also changes option recognition and enables
escape interpretation. `RenderEscaped` decodes named, octal and hexadecimal
escapes. A `\c` stops the remaining argument and all later arguments, and
suppresses the final newline. `RenderOperands` joins processed arguments with
spaces; ordinary execution starts with status 0.

### Proof idea

[`CommandRelation`](../bench/utils/echo/Spec/EchoSpec.dfy) characterizes the maximal
option prefix and its effective settings without using the scanner.
`EscapedPartition` divides an argument and its output into corresponding
escape units; only the final unit may stop processing. `OperandPartition`
extends this to arguments, spaces and early stopping.
[`OutputSatisfiesRelation`](../bench/utils/echo/Proof/EchoProof.dfy) combines the
scanner correspondence and these partitions to establish the exact output,
including whether a newline is permitted.

## expr

### Implementation

[`ParseOr` through `ParsePrimary`](../bench/utils/expr/Impl/ExprCore.dfy) form a
recursive-descent evaluator with precedence levels for Boolean operations,
comparisons, addition and multiplication. Primaries include parentheses,
literal quoting with `+`, `length`, `substr` and `index`. Arithmetic parses
signed decimal integers; division truncates toward zero. Comparisons use
integers when both operands are numeric and character-order comparison
otherwise. Regular-expression operations are explicitly unsupported.
`EvaluateArgs` prints a complete result followed by newline, with status 0 for
a true value and 1 for empty or numeric-zero values. Parse and evaluation errors
return 2; stream failures return 3.

### Proof idea

[`OrJudgment` and the other evaluation judgments](../bench/utils/expr/Spec/ExprSpec.dfy)
relate tokens, consumed positions and either a value or a diagnostic. Separate
relations define decimal values, arithmetic, comparison, substring bounds and
the first matching character index. The proof first connects numeric parsing
and rendering to these value relations, then proves each parser level respects
its judgment. [`EvaluateRefinement`](../bench/utils/expr/Proof/ExprProof.dfy) uses the
top-level judgment, full token consumption and `ValueTruth` to establish output
and status, including failures rather than just successful expressions.

## factor

### Implementation

[`FactorizeFrom`](../bench/utils/factor/Impl/FactorCore.dfy) tries 2 and then odd
divisors up to the square root of the remaining value. On division it records
the factor and restarts at 2; a remainder beyond the square bound is the last
factor. `RenderFactors` either lists factors or groups equal factors into
exponents. `ProcessToken` accepts nonnegative decimal integers with an optional
`+`; 0 and 1 have no listed factors. Operands are processed independently, or
stdin is split into tokens when there are no operands. Invalid tokens do not
prevent later results. Returned bytes from a failed stdin read are still
processed; any token or read error makes the status 1.

### Proof idea

[`PrimeFactorizationRelation`](../bench/utils/factor/Spec/FactorSpec.dfy) requires a
nonempty, nondecreasing sequence of primes whose product is the input, for
inputs above 1. [`FactorizeFromSatisfiesRelation`](../bench/utils/factor/Proof/FactorProof.dfy)
maintains the absence of smaller divisors. This makes a found divisor prime,
justifies the final remainder, and proves that prepending a factor preserves
product and order. Output partitions connect individual primes or maximal
equal-prime groups to their decimal text. Token and input partitions then
connect parsing, valid output, ordered diagnostics and aggregate error status
to `RunRelation`.

## false

### Implementation

[`Prepare`](../bench/utils/false/Impl/FalseCore.dfy) selects help text, version text
or no output. Every branch returns 1, including help and version. Ordinary
execution performs no stream writes; the selected informational modes use
the normal emission path, whose failures also return 1.

### Proof idea

[`PreparedSpec`](../bench/utils/false/Spec/FalseSpec.dfy) directly enumerates the
three modes and requires status 1 in each. There is no computational result to
characterize: [`PreparedSummaryImpliesPreparedSpec`](../bench/utils/false/Proof/FalseProof.dfy)
checks those branches, and the final bridge retains the specified emission
result. `Emits` limits writes to help and version, so ordinary false behavior
does not depend on a stdout write succeeding.

## logname

### Implementation

[`Prepare`](../bench/utils/logname/Impl/LognameCore.dfy) handles help and version,
rejects any operand, then calls `GetLoginName`. A successful lookup prints the
name followed by newline and returns 0. Failure emits the fixed no-login-name
diagnostic and returns 1. The name comes from the login-name IO contract,
rather than an environment-variable lookup.

### Proof idea

[`PreparedSpec`](../bench/utils/logname/Spec/LognameSpec.dfy) selects success by
the presence of `loginName` in the modeled properties map and specifies its
encoded value and terminator. The implementation retains the result as a
`LoginNameResultFields` witness tied to `GetLoginNameContractFields`.
[`PreparedSummaryImpliesPreparedSpec`](../bench/utils/logname/Proof/LognameProof.dfy)
splits that result into success and failure, deriving the corresponding map
property and output. The native lookup itself remains behind the IO contract.

## printenv

### Implementation

[`Output`](../bench/utils/printenv/Impl/PrintenvCore.dfy) either renders every
entry returned by `GetEnvironment`, or looks up requested names and prints
their values in operand order. Entries are split at the first `=`; the rest
is the value. Newline or NUL terminates each printed entry or value. Missing
names produce no value or diagnostic, but `AnyMissing` makes the status 1
while preserving other results. A stream failure instead returns 2.

### Proof idea

[`EnvironmentOutputRelation` and `OperandResultRelation`](../bench/utils/printenv/Spec/PrintenvSpec.dfy)
separate complete environment listing from requested-name lookup. The former
uses the IO-provided entry order; it does not impose sorting on a map.
[`LookupEntryRepresentedEnvironment`](../bench/utils/printenv/Proof/PrintenvProof.dfy)
proves that splitting and searching the contracted entry sequence agrees with
map membership and values. `OperandResultFromEnvironmentEntries` lifts that
fact to ordered output and missing-name status; the listing proof preserves
every returned entry and its terminator.

## printf

### Implementation

[`ClassifyFragment` and `RenderPass`](../bench/utils/printf/Impl/PrintfCore.dfy)
process the format a fragment at a time. The current conversion subset is
`%s` and `%%`, together with literal text and format escapes; other conversions
produce an unsupported-format diagnostic. Missing `%s` arguments are empty.
`RenderRepeatedFrom` repeats the format while arguments are consumed, warning
about excess arguments if a pass consumes none. `\c` stops successfully;
malformed supported escapes fail while retaining prior output. Unicode escapes
use the representation defined by `UnicodeBytes`, which emits ASCII directly
and textual universal-character escapes for larger values. Missing format,
format errors and stream failures return 1.

### Proof idea

[`FormatFragmentRelation` and `FormatDerivationRelation`](../bench/utils/printf/Spec/PrintfSpec.dfy)
describe legal fragments and a finite derivation of a completed or stopped pass.
`RepeatedPassesFromRelation` accounts for format reuse, argument consumption,
output concatenation and excess-argument warnings.
[`BuildFormatDerivation` and `BuildRepeatedDerivation`](../bench/utils/printf/Proof/PrintfProof.dfy)
construct those witnesses from the renderer. `EvaluateRefines` then relates
the result to command-level output and status, distinguishing successful
early stopping from a format error. The proof covers these defined conversions
and escape representations, not the full conversion list in GNU's help text.

## pwd

### Implementation

[`SelectDirectory`](../bench/utils/pwd/Impl/PwdCore.dfy) chooses logical or physical
mode from the last explicit mode option, or `POSIXLY_CORRECT` when neither is
present. Logical mode accepts `PWD` only if it is absolute, has no `.` or `..`
components, and its followed status has the same identity as the current
directory. Otherwise [`PhysicalDirectory`](../bench/utils/pwd/Impl/PwdRecoveryCore.dfy)
tries `GetCwd`, then recovers by ascending parents and finding the child's name
in each parent until reaching root. It retains failures from directory access,
search and close operations. Extra operands cause a warning. Successful output
is the directory plus newline; recovery or stream failures return 1, as does a
failed warning write.

### Proof idea

[`DirectorySelectionFields`](../bench/utils/pwd/Spec/PwdSpec.dfy) combines logical
selection evidence with a physical-selection witness when logical selection
fails. [`PhysicalSelectionFields`](../bench/utils/pwd/Spec/PwdPhysicalSpec.dfy)
requires an ordered trace of the direct attempt, statuses and parent attempts,
plus a partition spelling the recovered path from the discovered names.
[`AppendStep` and `PathPartitionSnoc`](../bench/utils/pwd/Proof/PwdProof.dfy) preserve
those trace and path witnesses during ascent. Native directory observations
remain contractual inputs. `RunFields` composes the warning, selection and
emission outcomes; `PwdCore.RunCore` establishes `Spec` directly, including the
modeled directory-state changes made during recovery.

## readlink

### Implementation

[`Prepare`](../bench/utils/readlink/Impl/ReadlinkCore.dfy) processes operands in order,
calling `ReadLinkAtCwd` for each nonempty path. Success appends the link target;
failure records status 1 and emits a diagnostic only in verbose mode, then
continues. Empty paths fail without a native read. Output ends in newline or
NUL; no-newline mode applies to one operand and warns when there are several.
Canonicalization is explicitly unsupported. Missing operands, unsupported
canonicalization and stream failures also return 1.

### Proof idea

[`RunFilesWitnessRelation`](../bench/utils/readlink/Spec/ReadlinkSpec.dfy) requires
one observation and output/diagnostic fragment per operand. Each observation
uses the proper native-read offset, and `hadError` is exactly the existence
of a failed observation. Fragment boundaries require complete, ordered
concatenation. [`RunFilesSummaryImpliesRelation`](../bench/utils/readlink/Proof/ReadlinkProof.dfy)
constructs this witness from the processed-prefix summary.
[`OffsetSnoc`](../bench/utils/readlink/Proof/ReadlinkContextProof.dfy) supports the
context accounting, including empty operands that make no native call.
The result is tied to the native readlink contract, not merely to an arbitrary
target string.

## realpath

### Implementation

[`InterpretPhysical`, `InterpretStrip`, and `Relative`](../bench/utils/realpath/Impl/RealpathCore.dfy)
implement the pinned GNU default physical traversal, explicit `-P`, logical
two-pass `-L`, and strip `-s` modes. Physical traversal expands links before
handling `..`; logical traversal normalizes lexical parents before expanding
links. After twenty expansions, cycle keys use parent device/inode identity
and the entire remaining raw path, preserving the difference between cycles
and repeated links with different suffixes. There is no global forty-link cap.
`-m` permits missing components and retains a repeated link component;
`-E`/`-e` apply the specified existence/directory checks and cycle errors.
Relative-directory preparation precedes operands; ordered results and diagnostics
preserve quiet/NUL behavior and fatal-error prefixes. See the
[full traversal scope](../bench/utils/realpath/realpath.md).

### Proof idea

[`Meaning`, `PhysicalMeaning`, and `RelativePath`](../bench/utils/realpath/Spec/RealpathSpec.dfy)
give inductive path denotations and a maximal-common-prefix relation. They bind
raw readlink results, ordinal-sensitive parent status observations and exact
output partitions, without a trusted canonicalization answer. A utility-local
finite-record measure and structural descent establish termination: every new
cycle key retains a native record, whose 24-byte size and the fixed 64-bit
address space give a physical storage bound. Exhausting that representation
produces GNU's global memory-fatal result, not an arbitrary traversal limit;
earlier host allocation-failure timing remains outside the enough-memory
environment. `RunCore` directly ensures `Spec`, with no new trusted primitive
or termination waiver.

## seq

### Implementation

[`ParseDecimal` and `ParseNumbers`](../bench/utils/seq/Impl/SeqCore.dfy) parse one
to three decimal operands, including signs, decimal points and exponents,
and supply default first value and increment. Numbers use an integer value
and decimal scale. `RenderSequence` rescales them to a common scale, computes
the finite term count, generates the arithmetic progression, then renders
fixed-point text. Equal-width mode zero-pads to the widest rendered item;
items use the selected separator and the last item ends in newline. The first
term can preserve negative zero. Invalid operands and a zero increment return
1; an empty progression is successful.

### Proof idea

[`DecimalValueRelation`](../bench/utils/seq/Spec/SeqSpec.dfy) characterizes syntax
and positional numeric value using witnesses for the exponent and decimal
point. Parsing proofs establish both successful values and rejection when
no value witness exists. `SequenceItemsRelation` defines each term by
`firstValue + i * stepValue`, the prescribed term count, fixed rendering and
maximum width. [`SequenceOutputRelation`](../bench/utils/seq/Proof/SeqProof.dfy)
connects generated values and padding to those indexed properties, then
supplies fragment boundaries for the separators and final newline. The
command-level bridge also preserves operand-error selection and status.

## true

### Implementation

[`Prepare`](../bench/utils/true/Impl/TrueCore.dfy) returns 0 and selects either
help text, version text or no output. Ordinary execution performs no stream
writes. Help and version use the emission path, so a write failure changes
their final status to 1.

### Proof idea

[`PreparedSpec`](../bench/utils/true/Spec/TrueSpec.dfy) requires the selected text
and normal status 0, with empty planned output in ordinary mode.
[`PreparedSummaryImpliesPreparedSpec`](../bench/utils/true/Proof/TrueProof.dfy)
discharges the mode cases directly. `Emits` and the emission relation distinguish
the ordinary no-write result from informational output whose writes may fail;
the final bridge carries that distinction into the utility specification.
