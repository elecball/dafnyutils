include "TruncateSchema.dfy"
include "../../../core/IO.dfy"
include "../../../core/Utf8.dfy"
include "../Impl/CliSupport.dfy"

module TruncateSpec {
  import S = TruncateSchema
  import BenchIO
  import W = BenchWorld
  import C = IOContract
  import Utf8 = Utf8Semantics
  import CliTypes
  import CliModel

  function HelpText(): W.Bytes { "Usage: truncate OPTION... FILE...\nShrink or extend the size of each FILE to the specified size\n\nA FILE argument that does not exist is created.\n\nIf a FILE is larger than the specified size, the extra data is lost.\nIf a FILE is shorter, it is extended and the sparse extended part (hole)\nreads as zero bytes.\n\nMandatory arguments to long options are mandatory for short options too.\n  -c, --no-create        do not create any files\n  -o, --io-blocks        treat SIZE as number of IO blocks instead of bytes\n  -r, --reference=RFILE  base size on RFILE\n  -s, --size=SIZE        set or adjust the file size by SIZE bytes\n      --help\n         display this help and exit\n      --version\n         output version information and exit\n\nThe SIZE argument is an integer and optional unit (example: 10K is 10*1024).\nUnits are K,M,G,T,P,E,Z,Y,R,Q (powers of 1024) or KB,MB,... (powers of 1000).\nBinary prefixes can be used, too: KiB=K, MiB=M, and so on.\n\nSIZE may also be prefixed by one of the following modifying characters:\n'+' extend by, '-' reduce by, '<' at most, '>' at least,\n'/' round down to multiple of, '%' round up to multiple of.\n\nReport bugs to: bug-coreutils@gnu.org\nGNU coreutils home page: <https://www.gnu.org/software/coreutils/>\nGeneral help using GNU software: <https://www.gnu.org/gethelp/>\nReport any translation bugs to <https://translationproject.org/team/>\nFull documentation <https://www.gnu.org/software/coreutils/truncate>\nor available locally via: info '(coreutils) truncate invocation'\n" }

  function VersionText(): W.Bytes { "truncate (GNU coreutils) 9.10.13-2cf49\nCopyright (C) 2026 Free Software Foundation, Inc.\nLicense GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\nThis is free software: you are free to change and redistribute it.\nThere is NO WARRANTY, to the extent permitted by law.\n\nWritten by Padraig Brady.\n" }

  const MaxSize: int := 9223372036854775807
  const MinSize: int := -9223372036854775808

  function WriteErrorTextPart1(): W.Bytes
  {
    "truncate: write error: "
  }

  function WriteErrorTextPart2(): W.Bytes
  {
    "\n"
  }

  function WriteErrorText(reason: string): W.Bytes
  {
    WriteErrorTextPart1() + Utf8.Encode(reason) + WriteErrorTextPart2()
  }
  ghost function WriteError(err: int): W.Bytes
  {
    WriteErrorText(C.CLocaleErrnoTextResult(err))
  }
  function UsageHint(): W.Bytes { "Try 'truncate --help' for more information.\n" }
  function MultipleModifiers(): W.Bytes {
    "truncate: multiple relative modifiers specified\n" + UsageHint()
  }
  function DivisionByZero(): W.Bytes { "truncate: division by zero\n" }
  function MissingSize(): W.Bytes {
    "truncate: you must specify either '--size' or '--reference'\n" + UsageHint()
  }
  function AbsoluteReference(): W.Bytes {
    "truncate: you must specify a relative '--size' with '--reference'\n" + UsageHint()
  }
  function BlocksWithoutSize(): W.Bytes {
    "truncate: '--io-blocks' was specified but '--size' was not\n" + UsageHint()
  }
  function MissingFile(): W.Bytes { "truncate: missing file operand\n" + UsageHint() }
  ghost function InvalidNumber(text: string, overflow: bool): W.Bytes
  {
    InvalidNumberText(C.QuoteArgumentResult(Utf8.Encode(text)), overflow)
  }
  function InvalidNumberText(quoted: W.Bytes, overflow: bool): W.Bytes {
    "truncate: Invalid number: " + quoted +
    (if overflow then ": Value too large for defined data type" else "") + "\n"
  }
  function IsSpace(c: char): bool { c in {' ', '\t', '\n', '\r', (11 as char), (12 as char)} }
  function IsDigit(c: char): bool { '0' <= c <= '9' }
  function Digit(c: char): nat
    requires IsDigit(c)
  { ((c as int) - ('0' as int)) as nat }
  predicate Digits(text: string) {
    forall i :: 0 <= i < |text| ==> IsDigit(text[i])
  }
  function Decimal(text: string): nat
    requires Digits(text)
    decreases |text|
  {
    if |text| == 0 then 0 else Decimal(text[..|text| - 1]) * 10 + Digit(text[|text| - 1])
  }
  function Power(base: nat, exponent: nat): nat
    decreases exponent
  { if exponent == 0 then 1 else base * Power(base, exponent - 1) }
  function UnitPower(c: char): nat {
    if c in {'k', 'K'} then 1 else if c in {'m', 'M'} then 2
    else if c in {'g', 'G'} then 3 else if c in {'t', 'T'} then 4
    else if c == 'P' then 5 else if c == 'E' then 6 else if c == 'Z' then 7
    else if c == 'Y' then 8 else if c == 'R' then 9 else if c == 'Q' then 10 else 0
  }
  function Scale(suffix: string): nat {
    if suffix == "" then 1
    else if UnitPower(suffix[0]) == 0 then 0
    else if |suffix| == 1 || suffix[1..] == "iB" then Power(1024, UnitPower(suffix[0]))
    else if suffix[1..] == "B" || suffix[1..] == "D" then Power(1000, UnitPower(suffix[0]))
    else 0
  }
  function PrefixModifier(text: string, index: nat): S.Modifier
    requires index <= |text|
  {
    if index == |text| then S.Absolute
    else if text[index] == '<' then S.AtMost else if text[index] == '>' then S.AtLeast
    else if text[index] == '/' then S.RoundDown else if text[index] == '%' then S.RoundUp
    else S.Absolute
  }
  predicate SpaceBoundary(text: string, start: nat, end: nat)
  {
    start <= end <= |text| &&
    (forall i :: start <= i < end ==> IsSpace(text[i])) &&
    (end == |text| || !IsSpace(text[end]))
  }
  ghost predicate NumberLayout(text: string, a: nat, b: nat, c: nat, end: nat)
  {
    SpaceBoundary(text, 0, a) &&
    SpaceBoundary(text, a + (if PrefixModifier(text, a) == S.Absolute then 0 else 1), b) &&
    c == b + (if b < |text| && text[b] in {'+', '-'} then 1 else 0) &&
    c <= end <= |text| && Digits(text[c..end]) &&
    (end == |text| || !IsDigit(text[end]))
  }
  opaque ghost predicate SizeRelation(text: string, parsed: S.ParsedSize)
  {
    exists a: nat, b: nat, c: nat, end: nat ::
      NumberLayout(text, a, b, c, end) &&
      parsed.signed == (b < |text| && text[b] in {'+', '-'}) &&
      parsed.modifier == (if PrefixModifier(text, a) != S.Absolute then PrefixModifier(text, a)
                          else if parsed.signed then S.Relative else S.Absolute) &&
      parsed.value == (if b < |text| && text[b] == '-' then -1 else 1) *
      (if c < end then Decimal(text[c..end]) else 1) * Scale(text[end..]) &&
      parsed.error ==
      (if PrefixModifier(text, a) != S.Absolute && parsed.signed then MultipleModifiers()
       else if Scale(text[end..]) == 0 || (c == end && (parsed.signed || text[end..] == "")) then
         InvalidNumber(text[b..], false)
       else if parsed.value < MinSize || MaxSize < parsed.value then
         InvalidNumber(text[b..], true)
       else [])
  }
  predicate ModeAt(parsed: seq<S.ParsedSize>, limit: nat, mode: S.Modifier)
    requires limit <= |parsed|
  {
    (mode == S.Absolute && forall i :: 0 <= i < limit ==> parsed[i].modifier == S.Absolute) ||
    (exists i: nat :: i < limit && parsed[i].modifier != S.Absolute &&
                      mode == parsed[i].modifier &&
                      forall j :: i < j < limit ==> parsed[j].modifier == S.Absolute)
  }
  ghost predicate ErrorAt(parsed: seq<S.ParsedSize>, index: nat, error: W.Bytes)
    requires index < |parsed|
  {
    exists mode: S.Modifier {:trigger ModeAt(parsed, index + 1, mode)} :: ModeAt(parsed, index + 1, mode) &&
                                                                          error == (if parsed[index].signed &&
                                                                                       (exists j: nat :: j < index && parsed[j].modifier != S.Absolute)
                                                                                    then MultipleModifiers()
                                                                                    else if parsed[index].error != [] then parsed[index].error
                                                                                      else if mode in {S.RoundDown, S.RoundUp} && parsed[index].value == 0
                                                                                      then DivisionByZero() else [])
  }
  opaque ghost predicate Resolved(raw: S.TruncateCmdRaw, mode: S.Modifier, value: int, error: W.Bytes)
  {
    exists parsed: seq<S.ParsedSize> ::
      |parsed| == |raw.sizes| &&
      (forall i :: 0 <= i < |parsed| ==> SizeRelation(raw.sizes[i], parsed[i])) &&
      ModeAt(parsed, |parsed|, mode) &&
      value == (if |parsed| == 0 then 0 else parsed[|parsed| - 1].value) &&
      ((error == [] && forall i :: 0 <= i < |parsed| ==> ErrorAt(parsed, i, [])) ||
       (exists i: nat :: i < |parsed| && error != [] && ErrorAt(parsed, i, error) &&
                         forall j :: 0 <= j < i ==> ErrorAt(parsed, j, [])))
  }
  function ConfigurationError(raw: S.TruncateCmdRaw, mode: S.Modifier): W.Bytes {
    if !raw.hasReference && |raw.sizes| == 0 then MissingSize()
    else if raw.hasReference && |raw.sizes| > 0 && mode == S.Absolute then AbsoluteReference()
    else if raw.blocks && |raw.sizes| == 0 then BlocksWithoutSize()
    else if |raw.files| == 0 then MissingFile() else []
  }
  opaque function NatText(n: nat): string
    decreases n
  {
    if n < 10 then [('0' as int + n) as char]
    else NatText(n / 10) + [('0' as int + n % 10) as char]
  }
  function IntTextPart1(): W.Bytes
  {
    "-"
  }

  function IntText(n: int): string
  { if n < 0 then IntTextPart1() + NatText(-n) else NatText(n) }
  function OpenTextPart1(): W.Bytes
  {
    "truncate: cannot open "
  }

  function OpenTextPart2(): W.Bytes
  {
    " for writing: "
  }

  function OpenTextPart3(): W.Bytes
  {
    "\n"
  }

  function OpenText(quoted: W.Bytes, reason: string): W.Bytes
  {
    OpenTextPart1() + quoted + OpenTextPart2() + Utf8.Encode(reason) + OpenTextPart3()
  }
  function StatTextPart1(): W.Bytes
  {
    "truncate: cannot "
  }

  function StatTextPart2(): W.Bytes
  {
    "stat "
  }

  function StatTextPart3(): W.Bytes
  {
    "fstat "
  }

  function StatTextPart4(): W.Bytes
  {
    ": "
  }

  function StatTextPart5(): W.Bytes
  {
    "\n"
  }

  function StatText(quoted: W.Bytes, reason: string, reference: bool): W.Bytes
  {
    StatTextPart1() + (if reference then StatTextPart2() else StatTextPart3()) + quoted + StatTextPart4() +
    Utf8.Encode(reason) + StatTextPart5()
  }
  function ResizeTextPart1(): W.Bytes
  {
    "truncate: failed to truncate "
  }

  function ResizeTextPart2(): W.Bytes
  {
    " at "
  }

  function ResizeTextPart3(): W.Bytes
  {
    " bytes: "
  }

  function ResizeTextPart4(): W.Bytes
  {
    "\n"
  }

  function ResizeText(quoted: W.Bytes, size: nat, reason: string): W.Bytes
  {
    ResizeTextPart1() + quoted + ResizeTextPart2() + Utf8.Encode(NatText(size)) +
    ResizeTextPart3() + Utf8.Encode(reason) + ResizeTextPart4()
  }
  function BlockOverflowTextPart1(): W.Bytes
  {
    "truncate: overflow in "
  }

  function BlockOverflowTextPart2(): W.Bytes
  {
    " * "
  }

  function BlockOverflowTextPart3(): W.Bytes
  {
    " byte blocks for file "
  }

  function BlockOverflowTextPart4(): W.Bytes
  {
    "\n"
  }

  function BlockOverflowText(quoted: W.Bytes, delta: int, block: nat): W.Bytes
  {
    BlockOverflowTextPart1() + Utf8.Encode(IntText(delta)) + BlockOverflowTextPart2() + Utf8.Encode(NatText(block)) +
    BlockOverflowTextPart3() + quoted + BlockOverflowTextPart4()
  }
  function ExtendOverflowText(quoted: W.Bytes): W.Bytes {
    "truncate: overflow extending size of file " + quoted + "\n"
  }
  ghost function CannotOpen(path: string, err: int): W.Bytes
  {
    OpenText(C.QuoteafPathResult(path), C.CLocaleErrnoTextResult(err))
  }
  ghost function CannotStat(path: string, err: int, reference: bool): W.Bytes
  {
    StatText(C.QuoteafPathResult(path), C.CLocaleErrnoTextResult(err), reference)
  }
  ghost function TruncateError(path: string, size: nat, err: int): W.Bytes
  {
    ResizeText(C.QuoteafPathResult(path), size, C.CLocaleErrnoTextResult(err))
  }
  ghost function BlockOverflow(path: string, delta: int, block: nat): W.Bytes
  {
    BlockOverflowText(C.QuoteafPathResult(path), delta, block)
  }
  ghost function ExtendOverflow(path: string): W.Bytes {
    ExtendOverflowText(C.QuoteafPathResult(path))
  }
  opaque function AdjustedSize(mode: S.Modifier, base: nat, delta: int): int
  {
    if mode == S.Absolute then delta
    else if mode == S.AtMost then (if base < delta then base else delta)
    else if mode == S.AtLeast then (if base > delta then base else delta)
    else if mode == S.RoundDown && delta > 0 then base - base % delta
    else if mode == S.RoundUp && delta > 0 then
      base + (if base % delta == 0 then 0 else delta - base % delta)
    else base + delta
  }
  function Clamped(n: int): nat { if n < 0 then 0 else n }
  function BlockSize(status: W.FileStatus): nat {
    var block := status.storage.preferredIoBlockBytes;
    if 0 < block <= 2305843009213693952 then block else 4096
  }
  datatype FileState = FileState(fs: W.FileSystem, cursor: nat, errors: W.Bytes, failed: bool)

  opaque ghost predicate OpenRelation(
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    now: int, path: string, noCreate: bool,
    before: W.FileSystem, after: W.FileSystem, isOpen: bool, err: int
  )
  {
    if noCreate then
      exists found: bool, queryErr: int ::
        C.PathExistsSpec(before, observations, path, true, found, queryErr) &&
        (if found then C.CreateFileSpec(before, now, observations, after, path, isOpen, err)
         else after == before && !isOpen && err == (if queryErr == 2 then 0 else queryErr))
    else C.CreateFileSpec(before, now, observations, after, path, isOpen, err)
  }
  datatype StatusObservations = StatusObservations(times: W.StatusTimeObservations,
                                                   failures: (W.NativeFailureRequest) -> int)

  opaque ghost predicate StatusRelation(
    observations: StatusObservations, cursor: nat, cursor2: nat, fs: W.FileSystem,
    path: string, ok: bool, status: W.FileStatus, err: int
  )
  {
    C.GetFileStatusSpec(observations.times, observations.failures, cursor, cursor2, fs, path, true, ok, status, err)
  }
  opaque ghost predicate Truncation(
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    now: int, path: string, size: nat, before: W.FileSystem, after: W.FileSystem, error: W.Bytes
  )
  {
    exists ok: bool, err: int ::
      C.TruncateFileSpec(before, now, observations, after, path, size, ok, err) &&
      error == (if ok then [] else TruncateError(path, size, err))
  }
  opaque ghost predicate ResizeOutcome(
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: StatusObservations, now: int, path: string,
    mode: S.Modifier, delta: int, blocks: bool, reference: int,
    before: W.FileSystem, cursor: nat, after: W.FileSystem, cursor2: nat,
    error: W.Bytes,
    status: W.FileStatus, statOk: bool, statErr: int
  )
  {
    (if blocks || (mode != S.Absolute && reference < 0) then
       StatusRelation(statusTimes, cursor, cursor2, before, path, statOk, status, statErr)
     else cursor2 == cursor && statOk && status == W.DEFAULT_FILE_STATUS && statErr == 0) &&
    (if !statOk then after == before && error == CannotStat(path, statErr, false)
     else
       var scaled := delta * (if blocks then BlockSize(status) else 1);
       var base := if reference >= 0 then reference as nat else status.storage.size;
       var requested := AdjustedSize(mode, base, scaled);
       if scaled < MinSize || MaxSize < scaled then
         after == before && error == BlockOverflow(path, delta, BlockSize(status))
       else if requested > MaxSize then after == before && error == ExtendOverflow(path)
       else Truncation(observations, now, path, Clamped(requested), before, after, error))
  }
  opaque ghost predicate ResizeRelation(
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: StatusObservations, now: int, path: string,
    mode: S.Modifier, delta: int, blocks: bool, reference: int,
    before: W.FileSystem, cursor: nat, after: W.FileSystem, cursor2: nat,
    error: W.Bytes
  )
  {
    exists status: W.FileStatus, statOk: bool, statErr: int ::
      ResizeOutcome(observations, statusTimes, now, path, mode, delta, blocks, reference,
                    before, cursor, after, cursor2, error, status, statOk, statErr)
  }
  opaque ghost predicate FileStep(
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: StatusObservations, now: int, path: string,
    noCreate: bool, mode: S.Modifier, delta: int, blocks: bool, reference: int,
    before: W.FileSystem, cursor: nat, after: W.FileSystem, cursor2: nat, error: W.Bytes
  )
  {
    exists openedFs: W.FileSystem, isOpen: bool, openErr: int ::
      OpenRelation(observations, now, path, noCreate, before, openedFs, isOpen, openErr) &&
      (if !isOpen then after == openedFs && cursor2 == cursor &&
                       error == (if openErr == 0 then [] else CannotOpen(path, openErr))
       else ResizeRelation(observations, statusTimes, now, path, mode, delta, blocks, reference,
                           openedFs, cursor, after, cursor2, error))
  }
  opaque ghost predicate FileRelation(
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: StatusObservations, now: int, path: string,
    noCreate: bool, mode: S.Modifier, delta: int, blocks: bool, reference: int,
    before: FileState, after: FileState
  )
  {
    exists error: W.Bytes ::
      FileStep(observations, statusTimes, now, path, noCreate, mode, delta, blocks, reference,
               before.fs, before.cursor, after.fs, after.cursor, error) &&
      after.errors == before.errors + error && after.failed == (before.failed || error != [])
  }
  opaque ghost predicate FilesRelation(
    raw: S.TruncateCmdRaw, mode: S.Modifier, delta: int, reference: int,
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: StatusObservations, now: int,
    before: W.FileSystem, cursor: nat, after: W.FileSystem, cursor2: nat,
    errors: W.Bytes, exit: int
  )
  {
    exists states: seq<FileState> :: |states| == |raw.files| + 1 &&
                                     states[0] == FileState(before, cursor, [], false) &&
                                     states[|raw.files|].fs == after && states[|raw.files|].cursor == cursor2 &&
                                     states[|raw.files|].errors == errors && exit == (if states[|raw.files|].failed then 1 else 0) &&
                                     forall i :: 0 <= i < |raw.files| ==>
                                                   FileRelation(observations, statusTimes, now, raw.files[i], raw.noCreate,
                                                                mode, delta, raw.blocks, reference, states[i], states[i + 1])
  }
  opaque ghost predicate RunRelation(
    raw: S.TruncateCmdRaw, mode: S.Modifier, value: int,
    observations: (W.TrustedFilesystemRequest) -> W.TrustedFilesystemResult,
    statusTimes: StatusObservations, now: int,
    before: W.FileSystem, cursor: nat, after: W.FileSystem, cursor2: nat,
    errors: W.Bytes, exit: int
  )
  {
    if raw.hasReference then
      exists ok: bool, status: W.FileStatus, err: int, next: nat ::
        StatusRelation(statusTimes, cursor, next, before, raw.reference, ok, status, err) &&
        (if !ok then after == before && cursor2 == next && exit == 1 &&
                     errors == CannotStat(raw.reference, err, true)
         else FilesRelation(raw, mode, if |raw.sizes| == 0 then status.storage.size else value,
                            if |raw.sizes| == 0 then -1 else status.storage.size,
                            observations, statusTimes, now, before, next, after, cursor2, errors, exit))
    else FilesRelation(raw, mode, value, -1,
                       observations, statusTimes, now, before, cursor, after, cursor2, errors, exit)
  }
  opaque ghost predicate DiagnosticResult(
    before: W.Bytes, after: W.Bytes,
    observations: (W.TrustedStreamRequest) -> W.TrustedStreamResult,
    message: W.Bytes, err: int
  )
  {
    if message == [] then after == before && err == 0
    else
      var observed := observations(W.StreamWriteStderr(before, message));
      observed.StreamWriteResult? &&
      C.WriteStderrSpec(before, observations, after, message, observed.committed, err) &&
      err == observed.err
  }

  opaque ghost predicate HelpResult(
    mode: S.Mode, beforeOut: W.Bytes, afterOut: W.Bytes,
    beforeErr: W.Bytes, afterErr: W.Bytes,
    observations: (W.TrustedStreamRequest) -> W.TrustedStreamResult, exit: int
  )
  {
    var payload := if mode == S.Help then HelpText() else VersionText();
    var observed := observations(W.StreamWriteStdout(beforeOut, payload));
    observed.StreamWriteResult? &&
    C.WriteStdoutSpec(beforeOut, observations, afterOut, payload, observed.committed, observed.err) &&
    var diagnostic := if observed.err == 0 then [] else WriteError(observed.err);
    var diagnosticObservation := observations(W.StreamWriteStderr(beforeErr, diagnostic));
    (if diagnostic == [] then afterErr == beforeErr
     else diagnosticObservation.StreamWriteResult? &&
          DiagnosticResult(beforeErr, afterErr, observations, diagnostic, diagnosticObservation.err)) &&
    exit == (if observed.err == 0 then 0 else 1)
  }

  twostate predicate ExecutionRelation(
    raw: S.TruncateCmdRaw, mode: S.Modifier, value: int, error: W.Bytes, io: BenchIO.IO, exit: int
  )
    reads io.fsRegion, io.stdoutRegion, io.stderrRegion, io.statusObservationsRegion,
          io.nowRegion, io.trustedFilesystemRegion, io.trustedNativeFailuresRegion, io.trustedStreamsRegion
  {
    if error != [] then
      io.fs() == old(io.fs()) && io.statusCursor() == old(io.statusCursor()) &&
      io.stdout() == old(io.stdout()) && exit == 1 &&
      (exists err: int :: DiagnosticResult(old(io.stderr()), io.stderr(),
                                           old(io.trustedStreams()), error, err))
    else if raw.mode != S.Run then
      io.fs() == old(io.fs()) && io.statusCursor() == old(io.statusCursor()) &&
      HelpResult(raw.mode, old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(),
                 old(io.trustedStreams()), exit)
    else if raw.parseError != [] then
      io.fs() == old(io.fs()) && io.statusCursor() == old(io.statusCursor()) &&
      io.stdout() == old(io.stdout()) && exit == 1 &&
      (exists err: int :: DiagnosticResult(old(io.stderr()), io.stderr(),
                                           old(io.trustedStreams()), raw.parseError, err))
    else if ConfigurationError(raw, mode) != [] then
      io.fs() == old(io.fs()) && io.statusCursor() == old(io.statusCursor()) &&
      io.stdout() == old(io.stdout()) &&
      exit == 1 &&
      (exists err: int :: DiagnosticResult(old(io.stderr()), io.stderr(),
                                           old(io.trustedStreams()), ConfigurationError(raw, mode), err))
    else
      exists errors: W.Bytes, normalExit: int, diagnosticErr: int ::
        io.stdout() == old(io.stdout()) &&
        DiagnosticResult(old(io.stderr()), io.stderr(), old(io.trustedStreams()), errors, diagnosticErr) &&
        exit == (if diagnosticErr == 0 then normalExit else 1) &&
        RunRelation(raw, mode, value, old(io.trustedFilesystem()), StatusObservations(io.statusObservations(),io.trustedNativeFailures()), old(io.now()),
                    old(io.fs()), old(io.statusCursor()), io.fs(), io.statusCursor(), errors, normalExit)
  }
  twostate predicate Spec(raw: S.TruncateCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdoutRegion, io.stderrRegion, io.statusObservationsRegion,
          io.nowRegion, io.trustedFilesystemRegion, io.trustedNativeFailuresRegion, io.trustedStreamsRegion
  {
    exists mode: S.Modifier, value: int, error: W.Bytes ::
      Resolved(raw, mode, value, error) && ExecutionRelation(raw, mode, value, error, io, exit)
  }

  function LongOption(token: string): string {
    var eq := CliModel.FindChar(token, '=');
    var name := if eq >= 0 then token[..eq] else token;
    if |name| <= 2 then name else
    var word := name[2..];
    if CliModel.HasPrefix("no-create", word) then "--no-create"
    else if CliModel.HasPrefix("io-blocks", word) then "--io-blocks"
    else if CliModel.HasPrefix("reference", word) then "--reference"
    else if CliModel.HasPrefix("size", word) then "--size"
    else if CliModel.HasPrefix("help", word) then "--help"
    else if CliModel.HasPrefix("version", word) then "--version" else name
  }
  ghost predicate UnknownShortRelation(text: string, character: char) {
    (character == '?' && forall i :: 0 <= i < |text| ==> text[i] in {'c', 'o'}) ||
    (exists index: nat :: index < |text| && text[index] !in {'c', 'o'} &&
                          character == text[index] && forall i :: 0 <= i < index ==> text[i] in {'c', 'o'})
  }
  function ParseErrorTextPart1(): W.Bytes
  {
    "truncate: option '"
  }

  function ParseErrorTextPart2(): W.Bytes
  {
    "' requires an argument\n"
  }

  function ParseErrorTextPart3(): W.Bytes
  {
    "truncate: option requires an argument -- '"
  }

  function ParseErrorTextPart4(): W.Bytes
  {
    "'\n"
  }

  function ParseErrorTextPart5(): W.Bytes
  {
    "' is ambiguous; possibilities: '--no-create' '--io-blocks' '--reference' '--size' '--help' '--version'\n"
  }

  function ParseErrorTextPart6(): W.Bytes
  {
    "' doesn't allow an argument\n"
  }

  function ParseErrorTextPart7(): W.Bytes
  {
    "truncate: unrecognized option '"
  }

  function ParseErrorTextPart8(): W.Bytes
  {
    "truncate: invalid option -- '"
  }

  function ParseErrorText(err: CliTypes.ParseError, invalidShort: char): W.Bytes
    requires |err.rawToken| > 1 ==> UnknownShortRelation(err.rawToken[1..], invalidShort)
  {
    var long := |err.rawToken| > 2 && err.rawToken[0] == '-' && err.rawToken[1] == '-';
    var detail :=
      if err.kind == CliTypes.MissingValue then
        (if long then
           ParseErrorTextPart1() + Utf8.Encode(LongOption(err.rawToken)) + ParseErrorTextPart2()
         else
           ParseErrorTextPart3() +
           (if |err.rawToken| > 1 then Utf8.Encode([err.rawToken[|err.rawToken| - 1]]) else []) + ParseErrorTextPart4())
      else if err.kind == CliTypes.Ambiguous then
        ParseErrorTextPart1() + Utf8.Encode(err.rawToken) +
        ParseErrorTextPart5()
      else if err.kind == CliTypes.UnexpectedValue then
        ParseErrorTextPart1() + Utf8.Encode(LongOption(err.rawToken)) + ParseErrorTextPart6()
      else if long then
        ParseErrorTextPart7() + Utf8.Encode(err.rawToken) + ParseErrorTextPart4()
      else
        ParseErrorTextPart8() +
        (if |err.rawToken| > 1 then Utf8.EncodeChar(invalidShort)[..1] else []) + ParseErrorTextPart4();
    detail + UsageHint()
  }
}
