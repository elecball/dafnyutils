include "DdSchema.dfy"
include "../../../core/IO.dfy"
include "../../../core/Utf8.dfy"
include "../../../core/StringEscaping.dfy"

module DdSpec {
  import BenchIO
  import BW = BenchWorld
  import C = IOContract
  import S = DdSchema
  import CliTypes
  import Utf8 = Utf8Semantics
  import Q = StringEscaping

  function HelpText(): BW.Bytes {
    "Usage: dd [OPERAND]...\n" +
    "  or:  dd OPTION\n" +
    "Copy a file, converting and formatting according to the operands.\n" +
    "\n" +
    "  bs=BYTES        read and write up to BYTES bytes at a time (default: 512);\n" +
    "                  overrides ibs and obs\n" +
    "  cbs=BYTES       convert BYTES bytes at a time\n" +
    "  conv=CONVS      convert the file as per the comma separated symbol list\n" +
    "  count=N         copy only N input blocks\n" +
    "  ibs=BYTES       read up to BYTES bytes at a time (default: 512)\n" +
    "  if=FILE         read from FILE instead of standard input\n" +
    "  iflag=FLAGS     read as per the comma separated symbol list\n" +
    "  obs=BYTES       write BYTES bytes at a time (default: 512)\n" +
    "  of=FILE         write to FILE instead of standard output\n" +
    "  oflag=FLAGS     write as per the comma separated symbol list\n" +
    "  seek=N          (or oseek=N) skip N obs sized output blocks\n" +
    "  skip=N          (or iseek=N) skip N ibs sized input blocks\n" +
    "  status=LEVEL    The LEVEL of information to print to standard error;\n" +
    "                  'none' suppresses everything but error messages,\n" +
    "                  'noxfer' suppresses the final transfer statistics,\n" +
    "                  'progress' shows periodic transfer statistics\n" +
    "\n" +
    "N and BYTES may be followed by the following multiplicative suffixes:\n" +
    "c=1, w=2, b=512, kB=1000, K=1024, MB=1000*1000, M=1024*1024, xM=M,\n" +
    "GB=1000*1000*1000, G=1024*1024*1024, and so on for T, P, E, Z, Y, R, Q.\n" +
    "Binary prefixes can be used, too: KiB=K, MiB=M, and so on.\n" +
    "If N ends in 'B', it counts bytes not blocks.\n" +
    "\n" +
    "Each CONV symbol may be:\n" +
    "\n" +
    "  ascii     from EBCDIC to ASCII\n" +
    "  ebcdic    from ASCII to EBCDIC\n" +
    "  ibm       from ASCII to alternate EBCDIC\n" +
    "  block     pad newline-terminated records with spaces to cbs-size\n" +
    "  unblock   replace trailing spaces in cbs-size records with newline\n" +
    "  lcase     change upper case to lower case\n" +
    "  ucase     change lower case to upper case\n" +
    "  sparse    try to seek rather than write all-NUL output blocks\n" +
    "  swab      swap every pair of input bytes\n" +
    "  sync      pad every input block with NULs to ibs-size; when used\n" +
    "            with block or unblock, pad with spaces rather than NULs\n" +
    "  excl      fail if the output file already exists\n" +
    "  nocreat   do not create the output file\n" +
    "  notrunc   do not truncate the output file\n" +
    "  noerror   continue after read errors\n" +
    "  fdatasync  physically write output file data before finishing\n" +
    "  fsync     likewise, but also write metadata\n" +
    "\n" +
    "Each FLAG symbol may be:\n" +
    "\n" +
    "  append    append mode (makes sense only for output; conv=notrunc suggested)\n" +
    "  direct    use direct I/O for data\n" +
    "  directory  fail unless a directory\n" +
    "  dsync     use synchronized I/O for data\n" +
    "  sync      likewise, but also for metadata\n" +
    "  fullblock  accumulate full blocks of input (iflag only)\n" +
    "  nonblock  use non-blocking I/O\n" +
    "  noatime   do not update access time\n" +
    "  nocache   Request to drop cache.  See also oflag=sync\n" +
    "  noctty    do not assign controlling terminal from file\n" +
    "  nofollow  do not follow symlinks\n" +
    "\n" +
    "Sending a USR1 signal to a running 'dd' process makes it\n" +
    "print I/O statistics to standard error and then resume copying.\n" +
    "\n" +
    "Options are:\n" +
    "\n" +
    "      --help\n" +
    "         display this help and exit\n" +
    "      --version\n" +
    "         output version information and exit\n" +
    "\n" +
    "Report bugs to: bug-coreutils@gnu.org\n" +
    "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n" +
    "General help using GNU software: <https://www.gnu.org/gethelp/>\n" +
    "Report any translation bugs to <https://translationproject.org/team/>\n" +
    "Full documentation <https://www.gnu.org/software/coreutils/dd>\n" +
    "or available locally via: info '(coreutils) dd invocation'\n"
  }
  function VersionText(): BW.Bytes {
    "dd (coreutils) 9.10.13-2cf49\n" +
    "Copyright (C) 2026 Free Software Foundation, Inc.\n" +
    "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n" +
    "This is free software: you are free to change and redistribute it.\n" +
    "There is NO WARRANTY, to the extent permitted by law.\n" +
    "\n" +
    "Written by Paul Rubin, David MacKenzie, and Stuart Kemp.\n"
  }

  function TryHelp(): BW.Bytes { "Try 'dd --help' for more information.\n" }
  function WarningText(): BW.Bytes {
    "dd: warning: '0x' is a zero multiplier; use '00x' if that is intended\n"
  }
  function Warnings(n: nat): BW.Bytes {
    seq(n * |WarningText()|, i => WarningText()[i % |WarningText()|])
  }
  function Quoted(text: string): BW.Bytes { Q.SpecQuoteAfBytes(Utf8.Encode(text)) }
  function LocaleQuoted(text: string): BW.Bytes { Q.SpecLocaleQuoteBytes(Utf8.Encode(text)) }

  function ErrorText(error: S.Error): BW.Bytes {
    match error
    case None => []
    case Operand(text) => "dd: unrecognized operand " + Quoted(text) + "\n" + TryHelp()
    case Conversion(text) => "dd: invalid conversion: " + LocaleQuoted(text) + "\n" + TryHelp()
    case InputFlag(text) => "dd: invalid input flag: " + LocaleQuoted(text) + "\n" + TryHelp()
    case OutputFlag(text) => "dd: invalid output flag: " + LocaleQuoted(text) + "\n" + TryHelp()
    case Status(text) => "dd: invalid status level: " + LocaleQuoted(text) + "\n" + TryHelp()
    case Number(text, overflow) => "dd: invalid number: " + Quoted(text) +
    (if overflow then ": Value too large for defined data type" else "") + "\n"
    case CaseConflict => "dd: cannot combine lcase and ucase\n"
    case OutsideScope => "dd: operand is outside this benchmark's documented scope\n"
  }

  function ParseErrorText(err: CliTypes.ParseError): BW.Bytes {
    var option := err.rawToken[..S.Find(err.rawToken, '=')];
    var canonical := if |option| > 2 && S.Starts("--help", option) then "--help"
                     else if |option| > 2 && S.Starts("--version", option) then "--version" else option;
    if err.kind == CliTypes.UnexpectedValue then
      "dd: option '" + Utf8.Encode(canonical) +
      "' doesn't allow an argument\n" + TryHelp()
    else if |err.rawToken| > 2 && err.rawToken[..2] == "--" then
      "dd: unrecognized option '" + Utf8.Encode(err.rawToken) + "'\n" + TryHelp()
    else if |err.rawToken| > 1 then
      "dd: invalid option -- '" + Utf8.EncodeChar(err.rawToken[1])[..1] + "'\n" + TryHelp()
    else TryHelp()
  }

  function ReadDiagnostic(message: string): BW.Bytes {
    "dd: error reading 'standard input': " + Utf8.Encode(message) + "\n"
  }
  function WriteDiagnostic(message: string, buffered: bool): BW.Bytes {
    (if buffered then "dd: writing to 'standard output': " else "dd: error writing 'standard output': ") + Utf8.Encode(message) + "\n"
  }
  function EarlyWriteDiagnostic(message: string): BW.Bytes {
    "dd: write error: " + Utf8.Encode(message) + "\n"
  }

  ghost function ReadError(err: int): BW.Bytes {
    if err == 0 then [] else
    ReadDiagnostic(C.CLocaleErrnoTextResult(err))
  }
  ghost function WriteError(err: int, buffered: bool): BW.Bytes {
    if err == 0 then [] else
    WriteDiagnostic(C.CLocaleErrnoTextResult(err), buffered)
  }
  ghost function EarlyWriteError(err: int): BW.Bytes {
    if err == 0 then [] else
    EarlyWriteDiagnostic(C.CLocaleErrnoTextResult(err))
  }

  function ReadLimit(raw: S.DdCmdRaw, ordinal: nat): nat {
    if raw.count < 0 || !raw.countBytes || ordinal < raw.count / raw.ibs then raw.ibs
    else raw.count % raw.ibs
  }
  predicate CountAllows(raw: S.DdCmdRaw, ordinal: nat) {
    raw.count < 0 ||
    ordinal < (if raw.countBytes then raw.count / raw.ibs + (if raw.count % raw.ibs == 0 then 0 else 1) else raw.count)
  }

  function Direct(raw: S.DdCmdRaw): bool { raw.direct && !raw.swab }

  function Ready(length: nat, swab: bool): nat {
    if swab then length - length % 2 else length
  }
  function CaseByte(raw: S.DdCmdRaw, byte: BW.RawByte): BW.RawByte {
    if raw.lower && 'A' <= byte <= 'Z' then (byte as int + 32) as char
    else if raw.upper && 'a' <= byte <= 'z' then (byte as int - 32) as char
    else byte
  }
  function SourceIndex(index: nat, length: nat, swab: bool): nat
    requires index < length
    ensures SourceIndex(index, length, swab) < length
  {
    if !swab then index
    else if index % 2 == 1 then index - 1
    else if index + 1 < length then index + 1
    else index
  }
  // Independent global adjacent-pair permutation followed by byte classification.
  predicate Transformed(raw: S.DdCmdRaw, data: BW.Bytes, output: BW.Bytes) {
    |output| == |data| &&
    forall i: nat | i < |data| :: output[i] == CaseByte(raw, data[SourceIndex(i, |data|, raw.swab)])
  }
  predicate Padded(raw: S.DdCmdRaw, input: BW.Bytes, output: BW.Bytes) {
    if input == [] then output == []
    else (|output| == (if raw.sync then raw.ibs else |input|) &&
          |input| <= |output| && output[..|input|] == input &&
          forall i: nat | |input| <= i < |output| :: output[i] == '\0')
  }

  // A finite partition of actual bounded read observations. The mathematical
  // cuts, rather than an executable parser or fullblock state machine, describe
  // which positive prefixes comprise one input record.
  ghost predicate ReadProgress(cuts: seq<nat>, errors: seq<int>, limit: nat, j: nat) {
    j < |errors| && |cuts| == |errors| + 1 &&
    errors[j] == 0 && cuts[j] < cuts[j + 1] < limit
  }

  opaque ghost predicate ReadAt(
    before: BW.Bytes, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    limit: nat, cuts: seq<nat>, states: seq<BW.Bytes>, errors: seq<int>, j: nat
  ) {
    j < |errors| && |cuts| == |errors| + 1 && |states| == |cuts| &&
    cuts[j] <= cuts[j + 1] <= |before| && cuts[j] < limit &&
    C.ReadStdinChunkSpec(states[j], streams, states[j + 1], limit - cuts[j],
                         before[cuts[j]..cuts[j + 1]], errors[j]) &&
    (j + 1 < |errors| ==> errors[j] == 0 && cuts[j] < cuts[j + 1] < limit)
  }

  opaque ghost predicate ReadPartition(
    before: BW.Bytes, after: BW.Bytes,
    streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    limit: nat, fullblock: bool, data: BW.Bytes, err: int,
    cuts: seq<nat>, states: seq<BW.Bytes>, errors: seq<int>
  ) {
    0 < limit <= 9223372036854775806 && |errors| > 0 &&
    |cuts| == |errors| + 1 && |states| == |cuts| && cuts[0] == 0 &&
    cuts[|errors|] <= |before| && cuts[|errors|] <= limit &&
    states[0] == before && states[|errors|] == after &&
    err == errors[|errors| - 1] &&
    data == (if err == 0 then before[..cuts[|errors|]] else []) &&
    (!fullblock ==> |errors| == 1) &&
    (err != 0 || cuts[|errors|] == limit ||
     cuts[|errors|] == cuts[|errors| - 1] || !fullblock) &&
    forall j: nat | j < |errors| :: ReadAt(before, streams, limit, cuts, states, errors, j)
  }
  opaque ghost predicate BlockRead(
    before: BW.Bytes, after: BW.Bytes,
    streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    limit: nat, fullblock: bool, data: BW.Bytes, err: int
  ) {
    exists cuts: seq<nat>, states: seq<BW.Bytes>, errors: seq<int> ::
      ReadPartition(before, after, streams, limit, fullblock, data, err, cuts, states, errors)
  }

  datatype Record = Record(data: BW.Bytes, err: int)
  datatype Write = Write(end: nat, readCount: nat, final: bool, committed: nat, err: int)

  function BufferedFailure(raw: S.DdCmdRaw, writes: seq<Write>): bool {
    !Direct(raw) && |writes| > 0 &&
    (!writes[|writes| - 1].final || writes[|writes| - 1].end % raw.obs == 0)
  }

  opaque ghost predicate InputAt(
    raw: S.DdCmdRaw, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    records: seq<Record>, states: seq<BW.Bytes>, data: BW.Bytes, cuts: seq<nat>, i: nat
  ) {
    i < |records| && |states| == |records| + 1 && |cuts| == |states| &&
    CountAllows(raw, i) && cuts[i] <= cuts[i + 1] <= |data| &&
    BlockRead(states[i], states[i + 1], streams, ReadLimit(raw, i), raw.fullblock,
              records[i].data, records[i].err) &&
    Padded(raw, records[i].data, data[cuts[i]..cuts[i + 1]]) &&
    (i + 1 < |records| ==> records[i].err == 0 && records[i].data != [])
  }

  ghost predicate InputPartition(
    raw: S.DdCmdRaw, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    before: BW.Bytes, after: BW.Bytes, records: seq<Record>, states: seq<BW.Bytes>,
    data: BW.Bytes, cuts: seq<nat>
  ) {
    |states| == |records| + 1 && |cuts| == |states| &&
    states[0] == before && states[|records|] == after &&
    cuts[0] == 0 && cuts[|records|] == |data| &&
    forall i: nat | i < |records| :: InputAt(raw, streams, records, states, data, cuts, i)
  }

  predicate InputEnded(raw: S.DdCmdRaw, records: seq<Record>) {
    !CountAllows(raw, |records|) ||
    (|records| > 0 && (records[|records| - 1].err != 0 || records[|records| - 1].data == []))
  }

  // Output partitions are fixed by record boundaries for bs without a
  // translation, and by obs-sized intervals for the reblocking path. readCount
  // identifies the least input prefix making that interval available; it is an
  // external consumption boundary, not an implementation accumulator.
  predicate WriteBoundary(
    raw: S.DdCmdRaw, records: seq<Record>, dataCuts: seq<nat>, length: nat,
    ordinal: nat, start: nat, end: nat, readCount: nat, final: bool
  ) {
    |dataCuts| == |records| + 1 && start < end <= length &&
    0 < readCount <= |records| &&
    (if Direct(raw) then
       !final && start == dataCuts[readCount - 1] && end == dataCuts[readCount]
     else if final then
       InputEnded(raw, records) && readCount == |records| && end == length &&
       end - start <= raw.obs && Ready(length, raw.swab) < start + raw.obs
     else
       start == ordinal * raw.obs && end == (ordinal + 1) * raw.obs &&
       Ready(dataCuts[readCount - 1], raw.swab) < end <= Ready(dataCuts[readCount], raw.swab))
  }

  opaque ghost predicate OutputAt(
    raw: S.DdCmdRaw, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    records: seq<Record>, dataCuts: seq<nat>, output: BW.Bytes,
    writes: seq<Write>, states: seq<BW.Bytes>, cuts: seq<nat>, j: nat
  ) {
    j < |writes| && |dataCuts| == |records| + 1 && |states| == |writes| + 1 && |cuts| == |states| &&
    cuts[j] < cuts[j + 1] <= cuts[|writes|] <= |output| && cuts[j + 1] == writes[j].end &&
    WriteBoundary(raw, records, dataCuts, |output|, j, cuts[j], cuts[j + 1], writes[j].readCount, writes[j].final) &&
    C.WriteStdoutSpec(states[j], streams, states[j + 1], output[cuts[j]..cuts[j + 1]],
                      writes[j].committed, writes[j].err) &&
    (j + 1 < |writes| ==> writes[j].err == 0) &&
    (writes[j].final ==> j + 1 == |writes|)
  }

  ghost predicate OutputPartition(
    raw: S.DdCmdRaw, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    before: BW.Bytes, after: BW.Bytes, records: seq<Record>, dataCuts: seq<nat>,
    output: BW.Bytes, writes: seq<Write>, states: seq<BW.Bytes>, cuts: seq<nat>
  ) {
    |dataCuts| == |records| + 1 && |output| == dataCuts[|records|] &&
    |states| == |writes| + 1 && |cuts| == |states| &&
    states[0] == before && states[|writes|] == after && cuts[0] == 0 &&
    cuts[|writes|] <= |output| &&
    forall j: nat | j < |writes| :: OutputAt(raw, streams, records, dataCuts, output, writes, states, cuts, j)
  }

  ghost predicate CopyRelation(
    raw: S.DdCmdRaw, streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
    preIn: BW.Bytes, postIn: BW.Bytes, preOut: BW.Bytes, postOut: BW.Bytes,
    data: BW.Bytes, output: BW.Bytes, records: seq<Record>, inputStates: seq<BW.Bytes>,
    dataCuts: seq<nat>, writes: seq<Write>, outputStates: seq<BW.Bytes>, outputCuts: seq<nat>,
    readErr: int, writeErr: int
  ) {
    InputPartition(raw, streams, preIn, postIn, records, inputStates, data, dataCuts) &&
    OutputPartition(raw, streams, preOut, postOut, records, dataCuts, output, writes, outputStates, outputCuts) &&
    readErr == (if |records| == 0 then 0 else records[|records| - 1].err) &&
    writeErr == (if |writes| == 0 then 0 else writes[|writes| - 1].err) &&
    (if writeErr == 0 then InputEnded(raw, records) && outputCuts[|writes|] == |output|
     else |writes| > 0 && writes[|writes| - 1].readCount == |records|)
  }

  twostate predicate Spec(raw: S.DdCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    if raw.mode != S.Copy || raw.error != S.None then
      exists out: BW.Bytes, err: BW.Bytes, n: nat, we: int, ne: nat, ee: int ::
        out == (if raw.mode == S.Help then HelpText() else if raw.mode == S.Version then VersionText() else []) &&
        err == (if raw.mode == S.Copy then Warnings(raw.warnings) + ErrorText(raw.error) else []) &&
        C.WriteStdoutSpec(old(io.stdout()), io.trustedStreams(), io.stdout(), out, n, we) &&
        C.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(), err + EarlyWriteError(we), ne, ee) &&
        exit == (if we != 0 || ee != 0 || (raw.error != S.None && raw.mode == S.Copy) then 1 else 0)
    else
      exists data: BW.Bytes, output: BW.Bytes, records: seq<Record>, ins: seq<BW.Bytes>,
        dc: seq<nat>, writes: seq<Write>, outs: seq<BW.Bytes>, oc: seq<nat>,
        re: int, we: int, committed: nat, ee: int ::
        CopyRelation(raw, io.trustedStreams(), old(io.stdin()), io.stdin(), old(io.stdout()), io.stdout(),
                     data, output, records, ins, dc, writes, outs, oc, re, we) &&
        Transformed(raw, data, output) &&
        C.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                          Warnings(raw.warnings) + ReadError(re) + WriteError(we, BufferedFailure(raw, writes)), committed, ee) &&
        exit == (if re == 0 && we == 0 && ee == 0 then 0 else 1)
  }
}
