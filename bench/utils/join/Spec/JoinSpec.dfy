include "JoinDataSpec.dfy"
include "../../../core/IO.dfy"
include "../../../core/StringEscaping.dfy"

module JoinSpec {
  import S = JoinSchema
  import D = JoinDataSpec
  import BW = BenchWorld
  import BenchIO
  import Errno = Errnos
  import C = IOContract
  import R = Results
  import U = Utf8Semantics
  import E = StringEscaping
  import CliTypes

  function HelpText(): BW.Bytes {
    U.Encode("Usage: join [OPTION]... FILE1 FILE2\nFor each pair of input lines with identical join fields, write a line to\nstandard output.  The default join field is the first, delimited by blanks.\n\nWhen FILE1 or FILE2 (not both) is -, read standard input.\n  -a FILENUM\n         also print unpairable lines from file FILENUM,\n         where FILENUM is 1 or 2, corresponding to FILE1 or FILE2\n  -e STRING\n         replace missing (empty) input fields with STRING;\n         I.e., missing fields specified with '-12jo' options\n  -i, --ignore-case\n         ignore differences in case when comparing fields\n  -j FIELD\n         equivalent to '-1 FIELD -2 FIELD'\n  -o FORMAT\n         obey FORMAT while constructing output line\n  -t CHAR\n         use CHAR as input and output field separator\n  -v FILENUM\n         like -a FILENUM, but suppress joined output lines\n  -1 FIELD\n         join on this FIELD of file 1\n  -2 FIELD\n         join on this FIELD of file 2\n      --check-order\n         check that the input is correctly sorted, even\n         if all input lines are pairable\n      --nocheck-order\n         do not check that the input is correctly sorted\n      --header\n         treat the first line in each file as field headers,\n         print them without trying to pair them\n  -z, --zero-terminated\n         line delimiter is NUL, not newline\n      --help\n         display this help and exit\n      --version\n         output version information and exit\n\nUnless -t CHAR is given, leading blanks separate fields and are ignored,\nelse fields are separated by CHAR.  Any FIELD is a field number counted\nfrom 1.  FORMAT is one or more comma or blank separated specifications,\neach being 'FILENUM.FIELD' or '0'.  Default FORMAT outputs the join field,\nthe remaining fields from FILE1, the remaining fields from FILE2, all\nseparated by CHAR.  If FORMAT is the keyword 'auto', then the first\nline of each file determines the number of fields output for each line.\n\nImportant: FILE1 and FILE2 must be sorted on the join fields.\nE.g., use \"sort -k 1b,1\" if 'join' has no options,\nor use \"join -t ''\" if 'sort' has no options.\nComparisons honor the rules specified by 'LC_COLLATE'.\nIf the input is not sorted and some lines cannot be joined, a\nwarning message will be given.\n\nReport bugs to: bug-coreutils@gnu.org\nGNU coreutils home page: <https://www.gnu.org/software/coreutils/>\nGeneral help using GNU software: <https://www.gnu.org/gethelp/>\nReport any translation bugs to <https://translationproject.org/team/>\nFull documentation <https://www.gnu.org/software/coreutils/join>\nor available locally via: info '(coreutils) join invocation'\n")
  }
  function VersionText(): BW.Bytes {
    U.Encode("join (GNU coreutils) 9.10.13-2cf49\nCopyright (C) 2026 Free Software Foundation, Inc.\nLicense GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\nThis is free software: you are free to change and redistribute it.\nThere is NO WARRANTY, to the extent permitted by law.\n\nWritten by Mike Haertel.\n")
  }

  const TryHelp: BW.Bytes := "Try 'join --help' for more information.\n"
  const DisorderSummary: BW.Bytes := "join: input is not in sorted order\n"
  const BothStdin: BW.Bytes := "join: both files cannot be standard input\n"

  function NatText(n: nat): BW.Bytes
    decreases n
  { if n < 10 then [('0' as int+n) as char] else NatText(n/10)+[('0' as int+n%10) as char] }
  function Quote(text: string): BW.Bytes { E.SpecLocaleQuoteBytes(U.Encode(text)) }
  function ParseErrorText(err: CliTypes.ParseError): BW.Bytes {
    var token := U.Encode(err.rawToken);
    if err.kind == CliTypes.UnknownOption then
      (if |token|>2 && token[..2] == "--" then "join: unrecognized option '"+token+"'\n"
       else "join: invalid option -- '"+(if |token|>1 then [token[1]] else [])+"'\n")+TryHelp
    else if err.kind == CliTypes.MissingValue then
      (if |token|>2 && token[..2] == "--" then "join: option '"+token+"' requires an argument\n"
       else "join: option requires an argument -- '"+(if |token|>1 then [token[|token|-1]] else [])+"'\n")+TryHelp
    else if err.kind == CliTypes.Ambiguous then
      "join: option '"+token+"' is ambiguous; possibilities: "+
      (if |token| >= 3 && token[..3] == "--=" then
         "'--ignore-case' '--check-order' '--nocheck-order' '--zero-terminated' '--header' '--help' '--version'"
       else "'--header' '--help'")+"\n"+TryHelp
    else "join: option '"+token+"' doesn't allow an argument\n"+TryHelp
  }
  function ArgumentMessage(error: S.ArgumentError): BW.Bytes {
    match error
    case Missing => "join: missing operand\n"+TryHelp
    case MissingAfter(text) => "join: missing operand after "+Quote(text)+"\n"+TryHelp
    case Extra(text) => "join: extra operand "+E.SpecQuoteAfBytes(U.Encode(text))+"\n"+TryHelp
    case BadField(text) => "join: invalid field number: "+Quote(text)+"\n"
    case BadFile(text) => "join: invalid file number: "+Quote(text)+"\n"
    case BadFormat(text,kind) => "join: "+(if kind == 1 then "invalid field specifier: " else "invalid file number in field spec: ")+Quote(text)+"\n"
    case IncompatibleFields(a,b) => "join: incompatible join fields "+NatText(a)+", "+NatText(b)+"\n"
    case ConflictingFiller => "join: conflicting empty-field replacement strings\n"
    case MultiTab(text) => "join: multi-character tab "+Quote(text)+"\n"
    case IncompatibleTabs => "join: incompatible tabs\n"
    case Parse(error) => ParseErrorText(error)
  }
  function Mode(cmd: S.JoinCmdRaw): S.Mode {
    if !S.IsRunning(cmd) then cmd.mode
    else if |cmd.operands| == 0 then S.Error(S.Missing)
    else if |cmd.operands| == 1 then S.Error(S.MissingAfter(cmd.operands[0]))
    else if |cmd.operands| > 2 then S.Error(S.Extra(cmd.operands[2])) else S.Run
  }
  function FileError(path: string, message: string): BW.Bytes {
    "join: "+E.SpecQuoteFBytes(U.Encode(path))+": "+U.Encode(message)+"\n"
  }
  function BothStdinError(message: string): BW.Bytes {
    "join: both files cannot be standard input: "+U.Encode(message)+"\n"
  }
  function ReadError(message: string): BW.Bytes { "join: read error: "+U.Encode(message)+"\n" }
  function WriteError(message: string): BW.Bytes { "join: write error: "+U.Encode(message)+"\n" }
  function OrderError(path: string, line: nat, display: BW.Bytes): BW.Bytes {
    "join: "+U.Encode(path)+":"+NatText(line)+": is not sorted: "+display+"\n"
  }
  function ReadFailed(result: BW.IOResult<BW.Bytes>): bool {
    result.Err? && C.ReadResultStage(result) != BW.CloseFailed
  }
  function CloseFailed(result: BW.IOResult<BW.Bytes>): bool {
    result.Err? && C.ReadResultStage(result) == BW.CloseFailed
  }
  ghost predicate UsableData(cmd: S.JoinCmdRaw, result: BW.IOResult<BW.Bytes>, data: BW.Bytes) {
    var raw := C.ReadResultData(result);
    if !ReadFailed(result) then data == raw else
    |data| <= |raw| && data == raw[..|data|] &&
    (data == [] || data[|data|-1] == D.Delimiter(cmd)) &&
    forall i: nat | |data| <= i < |raw| :: raw[i] != D.Delimiter(cmd)
  }
  function FirstReadAborts(cmd: S.JoinCmdRaw, result: BW.IOResult<BW.Bytes>): bool {
    ReadFailed(result) && D.Delimiter(cmd) !in C.ReadResultData(result)
  }
  ghost predicate DisplayPrefix(text: BW.Bytes, display: BW.Bytes) {
    |display| <= |text| && |display| <= 2147483647 && display == text[..|display|] && '\0' !in display &&
    (|display| == |text| || |display| == 2147483647 || text[|display|] == '\0')
  }
  ghost predicate WarningDiagnostic(cmd: S.JoinCmdRaw, left: seq<D.Line>, right: seq<D.Line>,
                                    events: seq<D.Read>, index: nat, output: BW.Bytes) {
    if index == |events| then output == [] else
    index < |events| &&
    var e := events[index];
    var lines := if e.side == 1 then left else right;
    e.index < |lines| && |cmd.operands| == 2 &&
    exists display: BW.Bytes :: DisplayPrefix(lines[e.index].text,display) &&
                                output == OrderError(cmd.operands[if e.side == 1 then 0 else 1],e.index+1,display)
  }
  datatype JoinWitnessData = JoinWitnessData(ldata: BW.Bytes, rdata: BW.Bytes, left: seq<D.Line>, right: seq<D.Line>,
                                             tiles: seq<D.Tile>, events: seq<D.Read>, readCuts: seq<nat>, w1: nat, w2: nat, stop: nat,
                                             message1: BW.Bytes, message2: BW.Bytes)
  opaque ghost predicate JoinStructure(cmd: S.JoinCmdRaw, first: BW.IOResult<BW.Bytes>, second: BW.IOResult<BW.Bytes>,
                                                                                                            w: JoinWitnessData) {
    var ldata := w.ldata; var rdata := w.rdata; var left := w.left; var right := w.right;
                                                                    var tiles := w.tiles; var events := w.events; var readCuts := w.readCuts;
                                                                                                                  var w1 := w.w1; var w2 := w.w2; var stop := w.stop;
                                                                                                                                                  |cmd.operands| == 2 &&
                                                                                                                                                  UsableData(cmd,first,ldata) && UsableData(cmd,second,rdata) &&
                                                                                                                                                  D.Records(cmd,ldata,left) && D.Records(cmd,rdata,right) &&
                                                                                                                                                  D.ReadLayout(cmd,left,right,tiles,events,readCuts) &&
                                                                                                                                                  D.FirstWarning(cmd,left,right,tiles,events,1,w1) && D.FirstWarning(cmd,left,right,tiles,events,2,w2) &&
                                                                                                                                                  D.FirstFatal(cmd,left,right,tiles,events,w1,w2,ReadFailed(first),ReadFailed(second),stop)
  }
  opaque ghost predicate JoinWitness(cmd: S.JoinCmdRaw, first: BW.IOResult<BW.Bytes>, second: BW.IOResult<BW.Bytes>,
                                                                                                          w: JoinWitnessData, output: BW.Bytes, diagnostics: BW.Bytes, exit: int) {
    var left := w.left; var right := w.right; var tiles := w.tiles;
                                              var events := w.events; var readCuts := w.readCuts;
                                                                      var w1 := w.w1; var w2 := w.w2; var stop := w.stop;
                                                                                                      var message1 := w.message1; var message2 := w.message2;
                                                                                                                                  |cmd.operands| == 2 && JoinStructure(cmd,first,second,w) &&
                                                                                                                                  D.BodyOutput(cmd,left,right,tiles,events,readCuts,stop,output) &&
                                                                                                                                  WarningDiagnostic(cmd,left,right,events,w1,message1) && WarningDiagnostic(cmd,left,right,events,w2,message2) &&
                                                                                                                                  var warning1 := if w1 <= stop then message1 else [];
                                                                                                                                  var warning2 := if w2 <= stop then message2 else [];
                                                                                                                                  var warnings := if w1 <= w2 then warning1+warning2 else warning2+warning1;
                                                                                                                                  var fatalOrder := cmd.order == S.CheckOrder && (stop == w1 || stop == w2) && stop < |events|;
                                                                                                                                  diagnostics == warnings +
                                                                                                                                  (if stop < |events| then if fatalOrder then [] else
                                                                                                                                                           ReadError(C.CLocaleErrnoTextResult(C.ResultErrno(if events[stop].side == 1 then first else second)))
                                                                                                                                   else if CloseFailed(first) then FileError(cmd.operands[0],C.CLocaleErrnoTextResult(C.ResultErrno(first)))
                                                                                                                                   else if CloseFailed(second) then FileError(cmd.operands[1],C.CLocaleErrnoTextResult(C.ResultErrno(second)))
                                                                                                                                   else if w1 < |events| || w2 < |events| then DisorderSummary else []) &&
                                                                                                                                  exit == (if stop < |events| || CloseFailed(first) || CloseFailed(second) || w1 < |events| || w2 < |events| then 1 else 0)
  }
  opaque ghost predicate JoinResult(cmd: S.JoinCmdRaw, first: BW.IOResult<BW.Bytes>, second: BW.IOResult<BW.Bytes>,
                                                                                                         output: BW.Bytes, diagnostics: BW.Bytes, exit: int) {
    exists certificate: JoinWitnessData :: JoinWitness(cmd,first,second,certificate,output,diagnostics,exit)
  }
  ghost function Probe(fs: BW.FileSystem, observations: (BW.TrustedStreamRequest)->BW.TrustedStreamResult,
                       operand: string): BW.IOResult<BW.Bytes> {
    if operand == "-" then R.Ok([]) else C.ObservedOpenReadFileResultFields(fs,observations,operand)
  }
  ghost function ReadInput(fs: BW.FileSystem, observations: (BW.TrustedStreamRequest)->BW.TrustedStreamResult,
                           input: BW.Bytes, operand: string): BW.IOResult<BW.Bytes> {
    if operand == "-" then C.ObservedReadStdinResultFields(input,observations)
    else C.ObservedReadFileResultFields(fs,observations,operand)
  }
  ghost function Remaining(observations: (BW.TrustedStreamRequest)->BW.TrustedStreamResult,
                           input: BW.Bytes, operand: string): BW.Bytes {
    if operand == "-" then C.ObservedReadStdinRemainingFields(input,observations) else input
  }
  opaque twostate predicate Prepared(cmd: S.JoinCmdRaw, io: BenchIO.IO, output: BW.Bytes, diagnostics: BW.Bytes, exit: int)
    reads io.stdinRegion
  {
    var mode := Mode(cmd);
    if mode != S.Run then
      io.stdin() == old(io.stdin()) &&
      output == (if mode == S.Help then HelpText() else if mode == S.Version then VersionText() else []) &&
      diagnostics == (if mode.Error? then ArgumentMessage(mode.error) else []) &&
      exit == (if mode.Error? then 1 else 0)
    else
      |cmd.operands| == 2 &&
      var op1 := cmd.operands[0]; var op2 := cmd.operands[1];
                                  var probe1 := Probe(old(io.fs()),old(io.trustedStreams()),op1);
                                  var probe2 := Probe(old(io.fs()),old(io.trustedStreams()),op2);
                                  if probe1.Err? || probe2.Err? || (op1 == "-" && op2 == "-") then
                                    io.stdin() == old(io.stdin()) && output == [] && exit == 1 &&
                                    diagnostics == (if probe1.Err? then FileError(op1,C.CLocaleErrnoTextResult(C.ResultErrno(probe1)))
                                                    else if probe2.Err? then FileError(op2,C.CLocaleErrnoTextResult(C.ResultErrno(probe2))) else if cmd.mode == S.RunWithRangeError then BothStdinError(C.CLocaleErrnoTextResult(Errno.ERANGE)) else BothStdin)
                                  else
                                    var first := ReadInput(old(io.fs()),old(io.trustedStreams()),old(io.stdin()),op1);
                                    var after1 := Remaining(old(io.trustedStreams()),old(io.stdin()),op1);
                                    if FirstReadAborts(cmd,first) then
                                      io.stdin() == after1 && output == [] && exit == 1 &&
                                      diagnostics == ReadError(C.CLocaleErrnoTextResult(C.ResultErrno(first)))
                                    else
                                      var second := ReadInput(old(io.fs()),old(io.trustedStreams()),after1,op2);
                                      io.stdin() == Remaining(old(io.trustedStreams()),after1,op2) &&
                                      JoinResult(cmd,first,second,output,diagnostics,exit)
  }
  ghost predicate Emitted(observations: (BW.TrustedStreamRequest)->BW.TrustedStreamResult,
                          beforeOut: BW.Bytes, beforeErr: BW.Bytes, afterOut: BW.Bytes, afterErr: BW.Bytes,
                          output: BW.Bytes, diagnostic: BW.Bytes, normal: int, exit: int) {
    var written := if output == [] then BW.StreamWriteResult(0,beforeOut,0) else observations(BW.StreamWriteStdout(beforeOut,output));
    written.StreamWriteResult? &&
    var errors := diagnostic + (if written.err == 0 then [] else WriteError(C.CLocaleErrnoTextResult(written.err)));
    var reported := if errors == [] then BW.StreamWriteResult(0,beforeErr,0) else observations(BW.StreamWriteStderr(beforeErr,errors));
    reported.StreamWriteResult? &&
    (if output == [] then afterOut == beforeOut else C.WriteStdoutSpec(beforeOut,observations,afterOut,output,written.committed,written.err)) &&
    (if errors == [] then afterErr == beforeErr else C.WriteStderrSpec(beforeErr,observations,afterErr,errors,reported.committed,reported.err)) &&
    exit == (if written.err != 0 || reported.err != 0 then 1 else normal)
  }
  twostate predicate Spec(raw: S.JoinCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists output: BW.Bytes, diagnostic: BW.Bytes, normal: int :: Prepared(raw,io,output,diagnostic,normal) &&
                                                                  Emitted(old(io.trustedStreams()),old(io.stdout()),old(io.stderr()),io.stdout(),io.stderr(),output,diagnostic,normal,exit)
  }
}
