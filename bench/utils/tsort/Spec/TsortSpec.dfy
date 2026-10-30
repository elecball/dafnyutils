include "TsortSchema.dfy"
include "TsortGraphBuildSpec.dfy"
include "TsortSortSpec.dfy"
include "../../../core/IO.dfy"
include "../../../core/Utf8.dfy"
include "../Impl/CliSupport.dfy"

module TsortSpec {
  import BenchIO
  import BenchWorld
  import CliTypes
  import CliModel
  import Schema = TsortSchema
  import Graph = TsortGraphBuildSpec
  import SortSpec = TsortSortSpec
  import C = IOContract
  import Utf8 = Utf8Semantics

  datatype Event = Emit(vertex: BenchWorld.Bytes) |
                   Cut(cycle: seq<BenchWorld.Bytes>, edge: (BenchWorld.Bytes, nat))

  datatype ResultWitness = ResultWitness(
    events: seq<Event>, ranks: map<BenchWorld.Bytes, nat>,
    removed: map<(BenchWorld.Bytes, nat), nat>, release: map<BenchWorld.Bytes, nat>,
    position: map<BenchWorld.Bytes, nat>, offsets: seq<nat>, errOffsets: seq<nat>)

  function HelpTextSpec(): BenchWorld.Bytes {
    "Usage: tsort [OPTION] [FILE]\n" +
    "Write totally ordered list consistent with the partial ordering in FILE.\n\n" +
    "With no FILE, or when FILE is -, read standard input.\n\n" +
    "      --help\n         display this help and exit\n" +
    "      --version\n         output version information and exit\n\n" +
    "Report bugs to: bug-coreutils@gnu.org\n" +
    "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n" +
    "General help using GNU software: <https://www.gnu.org/gethelp/>\n" +
    "Report any translation bugs to <https://translationproject.org/team/>\n" +
    "Full documentation <https://www.gnu.org/software/coreutils/tsort>\n" +
    "or available locally via: info '(coreutils) tsort invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes {
    "tsort (GNU coreutils) 9.10.13-2cf49\n" +
    "Copyright (C) 2026 Free Software Foundation, Inc.\n" +
    "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n" +
    "This is free software: you are free to change and redistribute it.\n" +
    "There is NO WARRANTY, to the extent permitted by law.\n\nWritten by Mark Kettenis.\n"
  }

  function TryHelpText(): BenchWorld.Bytes { "Try 'tsort --help' for more information.\n" }
  function ExtraOperandText(quoted: BenchWorld.Bytes): BenchWorld.Bytes {
    "tsort: extra operand " + quoted + "\n" + TryHelpText()
  }
  function OddTokensText(quoted: BenchWorld.Bytes): BenchWorld.Bytes {
    "tsort: " + quoted + ": input contains an odd number of tokens\n"
  }
  function LoopText(quoted: BenchWorld.Bytes): BenchWorld.Bytes {
    "tsort: " + quoted + ": input contains a loop:\n"
  }
  function ReadErrorText(quoted: BenchWorld.Bytes, reason: string): BenchWorld.Bytes {
    "tsort: " + quoted + ": read error: " + Utf8.Encode(reason) + "\n"
  }
  function FileErrorText(quoted: BenchWorld.Bytes, reason: string): BenchWorld.Bytes {
    "tsort: " + quoted + ": " + Utf8.Encode(reason) + "\n"
  }
  function WriteErrorText(reason: string): BenchWorld.Bytes {
    "tsort: write error: " + Utf8.Encode(reason) + "\n"
  }

  function InvalidShort(token: string, index: nat): BenchWorld.Bytes
    requires index < |token|
    decreases |token| - index
  {
    if token[index] == 'w' && index + 1 < |token| then InvalidShort(token, index + 1)
    else [Utf8.EncodeChar(token[index])[0]]
  }

  function LongOption(token: string): string {
    var eq := CliModel.FindChar(token, '=');
    var name := if eq >= 0 then token[..eq] else token;
    if |name| > 2 && CliModel.HasPrefix(name, "--") then
      if CliModel.HasPrefix("help", name[2..]) then "--help"
      else if CliModel.HasPrefix("version", name[2..]) then "--version"
      else name
    else name
  }

  function ParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes {
    if err.kind == CliTypes.UnknownOption then
      if |err.rawToken| > 2 && err.rawToken[..2] == "--" then
        "tsort: unrecognized option '" + Utf8.Encode(err.rawToken) + "'\n" + TryHelpText()
      else if |err.rawToken| > 1 && err.rawToken[0] == '-' then
        "tsort: invalid option -- '" + InvalidShort(err.rawToken, 1) + "'\n" + TryHelpText()
      else "tsort: invalid option\n" + TryHelpText()
    else if err.kind == CliTypes.UnexpectedValue then
      "tsort: option '" + Utf8.Encode(LongOption(err.rawToken)) + "' doesn't allow an argument\n" + TryHelpText()
    else if err.kind == CliTypes.Ambiguous then
      "tsort: option '" + Utf8.Encode(err.rawToken) +
      "' is ambiguous; possibilities: '--help' '--version'\n" + TryHelpText()
    else "tsort: parse error at token '" + Utf8.Encode(err.rawToken) + "'\n"
  }

  function InputPath(raw: Schema.TsortCmdRaw): string {
    if |raw.operands| == 0 then "-" else raw.operands[0]
  }
  function NeedsPathQuotes(path: string): bool {
    |path| == 0 || exists i: nat :: i < |path| &&
                                    ((path[i] as int) < 33 || (path[i] as int) >= 127 ||
                                     path[i] in ":!?\"$&'()*;<=>[\\^`|" ||
                                     (i == 0 && path[i] in "#~") || (|path| == 1 && path[i] in "{}"))
  }
  function FilenameText(path: string, alwaysQuoted: BenchWorld.Bytes): BenchWorld.Bytes {
    if NeedsPathQuotes(path) then alwaysQuoted else Utf8.Encode(path)
  }
  function IsSpace(byte: BenchWorld.RawByte): bool { byte in [' ', '\t', '\n'] }

  ghost opaque predicate TokenName(raw: BenchWorld.Bytes, name: BenchWorld.Bytes) {
    |raw| > 0 && exists stop: nat :: stop <= |raw| &&
                                     (forall i: nat | i < stop :: raw[i] != '\0') &&
                                     (stop == |raw| || raw[stop] == '\0') && name == raw[..stop]
  }

  ghost predicate Tokenization(
    data: BenchWorld.Bytes,
    tokens: seq<BenchWorld.Bytes>,
    starts: seq<nat>,
    ends: seq<nat>
  ) {
    |tokens| == |starts| == |ends| &&
    (forall k: nat | k < |tokens| ::
       starts[k] < ends[k] <= |data| &&
       (forall i: nat | starts[k] <= i < ends[k] :: !IsSpace(data[i])) &&
       TokenName(data[starts[k]..ends[k]], tokens[k])) &&
    (forall k: nat | 0 < k < |tokens| :: ends[k - 1] < starts[k]) &&
    (forall i: nat | i < |data| :: !IsSpace(data[i]) <==>
                                   exists k: nat :: k < |tokens| && starts[k] <= i < ends[k])
  }

  function Lines(names: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    decreases |names|
  { if |names| == 0 then [] else names[0] + "\n" + Lines(names[1..]) }
  function CycleLines(names: seq<BenchWorld.Bytes>): BenchWorld.Bytes
    decreases |names|
  { if |names| == 0 then [] else "tsort: " + names[0] + "\n" + CycleLines(names[1..]) }

  function OneLine(name: BenchWorld.Bytes, diagnostic: bool): BenchWorld.Bytes {
    (if diagnostic then "tsort: " else []) + name + "\n"
  }

  ghost predicate InputGraph(tokens: seq<BenchWorld.Bytes>, graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>) {
    |tokens| % 2 == 0 && graph.Keys == (set token | token in tokens) &&
    (forall source | source in graph ::
       exists positions: seq<nat> :: Graph.OutgoingEdges(tokens, source, graph[source], positions))
  }
  ghost predicate CyclicLe(anchor: BenchWorld.Bytes, first: BenchWorld.Bytes, second: BenchWorld.Bytes) {
    var firstAfter := !SortSpec.BytesLe(first, anchor);
    var secondAfter := !SortSpec.BytesLe(second, anchor);
    (firstAfter && !secondAfter) || (firstAfter == secondAfter && SortSpec.BytesLe(first, second))
  }
  ghost predicate ActiveRelation(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    removed: map<(BenchWorld.Bytes, nat), nat>,
    source: BenchWorld.Bytes,
    target: BenchWorld.Bytes,
    time: nat
  ) {
    exists p: nat :: source in graph && p < |graph[source]| && (source, p) in removed &&
                     graph[source][p] == target && removed[(source, p)] >= time
  }
  ghost predicate SelectedCycleFields(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    ranks: map<BenchWorld.Bytes, nat>,
    removed: map<(BenchWorld.Bytes, nat), nat>,
    time: nat,
    cycle: seq<BenchWorld.Bytes>,
    walk: seq<BenchWorld.Bytes>,
    begin: nat
  ) {
    |walk| >= 3 && 1 <= begin < |walk| - 1 &&
    (forall v | v in walk :: v in graph && v in ranks && ranks[v] > time) &&
    (forall v | v in graph && v in ranks && ranks[v] > time :: SortSpec.BytesLe(walk[0], v)) &&
    (forall i: nat, j: nat | 1 <= i < j < |walk| - 1 :: walk[i] != walk[j]) &&
    walk[|walk| - 1] == walk[begin] &&
    (forall i: nat | 0 < i < |walk| ::
       ActiveRelation(graph, removed, walk[i], walk[i - 1], time) &&
       (forall source | source in graph && source in ranks && ranks[source] > time &&
                        ActiveRelation(graph, removed, source, walk[i - 1], time) ::
          CyclicLe(walk[i - 1], walk[i], source))) &&
    |cycle| == |walk| - 1 - begin &&
    (forall i: nat | i < |cycle| :: cycle[i] == walk[|walk| - 2 - i])
  }

  ghost predicate SelectedCycle(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    ranks: map<BenchWorld.Bytes, nat>,
    removed: map<(BenchWorld.Bytes, nat), nat>,
    time: nat,
    cycle: seq<BenchWorld.Bytes>
  ) {
    exists walk: seq<BenchWorld.Bytes>, begin: nat ::
      SelectedCycleFields(graph, ranks, removed, time, cycle, walk, begin)
  }

  ghost opaque predicate VertexRelease(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    ranks: map<BenchWorld.Bytes, nat>,
    removed: map<(BenchWorld.Bytes, nat), nat>,
    release: map<BenchWorld.Bytes, nat>,
    position: map<BenchWorld.Bytes, nat>,
    v: BenchWorld.Bytes
  )
    requires v in graph && ranks.Keys == graph.Keys && removed.Keys == SortSpec.Edges(graph)
    requires release.Keys == graph.Keys == position.Keys
  {
    release[v] <= ranks[v] &&
    (forall edge | edge in SortSpec.Edges(graph) && graph[edge.0][edge.1] == v :: removed[edge] < release[v]) &&
    (release[v] == 0 || exists edge ::
       edge in SortSpec.Edges(graph) && graph[edge.0][edge.1] == v &&
       removed[edge] + 1 == release[v]) &&
    (release[v] == 0 || (
       (exists edge ::
          edge in SortSpec.Edges(graph) && graph[edge.0][edge.1] == v &&
          removed[edge] + 1 == release[v] && position[v] == edge.1) &&
       (forall edge | edge in SortSpec.Edges(graph) && graph[edge.0][edge.1] == v &&
                      removed[edge] + 1 == release[v] :: edge.1 <= position[v])))
  }

  ghost opaque predicate SortCertificate(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    events: seq<Event>,
    ranks: map<BenchWorld.Bytes, nat>,
    removed: map<(BenchWorld.Bytes, nat), nat>,
    release: map<BenchWorld.Bytes, nat>,
    position: map<BenchWorld.Bytes, nat>
  ) {
    ranks.Keys == graph.Keys && removed.Keys == SortSpec.Edges(graph) &&
    release.Keys == graph.Keys && position.Keys == graph.Keys &&
    (forall v | v in graph :: ranks[v] < |events| && events[ranks[v]] == Emit(v)) &&
    (forall i: nat | i < |events| && events[i].Emit? ::
       events[i].vertex in graph && ranks[events[i].vertex] == i) &&
    (forall edge: (BenchWorld.Bytes, nat) | edge in SortSpec.Edges(graph) ::
       removed[edge] == ranks[edge.0] ||
       (removed[edge] < ranks[edge.0] && removed[edge] < |events| &&
        events[removed[edge]].Cut? && events[removed[edge]].edge == edge)) &&
    (forall edge: (BenchWorld.Bytes, nat) | edge in SortSpec.Edges(graph) ::
       graph[edge.0][edge.1] in graph &&
       removed[edge] < ranks[graph[edge.0][edge.1]]) &&
    (forall v | v in graph :: VertexRelease(graph, ranks, removed, release, position, v)) &&
    (forall u: BenchWorld.Bytes, v: BenchWorld.Bytes | u in graph && v in graph && ranks[u] < ranks[v] ::
       release[u] < release[v] || (release[u] == release[v] &&
                                   (if release[u] == 0 then SortSpec.BytesLe(u, v) else position[u] < position[v]))) &&
    (forall i: nat | i < |events| && events[i].Cut? ::
       var event := events[i];
       event.edge in SortSpec.Edges(graph) && removed[event.edge] == i &&
       |event.cycle| > 0 && event.edge.0 == event.cycle[|event.cycle| - 1] &&
       graph[event.edge.0][event.edge.1] == event.cycle[0] &&
       (forall p: nat | p < event.edge.1 && graph[event.edge.0][p] == event.cycle[0] ::
          removed[(event.edge.0, p)] < i) &&
       (forall v | v in graph && ranks[v] > i :: release[v] > i) &&
       SelectedCycle(graph, ranks, removed, i, event.cycle))
  }

  ghost predicate EventText(
    event: Event,
    quoted: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    diagnostics: BenchWorld.Bytes,
    begin: nat,
    end: nat,
    errBegin: nat,
    errEnd: nat
  ) {
    begin <= end <= |output| && errBegin <= errEnd <= |diagnostics| &&
    output[begin..end] == (if event.Emit? then event.vertex + "\n" else []) &&
    diagnostics[errBegin..errEnd] ==
    (if event.Cut? then LoopText(quoted) + CycleLines(event.cycle) else [])
  }

  ghost predicate ResultFields(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    quoted: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    diagnostics: BenchWorld.Bytes,
    exit: int,
    resultData: ResultWitness
  ) {
    SortCertificate(graph, resultData.events, resultData.ranks, resultData.removed, resultData.release, resultData.position) &&
    |resultData.offsets| == |resultData.events| + 1 && |resultData.errOffsets| == |resultData.events| + 1 &&
    resultData.offsets[0] == 0 && resultData.errOffsets[0] == 0 &&
    resultData.offsets[|resultData.events|] == |output| && resultData.errOffsets[|resultData.events|] == |diagnostics| &&
    (forall i: nat | i < |resultData.events| ::
       EventText(
         resultData.events[i], quoted, output, diagnostics,
         resultData.offsets[i], resultData.offsets[i + 1], resultData.errOffsets[i], resultData.errOffsets[i + 1]
       )) &&
    exit == (if exists i: nat :: i < |resultData.events| && resultData.events[i].Cut? then 1 else 0)
  }

  ghost opaque predicate GraphResult(
    graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>>,
    quoted: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    diagnostics: BenchWorld.Bytes,
    exit: int
  ) {
    exists resultData: ResultWitness :: ResultFields(graph, quoted, output, diagnostics, exit, resultData)
  }

  ghost opaque predicate SortResult(
    tokens: seq<BenchWorld.Bytes>,
    quoted: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    diagnostics: BenchWorld.Bytes,
    exit: int
  ) {
    exists graph: map<BenchWorld.Bytes, seq<BenchWorld.Bytes>> ::
      InputGraph(tokens, graph) && GraphResult(graph, quoted, output, diagnostics, exit)
  }

  ghost opaque predicate DataResult(
    data: BenchWorld.Bytes,
    quoted: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    diagnostics: BenchWorld.Bytes,
    exit: int
  ) {
    exists tokens: seq<BenchWorld.Bytes>, starts: seq<nat>, ends: seq<nat> ::
      Tokenization(data, tokens, starts, ends) &&
      (if |tokens| % 2 != 0 then output == [] && diagnostics == OddTokensText(quoted) && exit == 1
       else SortResult(tokens, quoted, output, diagnostics, exit))
  }

  ghost predicate EmissionOutcome(
    beforeOut: BenchWorld.Bytes,
    beforeErr: BenchWorld.Bytes,
    afterOut: BenchWorld.Bytes,
    afterErr: BenchWorld.Bytes,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    output: BenchWorld.Bytes,
    diagnostics: BenchWorld.Bytes,
    normalExit: int,
    exit: int,
    committed: nat,
    outErr: int,
    errCommitted: nat,
    errErr: int
  ) {
    (if output == [] then afterOut == beforeOut && committed == 0 && outErr == 0
     else C.WriteStdoutSpec(beforeOut, observations, afterOut, output, committed, outErr)) &&
    var errors := diagnostics + (if outErr == 0 then [] else WriteErrorText(C.CLocaleErrnoTextResult(outErr)));
    (if errors == [] then afterErr == beforeErr && errCommitted == 0 && errErr == 0
     else C.WriteStderrSpec(beforeErr, observations, afterErr, errors, errCommitted, errErr)) &&
    exit == (if outErr != 0 || errErr != 0 then 1 else normalExit)
  }

  ghost opaque predicate Emission(
    beforeOut: BenchWorld.Bytes,
    beforeErr: BenchWorld.Bytes,
    afterOut: BenchWorld.Bytes,
    afterErr: BenchWorld.Bytes,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    output: BenchWorld.Bytes,
    diagnostics: BenchWorld.Bytes,
    normalExit: int,
    exit: int
  ) {
    exists committed: nat, outErr: int, errCommitted: nat, errErr: int ::
      EmissionOutcome(beforeOut, beforeErr, afterOut, afterErr, observations,
                      output, diagnostics, normalExit, exit, committed, outErr, errCommitted, errErr)
  }

  twostate predicate Prepared(
    raw: Schema.TsortCmdRaw,
    io: BenchIO.IO,
    exit: int,
    output: BenchWorld.Bytes,
    diagnostics: BenchWorld.Bytes
  )
    reads io.stdinRegion, io.fsRegion, io.trustedStreamsRegion
  {
    if raw.mode == Schema.ModeHelp then output == HelpTextSpec() && diagnostics == [] && exit == 0
    else if raw.mode == Schema.ModeVersion then output == VersionTextSpec() && diagnostics == [] && exit == 0
    else if raw.mode.ModeExtraOperand? then output == [] && exit == 1 &&
                                            diagnostics == ExtraOperandText(C.QuoteArgumentResult(Utf8.Encode(raw.mode.operand)))
    else
      var path := InputPath(raw);
      var result := if path == "-" then C.ObservedReadStdinResultFields(old(io.stdin()), io.trustedStreams())
                    else C.ObservedReadFileResultFields(io.fs(), io.trustedStreams(), path);
      (if path == "-" then
         C.ReadStdinSpec(old(io.stdin()), io.trustedStreams(), io.stdin(),
                         C.ReadResultData(result), C.ResultErrno(result))
       else
         C.ReadFileSpec(io.fs(), io.trustedStreams(), path,
                        C.ReadResultData(result), C.ResultErrno(result), C.ReadResultStage(result))) &&
      (path != "-" || io.stdin() == C.ObservedReadStdinRemainingFields(old(io.stdin()), io.trustedStreams())) &&
      var quoted := FilenameText(path, C.QuoteafPathResult(path));
      if result.Err? && C.ReadResultStage(result) != BenchWorld.CloseFailed then
        output == [] && exit == 1 && diagnostics ==
                                     (if path != "-" && C.ReadResultStage(result) == BenchWorld.OpenFailed then
                                        FileErrorText(quoted, C.CLocaleErrnoTextResult(C.ResultErrno(result)))
                                      else ReadErrorText(quoted, C.CLocaleErrnoTextResult(C.ResultErrno(result))))
      else exists normalExit: int, errors: BenchWorld.Bytes ::
             DataResult(C.ReadResultData(result), quoted, output, errors, normalExit) &&
             var closeError := C.ReadResultStage(result) == BenchWorld.CloseFailed && !(normalExit == 1 && output == []);
             diagnostics == errors + (if closeError then
                                        FileErrorText(quoted, C.CLocaleErrnoTextResult(C.ResultErrno(result))) else []) &&
             exit == (if closeError then 1 else normalExit)
  }

  opaque twostate predicate Spec(raw: Schema.TsortCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion, io.fsRegion, io.trustedStreamsRegion
  {
    exists output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      Prepared(raw, io, normalExit, output, diagnostics) &&
      Emission(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(), io.trustedStreams(),
               output, diagnostics, normalExit, exit)
  }
}
