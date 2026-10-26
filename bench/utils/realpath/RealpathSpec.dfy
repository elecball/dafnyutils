include "RealpathSchema.dfy"
include "../../core/IO.dfy"
include "../../core/Errno.dfy"
include "../../core/Utf8.dfy"
include "../../core/StringEscaping.dfy"

module RealpathSpec {
  import S = RealpathSchema
  import BW = BenchWorld
  import BenchIO
  import C = IOContract
  import E = Errnos
  import R = Results
  import Utf8 = Utf8Semantics
  import SE = StringEscaping
  import CliTypes

  datatype PathResult = Ok(v: string) | Err(e: int) | MemoryFatal
  datatype Status = NoStatus | ObservedStatus(ok: bool, directory: bool, err: int)
  // Inductive denotation rules for directory-anchored lexical path syntax.
  datatype MeaningProof = DirectoryMeaning |
                          ChildMeaning(parentProof: MeaningProof, parentResult: PathResult, rule: ComponentProof)
  datatype ComponentProof = InheritedFailure | SameDirectory | ParentDirectory |
                            Ordinary(status: Status)

  function Components(expr: S.PathExpr): seq<string>
    decreases expr
  {
    match expr
    case Anchor(_) => []
    case Child(parent, name) => Components(parent) + [name]
  }

  function Origin(expr: S.PathExpr): string
    decreases expr
  {
    match expr
    case Anchor(directory) => directory
    case Child(parent, _) => Origin(parent)
  }

  ghost predicate Syntax(path: string, cwd: string, expr: S.PathExpr) {
    Origin(expr) == (if BW.IsAbsolutePath(path) then "/" else cwd) &&
    BW.JoinSegments(Components(expr)) ==
    (if BW.IsAbsolutePath(path) then path[1..] else path) &&
    (forall name | name in Components(expr) :: '/' !in name)
  }

  function ChildPath(directory: string, name: string): string {
    if directory == "/" then "/" + name else directory + "/" + name
  }

  ghost predicate ParentPath(path: string, parent: string) {
    (path == "/" && parent == "/") ||
    (exists cut: nat :: cut < |path| && path[cut] == '/' &&
                        (forall j: nat | cut < j < |path| :: path[j] != '/') &&
                        parent == (if cut == 0 then "/" else path[..cut])) ||
    ('/' !in path && parent == "/")
  }

  // A suffix requires a directory when its first nonempty component is dot or
  // dot-dot, or when it contains separators and no filename component.
  predicate Slashes(text: string) { forall c | c in text :: c == '/' }

  ghost predicate DirectorySuffix(suffix: string) {
    var parts := BW.SplitSegments(suffix, 0, 0);
    |suffix| > 0 && suffix[0] == '/' &&
    ((forall i: nat | i < |parts| :: parts[i] == ".") ||
     (exists i: nat :: i < |parts| && parts[i] == ".." &&
                       (forall j: nat | j < i :: parts[j] == ".")))
  }

  ghost predicate StatusObservation(fs: BW.FileSystem,
                                    failures: (BW.NativeFailureRequest) -> int, path: string, status: Status) {
    status.ObservedStatus? &&
    C.IsDirectorySpec(fs, failures, path, true, status.ok, status.directory, status.err)
  }

  ghost predicate EntryPolicy(existence: S.Existence, suffix: string,
                              status: Status, error: int) {
    if existence == S.Missing then status == NoStatus && error == 0
    else if DirectorySuffix(suffix) then
      status.ObservedStatus? &&
      error == (if status.ok ||
                   (existence == S.AllButLast && status.err == E.ENOENT && Slashes(suffix))
                then 0 else status.err)
    else if suffix != "" then status == NoStatus && error == 0
    else (status.ObservedStatus? &&
          error == (if status.ok || (existence == S.AllButLast && status.err == E.ENOENT)
                    then 0 else status.err))
  }

  ghost predicate EntryStatus(fs: BW.FileSystem,
                              failures: (BW.NativeFailureRequest) -> int, path: string, suffix: string,
                              status: Status) {
    status == NoStatus ||
    StatusObservation(fs, failures,
                      if DirectorySuffix(suffix) then path + "/" else path, status)
  }

  opaque ghost predicate Meaning(fs: BW.FileSystem,
                                 failures: (BW.NativeFailureRequest) -> int, existence: S.Existence,
                                 expr: S.PathExpr, suffix: string, result: PathResult, proof: MeaningProof)
    decreases proof
  {
    match (expr, proof)
    case (Anchor(directory), DirectoryMeaning) => result == Ok(directory)
    case (Child(parent, name), ChildMeaning(prior, parentResult, rule)) =>
      Meaning(fs, failures, existence, parent, "/" + name + suffix, parentResult, prior) &&
      ComponentMeaning(fs, failures, existence, parentResult, name, suffix, result, rule)
    case _ => false
  }

  ghost predicate OrdinaryMeaning(fs: BW.FileSystem,
                                  failures: (BW.NativeFailureRequest) -> int, existence: S.Existence,
                                  parent: string, name: string, suffix: string, result: PathResult, status: Status) {
    var path := ChildPath(parent, name);
    var error := if result.Err? then result.e else 0;
    EntryStatus(fs, failures, path, suffix, status) &&
    EntryPolicy(existence, suffix, status, error) &&
    result == (if error == 0 then Ok(path) else Err(error))
  }

  opaque ghost predicate ComponentMeaning(fs: BW.FileSystem,
                                          failures: (BW.NativeFailureRequest) -> int, existence: S.Existence,
                                          parent: PathResult, name: string, suffix: string,
                                          result: PathResult, rule: ComponentProof)
  {
    if !parent.Ok? then rule == InheritedFailure && result == parent
    else if name == "" || name == "." then rule == SameDirectory && result == parent
    else if name == ".." then
      rule == ParentDirectory && result.Ok? && ParentPath(parent.v, result.v)
    else (rule.Ordinary? &&
          OrdinaryMeaning(fs, failures, existence, parent.v, name, suffix, result, rule.status))
  }

  // Every retained GNU F_triple occupies 24 disjoint native bytes. The
  // pinned64-bit ABI admits at most SIZE_MAX addressable nonnull bytes.
  const NativeAddressBytes: nat := 18446744073709551615
  const NativeTripleBytes: nat := 24
  const NativeRecordCapacity: nat := NativeAddressBytes / NativeTripleBytes
  datatype LinkKey = LinkKey(device: int, inode: int, suffix: string)
  datatype History = History(warm: nat, seen: set<LinkKey>)
  predicate ValidHistory(history: History) {
    history.warm <= 20 && |history.seen| <= NativeRecordCapacity
  }
  predicate Extends(before: History, after: History) {
    before.warm <= after.warm && before.seen <= after.seen
  }
  datatype ParentStatus = NoParentStatus | ParentStatus(result: BW.IOResult<BW.FileStatus>)
  datatype PhysicalProof = PhysicalDirectory |
                           PhysicalChild(prior: PhysicalProof, parentResult: PathResult,
                                         parentHistory: History, parentCursor: nat, rule: PhysicalRule)
  datatype PhysicalRule = PhysicalFailure | PhysicalSame | PhysicalParent |
                          PhysicalOrdinary(read: BW.IOResult<string>, status: Status) |
                          PhysicalFollow(target: string, parentStatus: ParentStatus, targetExpr: S.PathExpr,
                                         targetProof: PhysicalProof) |
                          PhysicalRepeat(target: string, parentStatus: ParentStatus) |
                          PhysicalParentFailure(target: string, parentStatus: ParentStatus) |
                          PhysicalMemory(target: string, parentStatus: ParentStatus)

  ghost predicate ParentQuery(fs: BW.FileSystem,
                              failures: (BW.NativeFailureRequest) -> int, observations: BW.StatusTimeObservations,
                              first: nat, last: nat, parent: string, history: History, status: ParentStatus) {
    if history.warm < 20 then status == NoParentStatus && last == first
    else (status.ParentStatus? &&
          C.GetFileStatusSpec(observations, failures, first, last, fs, ChildPath(parent, ""), true,
                              status.result.Ok?, C.ResultValue(status.result, BW.DEFAULT_FILE_STATUS), C.ResultErrno(status.result)))
  }
  function ParentKey(status: ParentStatus, suffix: string): LinkKey {
    if status.ParentStatus? && status.result.Ok? then
      LinkKey(status.result.v.hostKey.device, status.result.v.hostKey.inode, suffix)
    else LinkKey(0, 0, suffix)
  }
  function Added(history: History, key: LinkKey): History {
    if history.warm < 20 then History(history.warm + 1, history.seen)
    else History(history.warm, history.seen + {key})
  }
  predicate Repeated(history: History, key: LinkKey) {
    history.warm == 20 && key in history.seen
  }
  predicate Full(history: History) {
    history.warm == 20 && |history.seen| == NativeRecordCapacity
  }
  ghost predicate PhysicalOrdinaryMeaning(fs: BW.FileSystem,
                                          failures: (BW.NativeFailureRequest) -> int, existence: S.Existence,
                                          parent: string, name: string, suffix: string, result: PathResult,
                                          read: BW.IOResult<string>, status: Status) {
    var path := ChildPath(parent, name);
    var error := if result.Err? then result.e else 0;
    read.Err? && C.ReadLinkSpec(fs, failures, path, read) &&
    EntryStatus(fs, failures, path, suffix, status) &&
    (if existence == S.Missing then status == NoStatus && error == 0
     else if DirectorySuffix(suffix) then
       status.ObservedStatus? && error ==
                                 (if status.ok || (existence == S.AllButLast && status.err == E.ENOENT && Slashes(suffix))
                                  then 0 else status.err)
     else (status == NoStatus && error ==
                                 (if C.ResultErrno(read) == E.EINVAL ||
                                     (existence == S.AllButLast && C.ResultErrno(read) == E.ENOENT && Slashes(suffix))
                                  then 0 else C.ResultErrno(read)))) &&
    result == (if error == 0 then Ok(path) else Err(error))
  }

  opaque ghost predicate PhysicalMeaning(fs: BW.FileSystem,
                                         failures: (BW.NativeFailureRequest) -> int, observations: BW.StatusTimeObservations,
                                         first: nat, last: nat, existence: S.Existence, expr: S.PathExpr,
                                         suffix: string, before: History, after: History, result: PathResult, proof: PhysicalProof)
    decreases proof
  {
    match (expr, proof)
    case (Anchor(directory), PhysicalDirectory) =>
      result == Ok(directory) && after == before && last == first
    case (Child(parent, name), PhysicalChild(prior, parentResult, parentHistory, cursor, rule)) =>
      PhysicalMeaning(fs, failures, observations, first, cursor, existence, parent,
                      "/" + name + suffix, before, parentHistory, parentResult, prior) &&
      PhysicalComponent(fs, failures, observations, cursor, last, existence,
                        parentResult, name, suffix, parentHistory, after, result, rule)
    case _ => false
  }

  opaque ghost predicate PhysicalComponent(fs: BW.FileSystem,
                                           failures: (BW.NativeFailureRequest) -> int, observations: BW.StatusTimeObservations,
                                           first: nat, last: nat, existence: S.Existence, parent: PathResult,
                                           name: string, suffix: string, before: History, after: History,
                                           result: PathResult, rule: PhysicalRule)
    decreases rule
  {
    if !parent.Ok? then rule == PhysicalFailure && result == parent && after == before && last == first
    else if name == "" || name == "." then
      rule == PhysicalSame && result == parent && after == before && last == first
    else if name == ".." then
      rule == PhysicalParent && result.Ok? && ParentPath(parent.v, result.v) && after == before && last == first
    else
      var path := ChildPath(parent.v, name);
      match rule
      case PhysicalOrdinary(read, status) =>
        PhysicalOrdinaryMeaning(fs, failures, existence, parent.v, name, suffix, result, read, status) &&
        after == before && last == first
      case PhysicalFollow(target, status, expr, proof) =>
        C.ReadLinkSpec(fs, failures, path, R.Ok(target)) &&
        exists cursor: nat :: ParentQuery(fs, failures, observations, first, cursor, parent.v, before, status) &&
                              (status == NoParentStatus || status.result.Ok?) &&
                              var key := ParentKey(status, name + suffix);
                              !Repeated(before, key) && !Full(before) && Syntax(target, parent.v, expr) &&
                              PhysicalMeaning(fs, failures, observations, cursor, last, existence, expr, suffix,
                                              Added(before, key), after, result, proof)
      case PhysicalRepeat(target, status) =>
        C.ReadLinkSpec(fs, failures, path, R.Ok(target)) &&
        ParentQuery(fs, failures, observations, first, last, parent.v, before, status) &&
        status.ParentStatus? && status.result.Ok? && Repeated(before, ParentKey(status, name + suffix)) &&
        after == before && result == (if existence == S.Missing then Ok(path) else Err(E.ELOOP))
      case PhysicalParentFailure(target, status) =>
        C.ReadLinkSpec(fs, failures, path, R.Ok(target)) &&
        ParentQuery(fs, failures, observations, first, last, parent.v, before, status) &&
        status.ParentStatus? && status.result.Err? && after == before && result == Err(C.ResultErrno(status.result))
      case PhysicalMemory(target, status) =>
        C.ReadLinkSpec(fs, failures, path, R.Ok(target)) &&
        ParentQuery(fs, failures, observations, first, last, parent.v, before, status) &&
        status.ParentStatus? && status.result.Ok? && !Repeated(before, ParentKey(status, name + suffix)) &&
        Full(before) && after == before && result == MemoryFatal
      case _ => false
  }

  ghost predicate PhysicalCanonicalizes(fs: BW.FileSystem,
                                        failures: (BW.NativeFailureRequest) -> int, observations: BW.StatusTimeObservations,
                                        first: nat, last: nat, existence: S.Existence, cwd: string, path: string, result: PathResult) {
    exists expr: S.PathExpr, after: History, proof: PhysicalProof ::
      Syntax(path, cwd, expr) &&
      PhysicalMeaning(fs, failures, observations, first, last, existence, expr, "",
                      History(0, {}), after, result, proof)
  }

  ghost predicate Canonicalizes(fs: BW.FileSystem,
                                failures: (BW.NativeFailureRequest) -> int, observations: BW.StatusTimeObservations,
                                first: nat, last: nat, raw: S.RealpathCmdRaw,
                                cwd: BW.IOResult<string>, path: string, result: PathResult) {
    if path == "" then result == Err(E.ENOENT) && last == first
    else if !BW.IsAbsolutePath(path) && cwd.Err? then
      result == (if C.ResultErrno(cwd) == E.ENOMEM then MemoryFatal else Err(C.ResultErrno(cwd))) && last == first
    else if raw.links == S.Physical then
      PhysicalCanonicalizes(fs, failures, observations, first, last, raw.existence,
                            if cwd.Ok? then cwd.v else "/", path, result)
    else exists expr: S.PathExpr, prior: PathResult, proof: MeaningProof ::
           Syntax(path, if cwd.Ok? then cwd.v else "/", expr) &&
           Meaning(fs, failures, raw.existence, expr, "", prior, proof) &&
           (if raw.links == S.Strip || !prior.Ok? then result == prior && last == first
            else PhysicalCanonicalizes(fs, failures, observations, first, last, raw.existence, "/", prior.v, result))
  }

  ghost predicate LongestCommonPrefix(left: seq<string>, right: seq<string>, length: nat) {
    length <= |left| && length <= |right| && left[..length] == right[..length] &&
    (length == |left| || length == |right| || left[length] != right[length])
  }

  ghost predicate RelativePath(from: string, target: string, value: string) {
    var left := BW.SplitSegments(from, 0, 0);
    var right := BW.SplitSegments(target, 0, 0);
    exists common: nat :: LongestCommonPrefix(left, right, common) &&
                          var components := seq(|left| - common, i => "..") + right[common..];
                          value == (if components == [] then "." else BW.JoinSegments(components))
  }

  function PathPrefix(prefix: string, path: string): bool {
    prefix == "/" || path == prefix ||
    (|prefix| < |path| && path[..|prefix|] == prefix && path[|prefix|] == '/')
  }

  function MemoryMessage(): BW.Bytes { "realpath: memory exhausted\n" }

  function MissingOperand(): BW.Bytes {
    "realpath: missing operand\nTry 'realpath --help' for more information.\n"
  }

  function ErrorMessage(path: string, reason: string): BW.Bytes {
    "realpath: " + SE.SpecQuoteFBytes(Utf8.Encode(path)) + ": " + Utf8.Encode(reason) + "\n"
  }

  function WriteError(reason: string): BW.Bytes {
    "realpath: write error: " + Utf8.Encode(reason) + "\n"
  }

  function Delimiter(raw: S.RealpathCmdRaw): BW.Bytes { if raw.zero then ['\0'] else "\n" }

  function AmbiguityOptions(name: string): BW.Bytes {
    if name == "--" then
      " '--canonicalize' '--canonicalize-existing' '--canonicalize-missing'" +
      " '--relative-to' '--relative-base' '--quiet' '--strip' '--no-symlinks'" +
      " '--zero' '--logical' '--physical' '--help' '--version'"
    else if |name| >= 3 && name[2] == 'r' then " '--relative-to' '--relative-base'"
    else if |name| <= |"--canonicalize"| then
      " '--canonicalize' '--canonicalize-existing' '--canonicalize-missing'"
    else " '--canonicalize-existing' '--canonicalize-missing'"
  }

  function ParseErrorText(err: CliTypes.ParseError, name: string,
                          invalid: BW.Bytes, fullName: string): BW.Bytes {
    var token := err.rawToken;
    var message :=
      if err.kind == CliTypes.UnknownOption then
        if |token| > 2 && token[..2] == "--" then
          "unrecognized option '" + Utf8.Encode(token) + "'"
        else "invalid option -- '" + invalid + "'"
      else if err.kind == CliTypes.MissingValue then
        "option '" + Utf8.Encode(token) + "' requires an argument"
      else if err.kind == CliTypes.UnexpectedValue then
        "option '" + Utf8.Encode(fullName) + "' doesn't allow an argument"
      else "option '" + Utf8.Encode(token) + "' is ambiguous; possibilities:" + AmbiguityOptions(name);
    "realpath: " + message + "\nTry 'realpath --help' for more information.\n"
  }

  datatype DirectoryResult = DirectoryReady(path: string) |
                             DirectoryFailure(operand: string, error: int, cannotStat: bool) | DirectoryMemory
  datatype DirectoryEvidence = DirectoryEvidence(canonical: PathResult,
                                                 status: Status, result: DirectoryResult)
  datatype Setup = RelativeReady(relativeTo: CliTypes.OptionalString,
                                 relativeBase: CliTypes.OptionalString) |
                   RelativeFailure(operand: string, error: int, cannotStat: bool) | RelativeMemory
  datatype RelativeEvidence = RelativeEvidence(toEvidence: DirectoryEvidence,
                                               baseEvidence: DirectoryEvidence, cursor: nat)

  ghost predicate DirectoryPreparation(fs: BW.FileSystem,
                                       failures: (BW.NativeFailureRequest) -> int, observations: BW.StatusTimeObservations,
                                       first: nat, last: nat, raw: S.RealpathCmdRaw,
                                       cwd: BW.IOResult<string>, operand: string, evidence: DirectoryEvidence) {
    Canonicalizes(fs, failures, observations, first, last, raw, cwd, operand, evidence.canonical) &&
    (if evidence.canonical.MemoryFatal? then evidence.status == NoStatus && evidence.result == DirectoryMemory
     else if evidence.canonical.Err? then
       evidence.status == NoStatus &&
       evidence.result == DirectoryFailure(operand, evidence.canonical.e, false)
     else if raw.existence != S.Existing then
       evidence.status == NoStatus &&
       evidence.result == DirectoryReady(evidence.canonical.v)
     else (StatusObservation(fs, failures, evidence.canonical.v, evidence.status) &&
           evidence.result ==
           (if !evidence.status.ok then
              DirectoryFailure(evidence.canonical.v, evidence.status.err, true)
            else if !evidence.status.directory then DirectoryFailure(operand, E.ENOTDIR, false)
            else DirectoryReady(evidence.canonical.v))))
  }

  function ToOperand(raw: S.RealpathCmdRaw): CliTypes.OptionalString {
    if raw.relativeTo.Some? then raw.relativeTo else raw.relativeBase
  }

  function SetupFailure(result: DirectoryResult): Setup
    requires !result.DirectoryReady?
  { if result.DirectoryMemory? then RelativeMemory else RelativeFailure(result.operand, result.error, result.cannotStat) }

  ghost predicate RelativeSetup(fs: BW.FileSystem,
                                failures: (BW.NativeFailureRequest) -> int, observations: BW.StatusTimeObservations,
                                first: nat, last: nat, raw: S.RealpathCmdRaw,
                                cwd: BW.IOResult<string>, setup: Setup, evidence: RelativeEvidence) {
    if ToOperand(raw).None? then setup == RelativeReady(CliTypes.None, CliTypes.None) && last == first
    else (DirectoryPreparation(fs, failures, observations, first, evidence.cursor, raw, cwd, ToOperand(raw).value, evidence.toEvidence) &&
          (if !evidence.toEvidence.result.DirectoryReady? then
             setup == SetupFailure(evidence.toEvidence.result) && last == evidence.cursor
           else if raw.relativeBase.None? then
             setup == RelativeReady(CliTypes.Some(evidence.toEvidence.result.path), CliTypes.None) && last == evidence.cursor
           else if raw.relativeTo.None? then
             setup == RelativeReady(CliTypes.Some(evidence.toEvidence.result.path),
                                    CliTypes.Some(evidence.toEvidence.result.path)) && last == evidence.cursor
           else (DirectoryPreparation(fs, failures, observations, evidence.cursor, last, raw, cwd, raw.relativeBase.value, evidence.baseEvidence) &&
                 (if !evidence.baseEvidence.result.DirectoryReady? then
                    setup == SetupFailure(evidence.baseEvidence.result)
                  else if PathPrefix(evidence.baseEvidence.result.path, evidence.toEvidence.result.path) then
                    setup == RelativeReady(CliTypes.Some(evidence.toEvidence.result.path),
                                           CliTypes.Some(evidence.baseEvidence.result.path))
                  else setup == RelativeReady(CliTypes.None, CliTypes.None)))))
  }

  ghost predicate OutputPath(setup: Setup, path: string, output: string) {
    setup.RelativeReady? &&
    if setup.relativeTo.Some? &&
       (setup.relativeBase.None? || PathPrefix(setup.relativeBase.value, path)) then
      RelativePath(setup.relativeTo.value, path, output)
    else output == path
  }

  ghost predicate OperandPiece(fs: BW.FileSystem,
                               failures: (BW.NativeFailureRequest) -> int, observations: BW.StatusTimeObservations,
                               first: nat, last: nat, raw: S.RealpathCmdRaw,
                               cwd: BW.IOResult<string>, setup: Setup, operand: string,
                                                result: PathResult, output: BW.Bytes, diagnostics: BW.Bytes) {
    Canonicalizes(fs, failures, observations, first, last, raw, cwd, operand, result) &&
    (if result.MemoryFatal? then output == [] && diagnostics == MemoryMessage()
     else if result.Err? then
       output == [] && diagnostics ==
                       (if raw.quiet then [] else ErrorMessage(operand, C.CLocaleErrnoTextResult(result.e)))
     else (diagnostics == [] &&
           exists rendered: string :: OutputPath(setup, result.v, rendered) &&
                                      output == Utf8.Encode(rendered) + Delimiter(raw)))
  }

  ghost predicate Partition(pieces: seq<BW.Bytes>, output: BW.Bytes, cuts: seq<nat>) {
    |cuts| == |pieces| + 1 && cuts[0] == 0 && cuts[|pieces|] == |output| &&
    (forall i: nat {:trigger cuts[i]} | i < |pieces| ::
       cuts[i] <= cuts[i + 1] <= |output| && output[cuts[i]..cuts[i + 1]] == pieces[i])
  }

  datatype OperandEvidence = OperandEvidence(results: seq<PathResult>, outputs: seq<BW.Bytes>,
                                             diagnostics: seq<BW.Bytes>, outputCuts: seq<nat>, diagnosticCuts: seq<nat>, statusCuts: seq<nat>)

  ghost predicate Operands(fs: BW.FileSystem,
                           failures: (BW.NativeFailureRequest) -> int, observations: BW.StatusTimeObservations,
                           first: nat, last: nat, raw: S.RealpathCmdRaw,
                           cwd: BW.IOResult<string>, setup: Setup, paths: seq<string>,
                                            output: BW.Bytes, diagnostics: BW.Bytes, exit: int, evidence: OperandEvidence) {
    var count := |evidence.results|;
    count <= |paths| && |evidence.outputs| == count && |evidence.diagnostics| == count &&
    |evidence.statusCuts| == count + 1 && evidence.statusCuts[0] == first && evidence.statusCuts[count] == last &&
    (count < |paths| ==> count > 0 && evidence.results[count - 1].MemoryFatal?) &&
    (forall i: nat | i + 1 < count :: !evidence.results[i].MemoryFatal?) &&
    (forall i: nat | i < count ::
       OperandPiece(fs, failures, observations, evidence.statusCuts[i], evidence.statusCuts[i + 1],
                    raw, cwd, setup, paths[i], evidence.results[i], evidence.outputs[i], evidence.diagnostics[i])) &&
    Partition(evidence.outputs, output, evidence.outputCuts) &&
    Partition(evidence.diagnostics, diagnostics, evidence.diagnosticCuts) &&
    exit == (if exists i: nat :: i < count && !evidence.results[i].Ok? then 1 else 0)
  }

  function SetupError(setup: Setup, reason: string): BW.Bytes
    requires setup.RelativeFailure?
  {
    if setup.cannotStat then
      "realpath: cannot stat " + SE.SpecQuoteAfBytes(Utf8.Encode(setup.operand)) + ": " +
      Utf8.Encode(reason) + "\n"
    else ErrorMessage(setup.operand, reason)
  }

  twostate predicate CwdObservation(io: BenchIO.IO, cwd: BW.IOResult<string>)
    reads io.directoryStateRegion, io.fsRegion, io.cwdRegion
  {
    var request := BW.DirectoryRequest(BW.DirectoryGetCwd, old(io.directoryOrdinal()),
                                       old(io.fs()), old(io.directoryTopology()), old(io.directoryPosition()),
                                       old(io.directoryCapabilities()), 0, 0, "", old(io.statusCursor()), old(io.cwd()),
                                       old(io.dirHandles()).Keys);
    var response := old(io.directoryObservations())(request);
    io.directoryModel() == old(io.directoryModel()) &&
    C.DirectoryOperationSpec(request, old(io.directoryObservations()), response,
                             io.directoryPosition(), io.directoryCapabilities(), io.directoryOrdinal(),
                             old(io.statusCursor()), io.cwd()) && cwd == C.DirectoryPathResultFields(response)
  }

  datatype Preparation = EarlyPreparation |
                         RunPreparation(cwd: BW.IOResult<string>, setup: Setup, relative: RelativeEvidence,
                                        operands: OperandEvidence, setupCursor: nat)

  twostate predicate Prepared(raw: S.RealpathCmdRaw, io: BenchIO.IO,
                              output: BW.Bytes, diagnostics: BW.Bytes, exit: int, evidence: Preparation)
    reads io.directoryStateRegion, io.fsRegion, io.cwdRegion, io.statusObservationsRegion,
          io.trustedNativeFailuresRegion
  {
    if raw.mode == S.Help then evidence == EarlyPreparation &&
                               output == HelpText() && diagnostics == [] && exit == 0 && io.statusCursor() == old(io.statusCursor())
    else if raw.mode == S.Version then evidence == EarlyPreparation &&
                                       output == VersionText() && diagnostics == [] && exit == 0 && io.statusCursor() == old(io.statusCursor())
    else if raw.operands == [] then evidence == EarlyPreparation &&
                                    output == [] && diagnostics == MissingOperand() && exit == 1 && io.statusCursor() == old(io.statusCursor())
    else (evidence.RunPreparation? && CwdObservation(io, evidence.cwd) &&
          RelativeSetup(old(io.fs()), old(io.trustedNativeFailures()), io.statusObservations(),
                        old(io.statusCursor()), evidence.setupCursor, raw, evidence.cwd, evidence.setup, evidence.relative) &&
          (if evidence.setup.RelativeMemory? then output == [] && diagnostics == MemoryMessage() && exit == 1 &&
                                                  io.statusCursor() == evidence.setupCursor
           else if evidence.setup.RelativeFailure? then
             io.statusCursor() == evidence.setupCursor && output == [] && exit == 1 && diagnostics ==
                                                                                       SetupError(evidence.setup, C.CLocaleErrnoTextResult(evidence.setup.error))
           else Operands(old(io.fs()), old(io.trustedNativeFailures()), io.statusObservations(),
                         evidence.setupCursor, io.statusCursor(), raw, evidence.cwd, evidence.setup, raw.operands,
                         output, diagnostics, exit, evidence.operands)))
  }

  ghost predicate EmissionOutcome(beforeOut: BW.Bytes, beforeErr: BW.Bytes,
                                  afterOut: BW.Bytes, afterErr: BW.Bytes,
                                  streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
                                  output: BW.Bytes, diagnostics: BW.Bytes, normalExit: int, exit: int,
                                  committed: nat, outError: int, errCommitted: nat, errError: int) {
    (if output == [] then afterOut == beforeOut && committed == 0 && outError == 0
     else C.WriteStdoutSpec(beforeOut, streams, afterOut, output, committed, outError)) &&
    var errors := diagnostics +
                  (if outError == 0 then [] else WriteError(C.CLocaleErrnoTextResult(outError)));
    (if errors == [] then afterErr == beforeErr && errCommitted == 0 && errError == 0
     else C.WriteStderrSpec(beforeErr, streams, afterErr, errors, errCommitted, errError)) &&
    exit == (if outError != 0 || errError != 0 then 1 else normalExit)
  }

  ghost predicate Emission(beforeOut: BW.Bytes, beforeErr: BW.Bytes,
                           afterOut: BW.Bytes, afterErr: BW.Bytes,
                           streams: (BW.TrustedStreamRequest) -> BW.TrustedStreamResult,
                           output: BW.Bytes, diagnostics: BW.Bytes, normalExit: int, exit: int) {
    exists committed: nat, outError: int, errCommitted: nat, errError: int ::
      EmissionOutcome(beforeOut, beforeErr, afterOut, afterErr, streams, output,
                      diagnostics, normalExit, exit, committed, outError, errCommitted, errError)
  }

  twostate predicate Spec(raw: S.RealpathCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.directoryStateRegion, io.fsRegion,
          io.cwdRegion, io.statusObservationsRegion, io.trustedNativeFailuresRegion,
          io.trustedStreamsRegion
  {
    exists output: BW.Bytes, diagnostics: BW.Bytes, normalExit: int, evidence: Preparation ::
      Prepared(raw, io, output, diagnostics, normalExit, evidence) &&
      Emission(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
               io.trustedStreams(), output, diagnostics, normalExit, exit)
  }

  function HelpText(): BW.Bytes {
    "Usage: realpath [OPTION]... FILE...\n" +
    "Print the resolved absolute file name.\n" +
    "  -E, --canonicalize           all but the last component must exist (default)\n" +
    "  -e, --canonicalize-existing  all components of the path must exist\n" +
    "  -m, --canonicalize-missing   no path components need exist or be a directory\n" +
    "  -L, --logical                resolve '..' components before symlinks\n" +
    "  -P, --physical               resolve symlinks as encountered (default)\n" +
    "  -q, --quiet                  suppress most error messages\n" +
    "      --relative-to=DIR        print the resolved path relative to DIR\n" +
    "      --relative-base=DIR      print absolute paths unless paths below DIR\n" +
    "  -s, --strip, --no-symlinks   don't expand symlinks\n" +
    "  -z, --zero                   end each output line with NUL, not newline\n" +
    "      --help\n" +
    "         display this help and exit\n" +
    "      --version\n" +
    "         output version information and exit\n" +
    "\n" +
    "Report bugs to: bug-coreutils@gnu.org\n" +
    "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n" +
    "General help using GNU software: <https://www.gnu.org/gethelp/>\n" +
    "Report any translation bugs to <https://translationproject.org/team/>\n" +
    "Full documentation <https://www.gnu.org/software/coreutils/realpath>\n" +
    "or available locally via: info '(coreutils) realpath invocation'\n"
  }

  function VersionText(): BW.Bytes {
    "realpath (GNU coreutils) 9.10.13-2cf49\n" +
    "Copyright (C) 2026 Free Software Foundation, Inc.\n" +
    "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n" +
    "This is free software: you are free to change and redistribute it.\n" +
    "There is NO WARRANTY, to the extent permitted by law.\n" +
    "\n" +
    "Written by Padraig Brady.\n"
  }
}
