include "ChmodRecursiveSpec.dfy"
include "ChmodOperandSpec.dfy"

module ChmodDescriptorSpec {
  import W = BenchWorld
  import Errno = Errnos
  import C = IOContract
  import Base = ChmodSpec
  import Recursive = ChmodRecursiveSpec
  import Operand = ChmodOperandSpec
  import Schema = ChmodSchema
  import R = Results

  datatype RootGuard = RootUnchecked | RootChecked(key: W.HostInodeKey)
  datatype Scope = Scope(ghost context: Base.ObservationContext, ghost cwd: W.Path, ghost now: int,
    root: RootGuard, ghost directories: W.DirectoryObservations)
  datatype State = State(fs: W.FileSystem, cursor: nat, native: W.CwdContext,
    output: W.Bytes, diagnostics: W.Bytes, ok: bool)
  datatype Decision = EntrySkipped | EntryFailed(err: int, kind: Recursive.RecursiveFailureKind) |
    EntryPreserved(alias: bool) | EntryReady
  datatype RuntimeIdentity = RuntimeIdentity(displayPath: string, operand: Operand.Operand, top: bool,
    isSymlink: bool, isDirectory: bool, metadataFollow: bool, key: W.HostInodeKey)
  datatype Entry = Entry(identity: RuntimeIdentity, fs: W.FileSystem, native: W.CwdContext, cursor: nat,
    rawAttempts: nat, targets: seq<W.CwdTarget>, decision: Decision, result: State)
  datatype Change = Change(result: State, setFs: W.FileSystem, setNative: W.CwdContext,
    setErr: int, desired: bv32)
  datatype DirectoryRead = DirectoryRead(before: W.CwdContext, after: W.CwdContext,
    response: W.DirectoryResponse)
  datatype Listing = ListingSkipped | ListingOpenFailed(err: int, afterOpen: W.CwdContext) |
    ListingOpened(afterOpen: W.CwdContext, handle: int, readSteps: seq<DirectoryRead>, children: seq<Visit>,
      states: seq<State>, closeResponse: W.DirectoryResponse, afterClose: W.CwdContext)
  datatype Visit = EntryVisit(entry: Entry) | NodeVisit(entry: Entry, change: Change, listing: Listing, result: State)
  datatype Files = Files(visits: seq<Visit>, states: seq<State>)

  // With nonrecursive -P, FTS supplies physical metadata but an implicit
  // dereference still changes the top-level referent (chmod.c:266,310).
  function MetadataFollow(cmd: Schema.ChmodCmd, top: bool): bool
  {
    if !cmd.recursive then
      if Base.SpecUsesPhysicalTopLevelMetadata(cmd) then false
      else if cmd.dereferenceMode == 0 then cmd.traversalMode != 0
      else true
    else Recursive.TraversalFollowSpec(cmd, top) || cmd.dereferenceMode == 1
  }

  function ModeFollow(cmd: Schema.ChmodCmd, top: bool): bool
  {
    if !cmd.recursive then Base.ShouldDereference(cmd)
    else Recursive.ChmodFollowSpec(cmd, top)
  }

  ghost function Result(visit: Visit): State
  {
    if visit.EntryVisit? then visit.entry.result else visit.result
  }

  ghost function NamedTarget(entry: Entry): seq<W.Path>
  {
    if |entry.targets| == 1 then C.CwdTargetNamedPathFields(entry.native, entry.targets[0]) else []
  }

  ghost function MathematicalIdentity(scope: Scope, entry: Entry): Recursive.RecursiveIdentity
  {
    Recursive.RecursiveIdentity(entry.identity.displayPath,
      Operand.ModelPath(scope.cwd, entry.native, entry.identity.operand),
      if |NamedTarget(entry)| == 1 then NamedTarget(entry)[0] else "",
      entry.identity.top, entry.identity.isSymlink, entry.identity.isDirectory)
  }

  ghost predicate EntryFields(cmd: Schema.ChmodCmd, scope: Scope, display: string, operand: Operand.Operand,
    top: bool, fs: W.FileSystem, native: W.CwdContext, cursor: nat, entry: Entry)
  {
    var identity := entry.identity;
    var context := Base.AtCursor(scope.context, cursor);
    var first := Operand.StatusAt(context, fs, native, operand, 0, false);
    var attempts: nat := if top && first.Err? then 2 else 1;
    var raw := Operand.StatusAt(context, fs, native, operand, attempts-1, false);
    entry.fs == fs && entry.native == native && entry.cursor == cursor && entry.rawAttempts == attempts &&
    identity.operand == operand && identity.displayPath == display && identity.top == top &&
    if raw.Err? then
      entry.targets == [] && identity.key == W.HostInodeKey(0, 0) && !identity.metadataFollow &&
      !identity.isSymlink && !identity.isDirectory &&
      entry.decision == EntryFailed(C.ResultErrno(raw), Recursive.RecursiveAccess) &&
      entry.result == State(fs, cursor+attempts, Operand.AtOffset(native, attempts),
        Recursive.RecursiveAccessStdoutSpec(cmd, display),
        Recursive.NativeAccessText(cmd, display, Recursive.RecursiveAccess,
          C.CLocaleErrnoTextResult(C.ResultErrno(raw))), false)
    else
      var link := raw.v.kind == W.SymlinkKind;
      var metadata := Operand.StatusAt(context, fs, native, operand, attempts, MetadataFollow(cmd, top));
      identity.isSymlink == link &&
      if metadata.Err? then
        if link && !ModeFollow(cmd, top) && MetadataFollow(cmd, top) && C.ResultErrno(metadata) == Errno.ENOENT then
          var resolved := Operand.ResolveTarget(fs, Operand.AtOffset(native, attempts-1), operand, false);
          resolved.Ok? && entry.targets == [resolved.v] &&
          C.CwdTargetFields(fs, native, resolved.v) &&
          identity.key == raw.v.hostKey == C.CwdTargetRecordFields(fs, native, resolved.v).hostKey &&
          C.CwdTargetRecordFields(fs, native, resolved.v).node.Symlink? &&
          !identity.isDirectory && !identity.metadataFollow && entry.decision.EntryReady? &&
          entry.result == State(fs, cursor+attempts+1, Operand.AtOffset(native, attempts+1), [], [], true)
        else
          var kind := Recursive.ResolutionFailureKindSpec(cmd, top, link, C.ResultErrno(metadata));
          entry.targets == [] && identity.key == raw.v.hostKey && !identity.isDirectory &&
          identity.metadataFollow == MetadataFollow(cmd, top) &&
          entry.decision == EntryFailed(C.ResultErrno(metadata), kind) &&
          entry.result == State(fs, cursor+attempts+1, Operand.AtOffset(native, attempts+1),
            Recursive.RecursiveAccessStdoutSpec(cmd, display),
            Recursive.NativeAccessText(cmd, display, kind,
              C.CLocaleErrnoTextResult(C.ResultErrno(metadata))), false)
      else
        var resolved := Operand.ResolveTarget(fs, Operand.AtOffset(native, attempts), operand, MetadataFollow(cmd, top));
        resolved.Ok? && entry.targets == [resolved.v] && C.CwdTargetFields(fs, native, resolved.v) &&
        identity.metadataFollow == MetadataFollow(cmd, top) &&
        identity.isDirectory == (metadata.v.kind == W.DirectoryKind) &&
        identity.isDirectory == C.CwdTargetRecordFields(fs, native, resolved.v).node.Directory? &&
        identity.key == metadata.v.hostKey == C.CwdTargetRecordFields(fs, native, resolved.v).hostKey &&
        (cmd.recursive && cmd.preserveRoot ==> scope.root.RootChecked?) &&
        if cmd.recursive && cmd.preserveRoot && identity.isDirectory &&
          scope.root.RootChecked? && identity.key == scope.root.key then
          entry.decision == EntryPreserved(display != "/") &&
          entry.result == State(fs, cursor+attempts+1, Operand.AtOffset(native, attempts+1), [],
            Recursive.RootPreserveMessageSpec(display, display != "/"), false)
        else
          entry.decision.EntryReady? &&
          entry.result == State(fs, cursor+attempts+1, Operand.AtOffset(native, attempts+1), [], [], true)
  }

  ghost predicate SuccessFields(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan, scope: Scope,
    entry: Entry, fs: W.FileSystem, native: W.CwdContext, cursor: nat, before: bv32, requested: bv32,
    afterCursor: nat, afterNative: W.CwdContext, result: Base.SpecPathResult)
  {
    var context := Base.AtCursor(scope.context, cursor);
    var post := Operand.StatusAt(context, fs, native, entry.identity.operand, 0, true);
    var count: nat := if Base.SpecPostChangeLookupNeeded(cmd, requested) then 1 else 0;
    afterCursor == cursor+count && afterNative == Operand.AtOffset(native, count) &&
    Base.SuccessOutputRelation(cmd, plan, entry.identity.displayPath, before, requested,
      entry.identity.isDirectory, fs, post.Ok?, C.ResultValue(post, W.DEFAULT_FILE_STATUS).mode,
      C.ResultErrno(post), result)
  }

  ghost predicate ChangeFields(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan, scope: Scope,
    entry: Entry, fs: W.FileSystem, native: W.CwdContext, cursor: nat, change: Change)
  {
    var identity := entry.identity;
    var context := Base.AtCursor(scope.context, cursor);
    var mode := Operand.StatusAt(context, fs, native, identity.operand, 0, identity.metadataFollow);
    if mode.Err? then
      var kind := Recursive.ResolutionFailureKindSpec(cmd, identity.top, identity.isSymlink, C.ResultErrno(mode));
      change.setFs == fs && change.setNative == Operand.AtOffset(native, 1) &&
      change.setErr == 0 && change.desired == 0 as bv32 &&
      change.result == State(fs, cursor+1, Operand.AtOffset(native, 1),
        Recursive.RecursiveAccessStdoutSpec(cmd, identity.displayPath),
        Recursive.NativeAccessText(cmd, identity.displayPath, kind,
          C.CLocaleErrnoTextResult(C.ResultErrno(mode))), false)
    else
      Base.SpecPlannedModeRelation(plan, mode.v.mode, identity.isDirectory, change.desired) &&
      Operand.SetFields(Base.AtCursor(context, cursor+1), scope.now, fs, Operand.AtOffset(native, 1),
        identity.operand, ModeFollow(cmd, identity.top), change.desired, change.setFs, change.setNative,
        change.setErr == 0, change.setErr) &&
      if change.setErr != 0 then
        if Base.ModeNotSupported(change.setErr) then
          change.result == State(change.setFs, cursor+1, change.setNative,
            Recursive.RecursiveSkipStdoutSpec(cmd, identity.displayPath), [], true)
        else
          change.result == State(change.setFs, cursor+1, change.setNative,
            if cmd.verbose then Base.FailedChangeMessageSpec(identity.displayPath, mode.v.mode, change.desired) else [],
            if cmd.silent then [] else Base.ChangeErrorMessageSpec(identity.displayPath,
              C.CLocaleErrnoTextResult(change.setErr)), false)
      else
        exists result: Base.SpecPathResult ::
          SuccessFields(cmd, plan, scope, entry, change.setFs, change.setNative, cursor+1,
            mode.v.mode, W.NormalizeMode(change.desired), change.result.cursor, change.result.native, result) &&
          change.result == State(change.setFs, change.result.cursor, change.result.native,
            result.stdoutChunk, result.stderrChunk, result.ok)
  }

  ghost predicate ReadFields(scope: Scope, fs: W.FileSystem, cursor: nat, handle: int, read: DirectoryRead)
  {
    C.ContextOperationSpec(fs, read.before, scope.directories, W.DirectoryReadNext, handle, 0, "",
      cursor, cursor, read.response, read.after)
  }

  ghost predicate VisitFields(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan, scope: Scope,
    display: string, operand: Operand.Operand, top: bool, active: set<W.HostInodeKey>,
    fs: W.FileSystem, native: W.CwdContext, cursor: nat, visit: Visit)
    decreases visit
  {
    EntryFields(cmd, scope, display, operand, top, fs, native, cursor, visit.entry) &&
    match visit
    case EntryVisit(entry) => !entry.decision.EntryReady?
    case NodeVisit(entry, change, listing, result) =>
      entry.decision.EntryReady? &&
      ChangeFields(cmd, plan, scope, entry, fs, entry.result.native, entry.result.cursor, change) &&
      var identity := entry.identity;
      if !cmd.recursive || !identity.isDirectory ||
        (identity.isSymlink && !Recursive.TraversalFollowSpec(cmd, top)) || identity.key in active then
        listing.ListingSkipped? && result == change.result
      else
        match listing
        case ListingSkipped => false
        case ListingOpenFailed(err, afterOpen) =>
          Operand.OpenFields(Base.AtCursor(scope.context, change.result.cursor), change.result.fs,
            change.result.native, operand, afterOpen, false, 0, err) &&
          result == State(change.result.fs, change.result.cursor, afterOpen,
            change.result.output + (if cmd.verbose then Base.AccessFailureMessageSpec(display) else []),
            change.result.diagnostics + (if cmd.silent then [] else
              Recursive.ReadDirectoryText(display, C.CLocaleErrnoTextResult(err))), false)
        case ListingOpened(afterOpen, handle, readSteps, children, states, closeResponse, afterClose) =>
          Operand.OpenFields(Base.AtCursor(scope.context, change.result.cursor), change.result.fs,
            change.result.native, operand, afterOpen, true, handle, 0) &&
          |states| == |readSteps| == |children|+1 && states[0] == change.result.(native := afterOpen) &&
          (forall i: nat | i < |children| ::
            DirectoryStepFields(cmd, plan, scope, identity, active, handle,
              states[i], states[i+1], readSteps[i], children[i])) &&
          var n := |children|;
          var terminal := readSteps[n];
          var last := states[n];
          terminal.before == last.native && ReadFields(scope, last.fs, last.cursor, handle, terminal) &&
          (terminal.response.err != 0 || terminal.response.read.DirectoryEnd?) &&
          C.ContextOperationSpec(last.fs, terminal.after, scope.directories, W.DirectoryClose,
            handle, 0, "", last.cursor, last.cursor, closeResponse, afterClose) &&
          result == State(last.fs, last.cursor, afterClose,
            last.output + (if terminal.response.err != 0 && cmd.verbose then Base.AccessFailureMessageSpec(display) else []),
            last.diagnostics + (if terminal.response.err == 0 || cmd.silent then [] else
              Recursive.TerminalReadDirectoryText(display, n > 0, C.CLocaleErrnoTextResult(terminal.response.err))),
            last.ok && terminal.response.err == 0)
  }

  ghost predicate DirectoryStepFields(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan, scope: Scope,
    identity: RuntimeIdentity, active: set<W.HostInodeKey>, handle: int,
    before: State, after: State, read: DirectoryRead, child: Visit)
  {
    read.before == before.native && ReadFields(scope, before.fs, before.cursor, handle, read) &&
    read.response.err == 0 && read.response.read.DirectoryItem? &&
    VisitFields(cmd, plan, scope, W.AppendPath(identity.displayPath, read.response.read.name),
      Operand.DirectoryOperand(handle, read.response.read.name), false, active+{identity.key},
      before.fs, read.after, before.cursor, child) &&
    var result := Result(child);
    after == State(result.fs, result.cursor, result.native, before.output+result.output,
      before.diagnostics+result.diagnostics, before.ok && result.ok)
  }

  ghost predicate DirectoryPrefixFields(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan, scope: Scope,
    identity: RuntimeIdentity, active: set<W.HostInodeKey>, handle: int, initial: State,
    readSteps: seq<DirectoryRead>, children: seq<Visit>, states: seq<State>, current: W.CwdContext)
  {
    |readSteps| == |children| && |states| == |children|+1 && states[0] == initial &&
    current == states[|children|].native &&
    forall i: nat | i < |children| ::
      DirectoryStepFields(cmd, plan, scope, identity, active, handle,
        states[i], states[i+1], readSteps[i], children[i])
  }

  ghost predicate FileStepFields(file: string, cmd: Schema.ChmodCmd, plan: Base.SpecModePlan, scope: Scope,
    before: State, after: State, visit: Visit)
  {
    VisitFields(cmd, plan, scope, file, Operand.CwdOperand(file), true, {},
      before.fs, before.native, before.cursor, visit) &&
    var step := Result(visit);
    after == State(step.fs, step.cursor, step.native, before.output+step.output,
      before.diagnostics+step.diagnostics, before.ok && step.ok)
  }

  ghost predicate FilesFields(files: seq<string>, cmd: Schema.ChmodCmd, plan: Base.SpecModePlan, scope: Scope,
    fs: W.FileSystem, native: W.CwdContext, cursor: nat, result: State, observation: Files)
  {
    |observation.visits| == |files| && |observation.states| == |files|+1 &&
    observation.states[0] == State(fs, cursor, native, [], [], true) && observation.states[|files|] == result &&
    forall i: nat | i < |files| ::
      FileStepFields(files[i], cmd, plan, scope, observation.states[i], observation.states[i+1], observation.visits[i])
  }

  ghost predicate SuccessfulEntry(cmd: Schema.ChmodCmd, scope: Scope, entry: Entry)
  {
    var context := Base.AtCursor(scope.context, entry.cursor);
    var metadata := Operand.StatusAt(context, entry.fs, entry.native, entry.identity.operand,
      entry.rawAttempts, MetadataFollow(cmd, entry.identity.top));
    Operand.StatusAt(context, entry.fs, entry.native, entry.identity.operand, 0, false).Ok? &&
    (metadata.Ok? || (entry.identity.isSymlink && !ModeFollow(cmd, entry.identity.top) && MetadataFollow(cmd, entry.identity.top) &&
      C.ResultErrno(metadata) == Errno.ENOENT))
  }

  ghost predicate CompatibleResolution(scope: Scope, fs: W.FileSystem, native: W.CwdContext,
    operand: Operand.Operand, follow: bool)
  {
    var actual := Operand.ResolveTarget(fs, native, operand, follow);
    actual.Ok? && |C.CwdTargetNamedPathFields(native, actual.v)| == 1 &&
    C.ResolvePathForMetadataFields(fs, Operand.ModelPath(scope.cwd, native, operand), follow) ==
      R.Ok(C.CwdTargetNamedPathFields(native, actual.v)[0])
  }

  ghost predicate CompatibleEntry(cmd: Schema.ChmodCmd, scope: Scope, entry: Entry)
  {
    CompatibleResolution(scope, entry.fs, entry.native, entry.identity.operand, false) &&
    CompatibleResolution(scope, entry.fs, Operand.AtOffset(entry.native, entry.rawAttempts),
      entry.identity.operand, entry.identity.metadataFollow) &&
    (entry.identity.metadataFollow != MetadataFollow(cmd, entry.identity.top) ==>
      C.ResolvePathForMetadataFields(entry.fs, Operand.ModelPath(scope.cwd, entry.native, entry.identity.operand), true).Err? &&
      C.MetadataFailureErrFields(entry.fs, Operand.ModelPath(scope.cwd, entry.native, entry.identity.operand), true) == Errno.ENOENT) &&
    ((cmd.recursive && cmd.preserveRoot && entry.identity.isDirectory &&
        scope.root.RootChecked? && entry.identity.key == scope.root.key) <==>
      (cmd.recursive && cmd.preserveRoot && entry.identity.isDirectory &&
        MathematicalIdentity(scope, entry).resolvedPath == "/"))
  }

  ghost predicate SuccessfulChange(cmd: Schema.ChmodCmd, scope: Scope, entry: Entry, change: Change)
  {
    var context := Base.AtCursor(scope.context, entry.result.cursor);
    Operand.StatusAt(context, entry.fs, entry.result.native, entry.identity.operand, 0, entry.identity.metadataFollow).Ok? &&
    (change.setErr == 0 || (entry.identity.isSymlink && !ModeFollow(cmd, entry.identity.top) &&
      Base.ModeNotSupported(change.setErr))) &&
    (change.setErr != 0 || !Base.SpecPostChangeLookupNeeded(cmd, W.NormalizeMode(change.desired)) ||
      Operand.StatusAt(Base.AtCursor(context, context.cursor+1), change.setFs, change.setNative,
        entry.identity.operand, 0, true).Ok?)
  }

  ghost predicate CompatibleChange(cmd: Schema.ChmodCmd, scope: Scope, entry: Entry, change: Change)
  {
    if entry.identity.isSymlink && !ModeFollow(cmd, entry.identity.top) then true else
      CompatibleResolution(scope, entry.fs, entry.result.native, entry.identity.operand, entry.identity.metadataFollow) &&
      CompatibleResolution(scope, entry.fs, Operand.AtOffset(entry.result.native, 1),
        entry.identity.operand, ModeFollow(cmd, entry.identity.top)) &&
      (!Base.SpecPostChangeLookupNeeded(cmd, W.NormalizeMode(change.desired)) ||
        CompatibleResolution(scope, change.setFs, change.setNative, entry.identity.operand, true))
  }

  ghost predicate SuccessfulVisit(cmd: Schema.ChmodCmd, scope: Scope, visit: Visit)
    decreases visit
  {
    SuccessfulEntry(cmd, scope, visit.entry) &&
    if visit.EntryVisit? then true else
      SuccessfulChange(cmd, scope, visit.entry, visit.change) &&
      match visit.listing
      case ListingSkipped => true
      case ListingOpenFailed(_, _) => false
      case ListingOpened(_, _, readSteps, children, _, _, _) =>
        |readSteps| == |children|+1 && readSteps[|children|].response.err == 0 &&
        forall i: nat | i < |children| :: SuccessfulVisit(cmd, scope, children[i])
  }

  ghost predicate CompatibleVisit(cmd: Schema.ChmodCmd, scope: Scope,
    keys: set<W.HostInodeKey>, paths: set<seq<string>>, visit: Visit)
    decreases visit
  {
    CompatibleEntry(cmd, scope, visit.entry) &&
    if visit.EntryVisit? then true else
      CompatibleChange(cmd, scope, visit.entry, visit.change) &&
      var identity := MathematicalIdentity(scope, visit.entry);
      (visit.entry.identity.isDirectory ==>
        (visit.entry.identity.key in keys <==> W.PathSegments(identity.resolvedPath) in paths)) &&
      match visit.listing
      case ListingSkipped => true
      case ListingOpenFailed(_, _) => true
      case ListingOpened(_, _, _, children, _, _, _) =>
        forall i: nat | i < |children| ::
          CompatibleVisit(cmd, scope, keys+{visit.entry.identity.key},
            paths+{W.PathSegments(identity.resolvedPath)}, children[i])
  }

  ghost predicate SuccessfulFiles(cmd: Schema.ChmodCmd, scope: Scope, observation: Files)
  {
    forall i: nat | i < |observation.visits| :: SuccessfulVisit(cmd, scope, observation.visits[i])
  }

  ghost predicate CompatibleFiles(cmd: Schema.ChmodCmd, scope: Scope, observation: Files)
  {
    forall i: nat | i < |observation.visits| :: CompatibleVisit(cmd, scope, {}, {}, observation.visits[i])
  }
}
