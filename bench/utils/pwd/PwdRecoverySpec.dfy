include "../../core/IO.dfy"
include "../../core/Utf8.dfy"

module PwdRecoverySpec {
  import BenchIO
  import BenchWorld
  import Errno = Errnos
  import StreamContract = IOContract
  import Utf8 = Utf8Semantics

  // Recovery observations are utility-owned values. Native request bindings are
  // supplied by the later IO bridge, independently of these selection relations.
  datatype RecoveryFailure =
    | MemoryExhausted
    | RootAttributesFailed(err: int)
    | CurrentDirectoryStatusFailed(err: int)
    | ParentOpenFailed(height: nat, err: int)
    | ParentChdirFailed(height: nat, err: int)
    | ParentStatusFailed(height: nat, err: int)
    | ParentReadFailed(height: nat, err: int)
    | ParentEntryMissing(height: nat)

  function RecoveryFailureErr(failure: RecoveryFailure): int
  {
    match failure
    case MemoryExhausted => 0
    case ParentEntryMissing(_) => 0
    case _ => failure.err
  }

  ghost predicate ValidRecoveryFailure(failure: RecoveryFailure)
  {
    (failure.MemoryExhausted? || failure.ParentEntryMissing? || failure.err > 0) &&
    (failure.MemoryExhausted? || failure.RootAttributesFailed? ||
     failure.CurrentDirectoryStatusFailed? || failure.height >= 1)
  }

  function ParentArgumentText(height: nat): string
    requires height >= 1
  {
    seq(3 * height - 1, i => if i % 3 == 2 then '/' else '.')
  }

  function RecoveryFailureText(failure: RecoveryFailure,
    quotedArgument: BenchWorld.Bytes, reason: string): BenchWorld.Bytes
  {
    var suffix := ": " + Utf8.Encode(reason) + "\n";
    match failure
    case MemoryExhausted => "pwd: memory exhausted\n"
    case RootAttributesFailed(_) =>
      "pwd: failed to get attributes of " + quotedArgument + suffix
    case CurrentDirectoryStatusFailed(_) =>
      "pwd: failed to stat " + quotedArgument + suffix
    case ParentOpenFailed(_, _) =>
      "pwd: cannot open directory " + quotedArgument + suffix
    case ParentChdirFailed(_, _) =>
      "pwd: failed to chdir to " + quotedArgument + suffix
    case ParentStatusFailed(_, _) =>
      "pwd: failed to stat " + quotedArgument + suffix
    case ParentReadFailed(_, _) =>
      "pwd: reading directory " + quotedArgument + suffix
    case ParentEntryMissing(_) =>
      "pwd: couldn't find directory entry in " + quotedArgument + " with matching i-node\n"
  }

  ghost function RecoveryDiagnosticSpec(failure: RecoveryFailure): BenchWorld.Bytes
    requires ValidRecoveryFailure(failure)
  {
    var quoted :=
      if failure.MemoryExhausted? then ""
      else if failure.RootAttributesFailed? then StreamContract.QuoteafPathResult("/")
      else if failure.CurrentDirectoryStatusFailed? then StreamContract.QuoteafPathResult(".")
      else StreamContract.QuoteArgumentResult(Utf8.Encode(ParentArgumentText(failure.height)));
    var reason := if RecoveryFailureErr(failure) == 0 then ""
      else StreamContract.CLocaleErrnoTextResult(RecoveryFailureErr(failure));
    RecoveryFailureText(failure, quoted, reason)
  }

  ghost predicate LogicalTextFields(pwd: string)
  {
    BenchWorld.IsAbsolutePath(pwd) &&
    var components := BenchWorld.SplitSegments(BenchWorld.StripLeadingSlash(pwd), 0, 0);
    "." !in components && ".." !in components
  }

  ghost predicate LogicalSelectionFields(pwd: string,
    observations: seq<BenchWorld.IOResult<BenchWorld.FileStatus>>, selected: bool)
  {
    if !LogicalTextFields(pwd) then |observations| == 0 && !selected
    else
      |observations| >= 1 &&
      if observations[0].Err? then |observations| == 1 && !selected
      else
        |observations| == 2 &&
        (selected <==> observations[1].Ok? &&
          observations[0].v.hostKey == observations[1].v.hostKey)
  }

  datatype EntryObservation = EntryObservation(
    read: BenchWorld.IOResult<BenchWorld.DirectoryRead>,
    entryStatus: seq<BenchWorld.IOResult<BenchWorld.FileStatus>>)

  ghost predicate EntryNameFields(name: string)
  {
    BenchWorld.InodeChildNameValid(name)
  }

  ghost predicate EntryNeedsStatusFields(child: BenchWorld.FileStatus,
    parent: BenchWorld.FileStatus, entry: BenchWorld.DirectoryRead)
  {
    entry.DirectoryItem? &&
    (entry.inode == 0 || parent.hostKey.device != child.hostKey.device)
  }

  ghost predicate EntryObservationFields(child: BenchWorld.FileStatus,
    parent: BenchWorld.FileStatus, observation: EntryObservation)
  {
    if observation.read.Err? then
      |observation.entryStatus| == 0 && StreamContract.ResultErrno(observation.read) > 0
    else if observation.read.v.DirectoryEnd? then |observation.entryStatus| == 0
    else
      EntryNameFields(observation.read.v.name) &&
      if EntryNeedsStatusFields(child, parent, observation.read.v) then
        |observation.entryStatus| == 1 &&
        (observation.entryStatus[0].Err? ==>
          StreamContract.ResultErrno(observation.entryStatus[0]) > 0)
      else |observation.entryStatus| == 0
  }

  ghost predicate EntryMatchFields(child: BenchWorld.FileStatus,
    parent: BenchWorld.FileStatus, observation: EntryObservation)
  {
    EntryObservationFields(child, parent, observation) &&
    observation.read.Ok? && observation.read.v.DirectoryItem? &&
    if EntryNeedsStatusFields(child, parent, observation.read.v) then
      observation.entryStatus[0].Ok? &&
      observation.entryStatus[0].v.hostKey.inode == child.hostKey.inode &&
      (parent.hostKey.device == child.hostKey.device ||
       observation.entryStatus[0].v.hostKey.device == child.hostKey.device)
    else observation.read.v.inode == child.hostKey.inode
  }

  ghost predicate EntrySearchFields(child: BenchWorld.FileStatus,
    parent: BenchWorld.FileStatus, observations: seq<EntryObservation>,
    foundName: string, readErr: int)
  {
    |observations| > 0 &&
    (forall i: nat | i < |observations| :: EntryObservationFields(child, parent, observations[i])) &&
    (forall i: nat | i + 1 < |observations| ::
      observations[i].read.Ok? && observations[i].read.v.DirectoryItem? &&
      !EntryMatchFields(child, parent, observations[i])) &&
    var last := observations[|observations| - 1];
    if last.read.Err? then
      foundName == "" && readErr == StreamContract.ResultErrno(last.read)
    else if last.read.v.DirectoryEnd? then foundName == "" && readErr == 0
    else EntryMatchFields(child, parent, last) &&
      foundName == last.read.v.name && readErr == 0
  }

  ghost predicate ParentCompletionFields(height: nat, readErr: int,
    closeErr: int, found: bool, failure: seq<RecoveryFailure>)
  {
    height >= 1 && readErr >= 0 && closeErr >= 0 &&
    if readErr != 0 then failure == [ParentReadFailed(height, readErr)]
    else if closeErr != 0 then failure == [ParentReadFailed(height, closeErr)]
    else if !found then failure == [ParentEntryMissing(height)]
    else |failure| == 0
  }

  ghost predicate RecoveredDirectoryFields(root: BenchWorld.FileStatus,
    initial: BenchWorld.FileStatus, parents: seq<BenchWorld.FileStatus>,
    names: seq<string>, searches: seq<seq<EntryObservation>>,
    accesses: seq<ParentAccessObservation>, closes: seq<BenchWorld.IOResult<BenchWorld.Unit>>, directory: string)
  {
    root.kind == BenchWorld.DirectoryKind && initial.kind == BenchWorld.DirectoryKind &&
    |parents| == |names| == |searches| == |accesses| == |closes| &&
    (forall i: nat | i < |parents| ::
      var child := if i == 0 then initial else parents[i - 1];
      parents[i].kind == BenchWorld.DirectoryKind &&
      SuccessfulParentAccessFields(accesses[i], parents[i]) &&
      child.hostKey != root.hostKey &&
      EntryNameFields(names[i]) &&
      EntrySearchFields(child, parents[i], searches[i], names[i], 0) &&
      closes[i].Ok?) &&
    (if |parents| == 0 then initial.hostKey else parents[|parents| - 1].hostKey) == root.hostKey &&
    BenchWorld.IsAbsolutePath(directory) && BenchWorld.NormalizePath(directory) == directory &&
    var components := BenchWorld.SplitSegments(BenchWorld.StripLeadingSlash(directory), 0, 0);
    |components| == |names| &&
    (forall i: nat | i < |names| :: components[i] == names[|names| - 1 - i])
  }


  datatype PhysicalStart = ReturnedDirectory(directory: string) | RecoverDirectory | FatalAllocation

  ghost predicate PhysicalStartFields(result: BenchWorld.IOResult<string>, choice: PhysicalStart)
  {
    if result.Ok? then choice == ReturnedDirectory(result.v)
    else
      StreamContract.ResultErrno(result) > 0 &&
      if StreamContract.ResultErrno(result) == Errno.ENOMEM then choice == FatalAllocation
      else choice == RecoverDirectory
  }


  datatype ParentAccess = UseDirectoryDescriptor(fd: int) | UseRelativeParent

  ghost predicate ParentAccessFields(descriptor: BenchWorld.IOResult<int>, choice: ParentAccess)
  {
    if descriptor.Ok? then descriptor.v >= 0 && choice == UseDirectoryDescriptor(descriptor.v)
    else StreamContract.ResultErrno(descriptor) > 0 && choice == UseRelativeParent
  }

  datatype ParentAccessObservation = ParentAccessObservation(
    descriptor: BenchWorld.IOResult<int>, movement: BenchWorld.IOResult<BenchWorld.Unit>,
    status: BenchWorld.IOResult<BenchWorld.FileStatus>)

  ghost predicate SuccessfulParentAccessFields(observation: ParentAccessObservation,
    parent: BenchWorld.FileStatus)
  {
    (if observation.descriptor.Ok? then observation.descriptor.v >= 0
     else StreamContract.ResultErrno(observation.descriptor) > 0) &&
    observation.movement.Ok? && observation.status.Ok? && observation.status.v == parent
  }

  datatype DirectoryOutcome = DirectoryRecovered(directory: string) | DirectoryFailed(failure: RecoveryFailure)

  ghost predicate DirectoryOutcomeFields(outcome: DirectoryOutcome)
  {
    if outcome.DirectoryFailed? then ValidRecoveryFailure(outcome.failure)
    else BenchWorld.IsAbsolutePath(outcome.directory)
  }

  function WriteErrorText(reason: string): BenchWorld.Bytes
  {
    "pwd: write error: " + Utf8.Encode(reason) + "\n"
  }

  datatype RuntimeInputs = RuntimeInputs(
    ghost fs: BenchWorld.FileSystem,
    ghost topology: BenchWorld.LiveDirectoryTopology,
    ghost observations: BenchWorld.DirectoryObservations,
    ghost times: BenchWorld.StatusTimeObservations,
    ghost failures: (BenchWorld.NativeFailureRequest) -> int,
    ghost occupiedLegacyHandles: set<int>)

  datatype RuntimeState = RuntimeState(
    ghost position: BenchWorld.DirectoryPosition,
    ghost capabilities: map<int,BenchWorld.DirectoryCapabilityState>,
    ghost ordinal: nat, ghost statusOrdinal: nat, ghost cwdHint: BenchWorld.Path)

  datatype RuntimeAction =
    | DirectoryAction(ghost request: BenchWorld.DirectoryRequest,
                      ghost response: BenchWorld.DirectoryResponse)
    | AbsoluteStatusAction(ghost path: BenchWorld.Path, ghost follow: bool,
                           ghost result: BenchWorld.IOResult<BenchWorld.FileStatus>)

  datatype RuntimeObservation = RuntimeObservation(
    ghost before: RuntimeState, ghost after: RuntimeState, ghost action: RuntimeAction)

  ghost predicate RuntimeObservationFields(inputs: RuntimeInputs, observation: RuntimeObservation)
  {
    var before := observation.before;
    var after := observation.after;
    match observation.action
    case DirectoryAction(request,response) =>
      request.fs == inputs.fs && request.topology == inputs.topology &&
      request.position == before.position && request.capabilities == before.capabilities &&
      request.ordinal == before.ordinal && request.statusOrdinal == before.statusOrdinal &&
      request.cwdHint == before.cwdHint &&
      request.occupiedLegacyHandles == inputs.occupiedLegacyHandles &&
      StreamContract.DirectoryOperationSpec(request,inputs.observations,response,
        after.position,after.capabilities,after.ordinal,after.statusOrdinal,after.cwdHint)
    case AbsoluteStatusAction(path,follow,result) =>
      BenchWorld.IsAbsolutePath(path) &&
      StreamContract.GetFileStatusSpec(inputs.times,inputs.failures,
        before.statusOrdinal,after.statusOrdinal,inputs.fs,path,follow,
        result.Ok?,StreamContract.ResultValue(result,BenchWorld.DEFAULT_FILE_STATUS),
        StreamContract.ResultErrno(result)) &&
      after.position == before.position && after.capabilities == before.capabilities &&
      after.ordinal == before.ordinal && after.cwdHint == before.cwdHint
  }

  ghost predicate RuntimeTraceFields(inputs: RuntimeInputs, before: RuntimeState,
    after: RuntimeState, calls: seq<RuntimeObservation>)
  {
    (forall i: nat | i < |calls| :: RuntimeObservationFields(inputs,calls[i])) &&
    if |calls| == 0 then before == after
    else calls[0].before == before && calls[|calls|-1].after == after &&
      (forall i: nat | i+1 < |calls| :: calls[i].after == calls[i+1].before)
  }

  ghost predicate DirectoryActionFields(observation: RuntimeObservation,
    operation: BenchWorld.DirectoryOperation, handle: int, fd: int, name: string)
  {
    observation.action.DirectoryAction? &&
    observation.action.request.operation == operation &&
    observation.action.request.handle == handle && observation.action.request.fd == fd &&
    observation.action.request.name == name
  }

  ghost predicate EntryCallBindings(child: BenchWorld.FileStatus, parent: BenchWorld.FileStatus,
    handle: int, observation: EntryObservation, calls: seq<RuntimeObservation>)
  {
    EntryObservationFields(child,parent,observation) &&
    |calls| == 1 + |observation.entryStatus| &&
    DirectoryActionFields(calls[0],BenchWorld.DirectoryReadNext,handle,0,"") &&
    observation.read == StreamContract.DirectoryReadResultFields(calls[0].action.response) &&
    (|observation.entryStatus| == 1 ==>
      observation.read.Ok? && observation.read.v.DirectoryItem? &&
      DirectoryActionFields(calls[1],BenchWorld.DirectoryEntryLstat,0,0,observation.read.v.name) &&
      observation.entryStatus[0] == StreamContract.DirectoryStatusResultFields(calls[1].action.response))
  }

  datatype SearchWitness = SearchWitness(
    ghost entries: seq<EntryObservation>, ghost calls: seq<RuntimeObservation>,
    ghost boundaries: seq<nat>)

  ghost predicate EntryPartitionAt(child: BenchWorld.FileStatus,
    parent: BenchWorld.FileStatus, handle: int, evidence: SearchWitness, i: nat)
  {
    i < |evidence.entries| && i+1 < |evidence.boundaries| &&
    evidence.boundaries[i] <= evidence.boundaries[i+1] <= |evidence.calls| &&
    EntryCallBindings(child,parent,handle,evidence.entries[i],
      evidence.calls[evidence.boundaries[i]..evidence.boundaries[i+1]])
  }

  ghost predicate EntryWitnessFields(inputs: RuntimeInputs, before: RuntimeState,
    after: RuntimeState, child: BenchWorld.FileStatus, parent: BenchWorld.FileStatus,
    handle: int, evidence: SearchWitness)
  {
    RuntimeTraceFields(inputs,before,after,evidence.calls) &&
    |evidence.boundaries| == |evidence.entries| + 1 &&
    evidence.boundaries[0] == 0 &&
    evidence.boundaries[|evidence.boundaries|-1] == |evidence.calls| &&
    (forall i: nat | i < |evidence.entries| ::
      EntryPartitionAt(child,parent,handle,evidence,i))
  }

  ghost predicate SearchWitnessFields(inputs: RuntimeInputs, before: RuntimeState,
    after: RuntimeState, child: BenchWorld.FileStatus, parent: BenchWorld.FileStatus,
    handle: int, name: string, readErr: int, evidence: SearchWitness)
  {
    EntryWitnessFields(inputs,before,after,child,parent,handle,evidence) &&
    EntrySearchFields(child,parent,evidence.entries,name,readErr)
  }

}
