include "PwdTextCore.dfy"
include "PwdWorldPathCore.dfy"
include "../../core/IO.dfy"
include "PwdRecoverySpec.dfy"
include "PwdRecoveryIOProof.dfy"
include "PwdRecoveryTraceProof.dfy"
include "PwdRuntimeModel.dfy"
include "PwdRecoveryParentSpec.dfy"
include "PwdProof.dfy"
include "PwdEmissionCore.dfy"

module PwdRecoveryCore {
  import WorldPath = PwdWorldPathCore
  import BenchIO
  import BenchWorld
  import IOContract
  import C = IOContract
  import Errno = Errnos
  import Utf8 = PwdUtf8Core
  import Text = PwdTextCore
  import Spec = PwdRecoverySpec
  import NativeProof = PwdRecoveryIOProof
  import Trace = PwdRecoveryTraceProof
  import Model = PwdRuntimeModel
  import ParentSpec = PwdRecoveryParentSpec
  import PhysicalSpec = PwdPhysicalSpec
  import PhysicalProof = PwdProof
  import Emission = PwdEmissionSpec
  import Emit = PwdEmissionCore

  function ContainsUnsafeComponent(segs: seq<string>, i: nat): bool
    requires i <= |segs|
    decreases |segs| - i
  {
    if i >= |segs| then
      false
    else if segs[i] == "." || segs[i] == ".." then
      true
    else
      ContainsUnsafeComponent(segs, i + 1)
  } by method
  {
    if i >= |segs| {
      return false;
    } else if segs[i] == "." || segs[i] == ".." {
      return true;
    } else {
      return ContainsUnsafeComponent(segs, i + 1);
    }
  }

  function ParentArgument(height: nat): string
    requires height >= 1
    decreases height
  {
    if height == 1 then ".." else ParentArgument(height - 1) + "/.."
  } by method
  {
    if height == 1 {
      return "..";
    }
    var prefix := ParentArgument(height - 1);
    return prefix + "/..";
  }

  lemma ParentArgumentMatchesText(height: nat)
    requires height >= 1
    ensures ParentArgument(height) == Spec.ParentArgumentText(height)
    decreases height
  {
    if height == 1 {
      assert Spec.ParentArgumentText(height) == "..";
    } else {
      ParentArgumentMatchesText(height - 1);
      var prefix := Spec.ParentArgumentText(height - 1);
      var extended := prefix + "/..";
      assert |extended| == 3 * height - 1;
      forall i: nat | i < |extended|
        ensures extended[i] == Spec.ParentArgumentText(height)[i]
      {
        if i < |prefix| {
          assert extended[i] == prefix[i];
        } else {
          assert i - |prefix| < 3;
          if i == |prefix| {
            assert i % 3 == 2;
          } else if i == |prefix| + 1 {
            assert i % 3 == 0;
          } else {
            assert i == |prefix| + 2 && i % 3 == 1;
          }
        }
      }
      assert extended == Spec.ParentArgumentText(height);
    }
  }

  method FormatRecoveryFailure(failure: Spec.RecoveryFailure, io: BenchIO.IO)
    returns (diagnostic: BenchWorld.Bytes)
    requires Spec.ValidRecoveryFailure(failure)
    ensures diagnostic == Spec.RecoveryDiagnosticSpec(failure)
  {
    var quoted: BenchWorld.Bytes := [];
    if failure.RootAttributesFailed? {
      quoted := io.QuoteafPath("/");
    } else if failure.CurrentDirectoryStatusFailed? {
      quoted := io.QuoteafPath(".");
    } else if !failure.MemoryExhausted? {
      var argument := ParentArgument(failure.height);
      ParentArgumentMatchesText(failure.height);
      quoted := io.QuoteArgument(Utf8.Encode(argument));
    }
    var reason := "";
    var err := Spec.RecoveryFailureErr(failure);
    if err != 0 {
      reason := io.GetCLocaleErrnoText(err);
    }
    diagnostic := Text.RecoveryFailureText(failure, quoted, reason);
  }

  function LogicalTextValid(pwd: string): bool
  {
    BenchWorld.IsAbsolutePath(pwd) &&
    !ContainsUnsafeComponent(BenchWorld.SplitSegments(BenchWorld.StripLeadingSlash(pwd), 0, 0), 0)
  } by method
  {
    if !BenchWorld.IsAbsolutePath(pwd) {
      return false;
    }
    var components := WorldPath.SplitSegments(WorldPath.StripLeadingSlash(pwd), 0, 0);
    var unsafe := ContainsUnsafeComponent(components, 0);
    return !unsafe;
  }

  ghost predicate LogicalSelectionSummary(pwd: string,
                                          observations: seq<BenchWorld.IOResult<BenchWorld.FileStatus>>, selected: bool)
  {
    if !LogicalTextValid(pwd) then |observations| == 0 && !selected
    else
      |observations| >= 1 &&
      if observations[0].Err? then |observations| == 1 && !selected
      else
        |observations| == 2 &&
        (selected <==> observations[1].Ok? &&
                       observations[0].v.hostKey == observations[1].v.hostKey)
  }

  method ChooseLogicalFromStatuses(pwd: string,
                                   observations: seq<BenchWorld.IOResult<BenchWorld.FileStatus>>) returns (selected: bool)
    requires if !LogicalTextValid(pwd) then |observations| == 0
             else |observations| >= 1 &&
                  (if observations[0].Err? then |observations| == 1 else |observations| == 2)
    ensures LogicalSelectionSummary(pwd, observations, selected)
  {
    var valid := LogicalTextValid(pwd);
    if !valid {
      return false;
    }
    if observations[0].Err? {
      return false;
    }
    if observations[1].Err? {
      return false;
    }
    return observations[0].v.hostKey == observations[1].v.hostKey;
  }

  method ChooseEntryMatch(child: BenchWorld.FileStatus, parent: BenchWorld.FileStatus,
                          observation: Spec.EntryObservation) returns (matched: bool)
    requires Spec.EntryObservationFields(child, parent, observation)
    ensures matched <==> Spec.EntryMatchFields(child, parent, observation)
  {
    if observation.read.Err? || observation.read.v.DirectoryEnd? {
      return false;
    }
    var entry := observation.read.v;
    var crossDevice := parent.hostKey.device != child.hostKey.device;
    if entry.inode == 0 || crossDevice {
      var status := observation.entryStatus[0];
      if status.Err? {
        return false;
      }
      if status.v.hostKey.inode != child.hostKey.inode {
        return false;
      }
      return !crossDevice || status.v.hostKey.device == child.hostKey.device;
    }
    return entry.inode == child.hostKey.inode;
  }

  method ChooseParentCompletion(height: nat, readErr: int, closeErr: int, found: bool)
    returns (failure: seq<Spec.RecoveryFailure>)
    requires height >= 1 && readErr >= 0 && closeErr >= 0
    ensures Spec.ParentCompletionFields(height, readErr, closeErr, found, failure)
    ensures |failure| <= 1
    ensures |failure| == 1 ==> Spec.ValidRecoveryFailure(failure[0])
  {
    if readErr != 0 {
      return [Spec.ParentReadFailed(height, readErr)];
    }
    if closeErr != 0 {
      return [Spec.ParentReadFailed(height, closeErr)];
    }
    if !found {
      return [Spec.ParentEntryMissing(height)];
    }
    return [];
  }


  method ChoosePhysicalStart(result: BenchWorld.IOResult<string>) returns (choice: Spec.PhysicalStart)
    requires result.Err? ==> IOContract.ResultErrno(result) > 0
    ensures Spec.PhysicalStartFields(result, choice)
  {
    if result.Ok? {
      return Spec.ReturnedDirectory(result.v);
    }
    var err := IOContract.ResultErrno(result);
    if err == Errno.ENOMEM {
      return Spec.FatalAllocation;
    }
    return Spec.RecoverDirectory;
  }


  method ChooseParentAccess(descriptor: BenchWorld.IOResult<int>) returns (choice: Spec.ParentAccess)
    requires if descriptor.Ok? then descriptor.v >= 0 else IOContract.ResultErrno(descriptor) > 0
    ensures Spec.ParentAccessFields(descriptor, choice)
  {
    if descriptor.Ok? {
      return Spec.UseDirectoryDescriptor(descriptor.v);
    }
    return Spec.UseRelativeParent;
  }

  method ReadEntryObservation(child: BenchWorld.FileStatus, parent: BenchWorld.FileStatus,
                              handle: int, io: BenchIO.IO)
    returns (observation: Spec.EntryObservation, ghost calls: seq<Spec.RuntimeObservation>)
    requires handle in io.directoryCapabilities()
    requires io.directoryCapabilities()[handle].anchorFs == io.fs()
    requires !io.directoryCapabilities()[handle].includeDots
    requires C.DirectoryCapabilityReadCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle])
    modifies io.directoryStateRegion, io.statusObservationsRegion
    ensures Model.Inputs(io) == old(Model.Inputs(io))
    ensures Spec.RuntimeTraceFields(old(Model.Inputs(io)),old(Model.State(io)),Model.State(io),calls)
    ensures Spec.EntryCallBindings(child,parent,handle,observation,calls)
    ensures handle in io.directoryCapabilities()
    ensures io.directoryCapabilities()[handle].anchorFs == io.fs()
    ensures !io.directoryCapabilities()[handle].includeDots
    ensures C.DirectoryCapabilityReadCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle])
  {
    hide *;
    reveal C.DirectoryReadResultFields(), C.DirectoryStatusResultFields();
    ghost var inputs := Model.Inputs(io);
    ghost var before := Model.State(io);
    Model.InputsMatchModel(io);
    ghost var readRequest := BenchWorld.DirectoryRequest(BenchWorld.DirectoryReadNext,
                                                         before.ordinal,inputs.fs,inputs.topology,before.position,before.capabilities,
                                                         handle,0,"",before.statusOrdinal,before.cwdHint,inputs.occupiedLegacyHandles);
    assert C.DirectoryOperationCapabilitiesCurrentFields(io.directoryTopology(),
                                                         io.directoryCapabilities(),BenchWorld.DirectoryReadNext,handle,0) by {
      reveal C.DirectoryOperationCapabilitiesCurrentFields();
    }
    var read := io.ReadDirectoryCapability(handle);
    Model.InputsMatchModel(io);
    assert Model.Inputs(io) == inputs;
    ghost var middle := Model.State(io);
    ghost var readResponse := inputs.observations(readRequest);
    assert C.DirectoryResponseFields(readRequest,readResponse) by {
      hide *;
      reveal C.DirectoryOperationSpec();
    }
    NativeProof.ResponseErrnos(readRequest,readResponse);
    NativeProof.OperationCapabilities(readRequest,inputs.observations,readResponse,
                                      middle.position,middle.capabilities,middle.ordinal,middle.statusOrdinal,middle.cwdHint);
    NativeProof.ReadName(readRequest,readResponse);
    ghost var readCall := Spec.RuntimeObservation(before,middle,
                                                  Spec.DirectoryAction(readRequest,readResponse));
    assert Spec.RuntimeObservationFields(inputs,readCall) by {
      reveal Spec.RuntimeObservationFields();
    }
    Trace.SingleObservation(inputs,readCall);
    calls := [readCall];
    var statuses: seq<BenchWorld.IOResult<BenchWorld.FileStatus>> := [];
    if read.Ok? && read.v.DirectoryItem? &&
       (read.v.inode == 0 || parent.hostKey.device != child.hostKey.device) {
      ghost var entryRequest := BenchWorld.DirectoryRequest(BenchWorld.DirectoryEntryLstat,
                                                            middle.ordinal,inputs.fs,inputs.topology,middle.position,middle.capabilities,
                                                            0,0,read.v.name,middle.statusOrdinal,middle.cwdHint,inputs.occupiedLegacyHandles);
      var status := io.LstatCwdEntry(read.v.name);
      Model.InputsMatchModel(io);
      assert Model.Inputs(io) == inputs;
      ghost var after := Model.State(io);
      ghost var entryResponse := inputs.observations(entryRequest);
      assert C.DirectoryResponseFields(entryRequest,entryResponse) by {
        hide *;
        reveal C.DirectoryOperationSpec();
      }
      NativeProof.ResponseErrnos(entryRequest,entryResponse);
      NativeProof.OperationCapabilities(entryRequest,inputs.observations,entryResponse,
                                        after.position,after.capabilities,after.ordinal,after.statusOrdinal,after.cwdHint);
      ghost var entryCall := Spec.RuntimeObservation(middle,after,
                                                     Spec.DirectoryAction(entryRequest,entryResponse));
      assert Spec.RuntimeObservationFields(inputs,entryCall) by {
        reveal Spec.RuntimeObservationFields();
      }
      Trace.SingleObservation(inputs,entryCall);
      Trace.ConcatTraces(inputs,before,middle,after,calls,[entryCall]);
      calls := calls+[entryCall];
      statuses := [status];
    }
    observation := Spec.EntryObservation(read,statuses);
    assert Spec.EntryCallBindings(child,parent,handle,observation,calls) by {
      reveal Spec.EntryCallBindings(), Spec.EntryObservationFields();
      reveal Spec.EntryNeedsStatusFields(), Spec.EntryNameFields(), Spec.DirectoryActionFields();
    }
  }

  method FindParentName(child: BenchWorld.FileStatus, parent: BenchWorld.FileStatus,
                        handle: int, io: BenchIO.IO)
    returns (name: string, readErr: int, ghost evidence: Spec.SearchWitness)
    requires handle in io.directoryCapabilities()
    requires io.directoryCapabilities()[handle].anchorFs == io.fs()
    requires !io.directoryCapabilities()[handle].includeDots
    requires C.DirectoryCapabilityReadCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle])
    modifies io.directoryStateRegion, io.statusObservationsRegion
    ensures name == "" || BenchWorld.InodeChildNameValid(name)
    ensures readErr >= 0
    ensures Model.Inputs(io) == old(Model.Inputs(io))
    ensures Spec.SearchWitnessFields(old(Model.Inputs(io)),old(Model.State(io)),
                                     Model.State(io),child,parent,handle,name,readErr,evidence)
    ensures handle in io.directoryCapabilities()
    ensures io.directoryCapabilities()[handle].anchorFs == io.fs()
    ensures !io.directoryCapabilities()[handle].includeDots
    ensures C.DirectoryCapabilityReadCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle])
    decreases *
  {
    hide *;
    reveal Spec.EntryObservationFields(), Spec.EntryNameFields();
    ghost var inputs := Model.Inputs(io);
    ghost var before := Model.State(io);
    evidence := Spec.SearchWitness([],[],[0]);
    assert Spec.EntryWitnessFields(inputs,before,before,child,parent,handle,evidence) by {
      reveal Spec.EntryWitnessFields(), Spec.RuntimeTraceFields();
    }
    name := "";
    readErr := 0;
    while true
      invariant name == "" && readErr == 0
      invariant handle in io.directoryCapabilities()
      invariant io.directoryCapabilities()[handle].anchorFs == io.fs()
      invariant !io.directoryCapabilities()[handle].includeDots
      invariant C.DirectoryCapabilityReadCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle])
      invariant Model.Inputs(io) == inputs
      invariant Spec.EntryWitnessFields(inputs,before,Model.State(io),child,parent,handle,evidence)
      invariant forall i: nat | i < |evidence.entries| ::
                  evidence.entries[i].read.Ok? && evidence.entries[i].read.v.DirectoryItem? &&
                  !Spec.EntryMatchFields(child,parent,evidence.entries[i])
      decreases *
    {
      ghost var middle := Model.State(io);
      var entry, ghostCalls := ReadEntryObservation(child,parent,handle,io);
      assert Spec.EntryObservationFields(child,parent,entry) by {
        reveal Spec.EntryCallBindings();
      }
      Trace.AppendEntry(inputs,before,middle,Model.State(io),child,parent,handle,evidence,entry,ghostCalls);
      ghost var next := Spec.SearchWitness(evidence.entries+[entry],evidence.calls+ghostCalls,
                                           evidence.boundaries+[|evidence.calls+ghostCalls|]);
      assert forall i: nat | i+1 < |next.entries| ::
          next.entries[i].read.Ok? && next.entries[i].read.v.DirectoryItem? &&
          !Spec.EntryMatchFields(child,parent,next.entries[i]);
      if entry.read.Err? {
        readErr := C.ResultErrno(entry.read);
        Trace.FinishEntrySearch(inputs,before,Model.State(io),child,parent,handle,name,readErr,next);
        evidence := next;
        return;
      }
      if entry.read.v.DirectoryEnd? {
        Trace.FinishEntrySearch(inputs,before,Model.State(io),child,parent,handle,name,readErr,next);
        evidence := next;
        return;
      }
      var matched := ChooseEntryMatch(child,parent,entry);
      if matched {
        name := entry.read.v.name;
        Trace.FinishEntrySearch(inputs,before,Model.State(io),child,parent,handle,name,readErr,next);
        evidence := next;
        return;
      }
      evidence := next;
    }
  }

  method AccessParent(child: BenchWorld.FileStatus, height: nat, io: BenchIO.IO)
    returns (parent: BenchWorld.FileStatus, handle: int,
             failure: seq<Spec.RecoveryFailure>, ghost evidence: ParentSpec.AccessEvidence)
    requires height >= 1
    modifies io.directoryStateRegion, io.cwdRegion, io.statusObservationsRegion
    ensures Model.Inputs(io) == old(Model.Inputs(io))
    ensures ParentSpec.AccessOutcomeFields(old(Model.Inputs(io)),old(Model.State(io)),
                                           Model.State(io),height,parent,handle,failure,evidence)
    ensures |failure| <= 1
    ensures |failure| == 1 ==> Spec.ValidRecoveryFailure(failure[0])
    ensures |failure| == 0 ==> parent.kind == BenchWorld.DirectoryKind
    ensures |failure| == 0 ==> handle in io.directoryCapabilities() &&
                               io.directoryCapabilities()[handle].anchorFs == io.fs() &&
                               !io.directoryCapabilities()[handle].includeDots &&
                               C.DirectoryCapabilityReadCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle])
  {
    hide *;
    reveal Spec.ValidRecoveryFailure();
    reveal C.DirectoryHandleResultFields(), C.DirectoryDescriptorResultFields();
    reveal C.DirectoryUnitResultFields(), C.DirectoryStatusResultFields();
    parent := child;
    handle := 0;
    failure := [];
    ghost var inputs := Model.Inputs(io);
    ghost var before := Model.State(io);
    ghost var calls: seq<Spec.RuntimeObservation> := [];
    Model.InputsMatchModel(io);
    ghost var openParentBefore := Model.State(io);
    ghost var openParentRequest := BenchWorld.DirectoryRequest(BenchWorld.DirectoryOpenParent,
                                                               openParentBefore.ordinal,inputs.fs,inputs.topology,openParentBefore.position,
                                                               openParentBefore.capabilities,0,0,"",openParentBefore.statusOrdinal,openParentBefore.cwdHint,inputs.occupiedLegacyHandles);
    var openResult := io.OpenParentDirectory();
    Model.InputsMatchModel(io);
    assert Model.Inputs(io) == inputs;
    ghost var openParentAfter := Model.State(io);
    ghost var openParentResponse := inputs.observations(openParentRequest);
    assert C.DirectoryResponseFields(openParentRequest,openParentResponse) by {
      hide *;
      reveal C.DirectoryOperationSpec();
    }
    NativeProof.ResponseErrnos(openParentRequest,openParentResponse);
    NativeProof.OperationCapabilities(openParentRequest,inputs.observations,openParentResponse,
                                      openParentAfter.position,openParentAfter.capabilities,openParentAfter.ordinal,
                                      openParentAfter.statusOrdinal,openParentAfter.cwdHint);
    ghost var openParentCall := Spec.RuntimeObservation(openParentBefore,openParentAfter,
                                                        Spec.DirectoryAction(openParentRequest,openParentResponse));
    assert Spec.RuntimeObservationFields(inputs,openParentCall) by {
      reveal Spec.RuntimeObservationFields();
    }
    Trace.SingleObservation(inputs,openParentCall);
    calls := calls+[openParentCall];
    assert openParentBefore == before;
    assert calls == [openParentCall];
    assert Spec.RuntimeTraceFields(inputs,before,openParentAfter,calls);
    if openResult.Err? {
      failure := [Spec.ParentOpenFailed(height,C.ResultErrno(openResult))];
      evidence := ParentSpec.AccessEvidence(openResult,[],[],[],calls);
      assert C.ResultErrno(openResult) > 0;
      assert ParentSpec.AccessCallBindings(evidence) by {
        reveal ParentSpec.AccessCallBindings(), ParentSpec.HandleCallFields();
        reveal Spec.DirectoryActionFields();
      }
      assert ParentSpec.AccessOutcomeFields(inputs,before,Model.State(io),height,
                                            parent,handle,failure,evidence) by {
        reveal ParentSpec.AccessOutcomeFields(), ParentSpec.AccessCallBindings();
        reveal ParentSpec.HandleCallFields(), ParentSpec.DescriptorCallFields();
        reveal ParentSpec.UnitCallFields(), ParentSpec.StatusCallFields();
        reveal Spec.DirectoryActionFields(), Spec.ValidRecoveryFailure();
      }
      return;
    }
    handle := openResult.v;
    ghost var descriptorBefore := Model.State(io);
    ghost var descriptorRequest := BenchWorld.DirectoryRequest(BenchWorld.DirectoryGetDescriptor,
                                                               descriptorBefore.ordinal,inputs.fs,inputs.topology,descriptorBefore.position,
                                                               descriptorBefore.capabilities,handle,0,"",descriptorBefore.statusOrdinal,descriptorBefore.cwdHint,inputs.occupiedLegacyHandles);
    var descriptor := io.GetDirectoryDescriptor(handle);
    Model.InputsMatchModel(io);
    assert Model.Inputs(io) == inputs;
    ghost var descriptorAfter := Model.State(io);
    ghost var descriptorResponse := inputs.observations(descriptorRequest);
    assert C.DirectoryResponseFields(descriptorRequest,descriptorResponse) by {
      hide *;
      reveal C.DirectoryOperationSpec();
    }
    NativeProof.ResponseErrnos(descriptorRequest,descriptorResponse);
    NativeProof.OperationCapabilities(descriptorRequest,inputs.observations,descriptorResponse,
                                      descriptorAfter.position,descriptorAfter.capabilities,descriptorAfter.ordinal,
                                      descriptorAfter.statusOrdinal,descriptorAfter.cwdHint);
    ghost var descriptorCall := Spec.RuntimeObservation(descriptorBefore,descriptorAfter,
                                                        Spec.DirectoryAction(descriptorRequest,descriptorResponse));
    assert Spec.RuntimeObservationFields(inputs,descriptorCall) by {
      reveal Spec.RuntimeObservationFields();
    }
    Trace.SingleObservation(inputs,descriptorCall);
    Trace.ConcatTraces(inputs,before,descriptorBefore,descriptorAfter,calls,[descriptorCall]);
    calls := calls+[descriptorCall];
    ghost var movementBefore := Model.State(io);
    ghost var movementRequest := BenchWorld.DirectoryRequest(if descriptor.Ok? then BenchWorld.DirectoryFchdir else BenchWorld.DirectoryChdirParent,
                                                             movementBefore.ordinal,inputs.fs,inputs.topology,movementBefore.position,
                                                             movementBefore.capabilities,0,if descriptor.Ok? then descriptor.v else 0,"",movementBefore.statusOrdinal,movementBefore.cwdHint,inputs.occupiedLegacyHandles);
    var moved: BenchWorld.IOResult<BenchWorld.Unit>;
    if descriptor.Ok? {
      moved := io.FchdirDirectory(descriptor.v);
    } else {
      moved := io.ChdirParent();
    }
    Model.InputsMatchModel(io);
    assert Model.Inputs(io) == inputs;
    ghost var movementAfter := Model.State(io);
    ghost var movementResponse := inputs.observations(movementRequest);
    assert C.DirectoryResponseFields(movementRequest,movementResponse) by {
      hide *;
      reveal C.DirectoryOperationSpec();
    }
    NativeProof.ResponseErrnos(movementRequest,movementResponse);
    NativeProof.OperationCapabilities(movementRequest,inputs.observations,movementResponse,
                                      movementAfter.position,movementAfter.capabilities,movementAfter.ordinal,
                                      movementAfter.statusOrdinal,movementAfter.cwdHint);
    ghost var movementCall := Spec.RuntimeObservation(movementBefore,movementAfter,
                                                      Spec.DirectoryAction(movementRequest,movementResponse));
    assert Spec.RuntimeObservationFields(inputs,movementCall) by {
      reveal Spec.RuntimeObservationFields();
    }
    Trace.SingleObservation(inputs,movementCall);
    Trace.ConcatTraces(inputs,before,movementBefore,movementAfter,calls,[movementCall]);
    calls := calls+[movementCall];
    if moved.Err? {
      failure := [Spec.ParentChdirFailed(height,C.ResultErrno(moved))];
      evidence := ParentSpec.AccessEvidence(openResult,[descriptor],[moved],[],calls);
      assert ParentSpec.AccessOutcomeFields(inputs,before,Model.State(io),height,
                                            parent,handle,failure,evidence) by {
        reveal ParentSpec.AccessOutcomeFields(), ParentSpec.AccessCallBindings();
        reveal ParentSpec.HandleCallFields(), ParentSpec.DescriptorCallFields();
        reveal ParentSpec.UnitCallFields(), ParentSpec.StatusCallFields();
        reveal Spec.DirectoryActionFields(), Spec.ValidRecoveryFailure();
      }
      return;
    }
    ghost var parentStatusBefore := Model.State(io);
    ghost var parentStatusRequest := BenchWorld.DirectoryRequest(if descriptor.Ok? then BenchWorld.DirectoryFstat else BenchWorld.DirectoryCurrentStatus,
                                                                 parentStatusBefore.ordinal,inputs.fs,inputs.topology,parentStatusBefore.position,
                                                                 parentStatusBefore.capabilities,0,if descriptor.Ok? then descriptor.v else 0,"",parentStatusBefore.statusOrdinal,parentStatusBefore.cwdHint,inputs.occupiedLegacyHandles);
    var observed: BenchWorld.IOResult<BenchWorld.FileStatus>;
    if descriptor.Ok? {
      observed := io.FstatDirectory(descriptor.v);
    } else {
      observed := io.GetCwdDirectoryIdentity();
    }
    Model.InputsMatchModel(io);
    assert Model.Inputs(io) == inputs;
    ghost var parentStatusAfter := Model.State(io);
    ghost var parentStatusResponse := inputs.observations(parentStatusRequest);
    assert C.DirectoryResponseFields(parentStatusRequest,parentStatusResponse) by {
      hide *;
      reveal C.DirectoryOperationSpec();
    }
    NativeProof.ResponseErrnos(parentStatusRequest,parentStatusResponse);
    NativeProof.OperationCapabilities(parentStatusRequest,inputs.observations,parentStatusResponse,
                                      parentStatusAfter.position,parentStatusAfter.capabilities,parentStatusAfter.ordinal,
                                      parentStatusAfter.statusOrdinal,parentStatusAfter.cwdHint);
    ghost var parentStatusCall := Spec.RuntimeObservation(parentStatusBefore,parentStatusAfter,
                                                          Spec.DirectoryAction(parentStatusRequest,parentStatusResponse));
    assert Spec.RuntimeObservationFields(inputs,parentStatusCall) by {
      reveal Spec.RuntimeObservationFields();
    }
    Trace.SingleObservation(inputs,parentStatusCall);
    Trace.ConcatTraces(inputs,before,parentStatusBefore,parentStatusAfter,calls,[parentStatusCall]);
    calls := calls+[parentStatusCall];
    NativeProof.StatusKind(parentStatusRequest,parentStatusResponse);
    if observed.Err? {
      failure := [Spec.ParentStatusFailed(height,C.ResultErrno(observed))];
    } else {
      parent := observed.v;
    }
    evidence := ParentSpec.AccessEvidence(openResult,[descriptor],[moved],[observed],calls);
    assert ParentSpec.AccessOutcomeFields(inputs,before,Model.State(io),height,
                                          parent,handle,failure,evidence) by {
      reveal ParentSpec.AccessOutcomeFields(), ParentSpec.AccessCallBindings();
      reveal ParentSpec.HandleCallFields(), ParentSpec.DescriptorCallFields();
      reveal ParentSpec.UnitCallFields(), ParentSpec.StatusCallFields();
      reveal Spec.DirectoryActionFields(), Spec.ValidRecoveryFailure();
    }
  }

  method AscendAndFind(child: BenchWorld.FileStatus, height: nat, io: BenchIO.IO)
    returns (parent: BenchWorld.FileStatus, name: string, failure: seq<Spec.RecoveryFailure>,
             ghost evidence: ParentSpec.ParentEvidence)
    requires height >= 1
    modifies io.directoryStateRegion, io.cwdRegion, io.statusObservationsRegion
    ensures Model.Inputs(io) == old(Model.Inputs(io))
    ensures ParentSpec.ParentAttemptFields(old(Model.Inputs(io)),old(Model.State(io)),
                                           Model.State(io),child,height,parent,name,failure,evidence)
    ensures |failure| <= 1
    ensures |failure| == 1 ==> Spec.ValidRecoveryFailure(failure[0])
    ensures |failure| == 0 ==> BenchWorld.InodeChildNameValid(name)
    ensures |failure| == 0 ==> parent.kind == BenchWorld.DirectoryKind
    decreases *
  {
    hide *;
    reveal C.DirectoryUnitResultFields();
    ghost var inputs := Model.Inputs(io);
    ghost var before := Model.State(io);
    name := "";
    var handle: int;
    ghost var access: ParentSpec.AccessEvidence;
    parent,handle,failure,access := AccessParent(child,height,io);
    if |failure| != 0 {
      evidence := ParentSpec.ParentEvidence(access,[],[],access.calls);
      assert ParentSpec.ParentAttemptFields(inputs,before,Model.State(io),child,height,
                                            parent,name,failure,evidence) by {
        reveal ParentSpec.ParentAttemptFields(), ParentSpec.AccessOutcomeFields();
        reveal ParentSpec.AccessCallBindings();
      }
      return;
    }
    ghost var searchBefore := Model.State(io);
    var readErr: int;
    ghost var search: Spec.SearchWitness;
    name,readErr,search := FindParentName(child,parent,handle,io);
    ghost var calls := access.calls+search.calls;
    assert Spec.RuntimeTraceFields(inputs,searchBefore,Model.State(io),search.calls) by {
      reveal Spec.SearchWitnessFields(), Spec.EntryWitnessFields();
    }
    assert Spec.RuntimeTraceFields(inputs,before,searchBefore,access.calls) by {
      reveal ParentSpec.AccessOutcomeFields();
    }
    Trace.ConcatTraces(inputs,before,searchBefore,Model.State(io),access.calls,search.calls);
    Model.InputsMatchModel(io);
    ghost var closeParentBefore := Model.State(io);
    ghost var closeParentRequest := BenchWorld.DirectoryRequest(BenchWorld.DirectoryClose,
                                                                closeParentBefore.ordinal,inputs.fs,inputs.topology,closeParentBefore.position,
                                                                closeParentBefore.capabilities,handle,0,"",closeParentBefore.statusOrdinal,closeParentBefore.cwdHint,inputs.occupiedLegacyHandles);
    var closed := io.CloseDirectoryCapability(handle);
    Model.InputsMatchModel(io);
    assert Model.Inputs(io) == inputs;
    ghost var closeParentAfter := Model.State(io);
    ghost var closeParentResponse := inputs.observations(closeParentRequest);
    assert C.DirectoryResponseFields(closeParentRequest,closeParentResponse) by {
      hide *;
      reveal C.DirectoryOperationSpec();
    }
    NativeProof.ResponseErrnos(closeParentRequest,closeParentResponse);
    NativeProof.OperationCapabilities(closeParentRequest,inputs.observations,closeParentResponse,
                                      closeParentAfter.position,closeParentAfter.capabilities,closeParentAfter.ordinal,
                                      closeParentAfter.statusOrdinal,closeParentAfter.cwdHint);
    ghost var closeParentCall := Spec.RuntimeObservation(closeParentBefore,closeParentAfter,
                                                         Spec.DirectoryAction(closeParentRequest,closeParentResponse));
    assert Spec.RuntimeObservationFields(inputs,closeParentCall) by {
      reveal Spec.RuntimeObservationFields();
    }
    Trace.SingleObservation(inputs,closeParentCall);
    Trace.ConcatTraces(inputs,before,closeParentBefore,closeParentAfter,calls,[closeParentCall]);
    calls := calls+[closeParentCall];
    failure := ChooseParentCompletion(height,readErr,C.ResultErrno(closed),name != "");
    evidence := ParentSpec.ParentEvidence(access,[search],[closed],calls);
    assert ParentSpec.ParentAttemptFields(inputs,before,Model.State(io),child,height,
                                          parent,name,failure,evidence) by {
      reveal ParentSpec.ParentAttemptFields(), ParentSpec.UnitCallFields();
      reveal ParentSpec.AccessOutcomeFields(), ParentSpec.AccessCallBindings();
      reveal Spec.RuntimeTraceFields(), Spec.DirectoryActionFields();
      assert access.calls[|access.calls|-1].after == searchBefore;
    }
  }

  method PhysicalDirectory(io: BenchIO.IO) returns (outcome: Spec.DirectoryOutcome)
    modifies io.directoryStateRegion, io.cwdRegion, io.statusObservationsRegion
    ensures Model.Inputs(io) == old(Model.Inputs(io))
    ensures Spec.DirectoryOutcomeFields(outcome)
    ensures exists evidence: PhysicalSpec.PhysicalEvidence ::
              PhysicalSpec.PhysicalSelectionFields(old(Model.Inputs(io)),old(Model.State(io)),Model.State(io),outcome,evidence)
    decreases *
  {
    hide *;
    reveal C.DirectoryPathResultFields(), C.DirectoryStatusResultFields();
    reveal Spec.ValidRecoveryFailure(), Spec.DirectoryOutcomeFields(), BenchWorld.IsAbsolutePath();
    ghost var inputs := Model.Inputs(io);
    ghost var before := Model.State(io);
    ghost var calls: seq<Spec.RuntimeObservation> := [];
    Model.InputsMatchModel(io);
    ghost var directBefore := Model.State(io);
    ghost var directRequest := BenchWorld.DirectoryRequest(BenchWorld.DirectoryGetCwd,
                                                           directBefore.ordinal,inputs.fs,inputs.topology,directBefore.position,
                                                           directBefore.capabilities,0,0,"",directBefore.statusOrdinal,directBefore.cwdHint,inputs.occupiedLegacyHandles);
    var direct := io.GetCwd();
    Model.InputsMatchModel(io);
    assert Model.Inputs(io) == inputs;
    ghost var directAfter := Model.State(io);
    ghost var directResponse := inputs.observations(directRequest);
    assert C.DirectoryResponseFields(directRequest,directResponse) by {
      hide *;
      reveal C.DirectoryOperationSpec();
    }
    NativeProof.ResponseErrnos(directRequest,directResponse);
    ghost var directCall := Spec.RuntimeObservation(directBefore,directAfter,
                                                    Spec.DirectoryAction(directRequest,directResponse));
    assert Spec.RuntimeObservationFields(inputs,directCall) by {
      reveal Spec.RuntimeObservationFields();
    }
    Trace.SingleObservation(inputs,directCall);
    calls := calls+[directCall];
    assert directBefore == before;
    assert calls == [directCall];
    assert Spec.RuntimeTraceFields(inputs,before,directAfter,calls);
    NativeProof.PathIsAbsolute(directRequest,directResponse);
    if direct.Ok? {
      outcome := Spec.DirectoryRecovered(direct.v);
      ghost var selectedEvidence := PhysicalSpec.PhysicalEvidence(direct,[],[],[],calls,[0],[0]);
      assert PhysicalSpec.PhysicalSelectionFields(inputs,before,Model.State(io),outcome,selectedEvidence) by {
        reveal PhysicalSpec.PhysicalSelectionFields(), Spec.DirectoryOutcomeFields();
        reveal Spec.DirectoryActionFields(), Spec.ValidRecoveryFailure();
      }
      PhysicalProof.SelectionWitness(inputs,before,Model.State(io),outcome,selectedEvidence);
      return;
    }
    if C.ResultErrno(direct) == Errno.ENOMEM {
      outcome := Spec.DirectoryFailed(Spec.MemoryExhausted);
      ghost var selectedEvidence := PhysicalSpec.PhysicalEvidence(direct,[],[],[],calls,[0],[0]);
      assert PhysicalSpec.PhysicalSelectionFields(inputs,before,Model.State(io),outcome,selectedEvidence) by {
        reveal PhysicalSpec.PhysicalSelectionFields(), Spec.DirectoryOutcomeFields();
        reveal Spec.DirectoryActionFields(), Spec.ValidRecoveryFailure();
      }
      PhysicalProof.SelectionWitness(inputs,before,Model.State(io),outcome,selectedEvidence);
      return;
    }
    ghost var rootBefore := Model.State(io);
    var root := io.GetFileStatus("/",false);
    ghost var rootAfter := Model.State(io);
    NativeProof.RootStatusKind(inputs.times,inputs.failures,rootBefore.statusOrdinal,
                               rootAfter.statusOrdinal,inputs.fs,root);
    ghost var rootCall := Spec.RuntimeObservation(rootBefore,rootAfter,
                                                  Spec.AbsoluteStatusAction("/",false,root));
    assert Spec.RuntimeObservationFields(inputs,rootCall) by {
      reveal Spec.RuntimeObservationFields(), BenchWorld.IsAbsolutePath();
    }
    Trace.SingleObservation(inputs,rootCall);
    Trace.ConcatTraces(inputs,before,rootBefore,rootAfter,calls,[rootCall]);
    calls := calls+[rootCall];
    if root.Err? {
      outcome := Spec.DirectoryFailed(Spec.RootAttributesFailed(C.ResultErrno(root)));
      ghost var selectedEvidence := PhysicalSpec.PhysicalEvidence(direct,[root],[],[],calls,[0],[0]);
      assert PhysicalSpec.PhysicalSelectionFields(inputs,before,Model.State(io),outcome,selectedEvidence) by {
        reveal PhysicalSpec.PhysicalSelectionFields(), Spec.DirectoryOutcomeFields();
        reveal Spec.DirectoryActionFields(), Spec.ValidRecoveryFailure();
      }
      PhysicalProof.SelectionWitness(inputs,before,Model.State(io),outcome,selectedEvidence);
      return;
    }
    ghost var currentBefore := Model.State(io);
    ghost var currentRequest := BenchWorld.DirectoryRequest(BenchWorld.DirectoryCurrentStatus,
                                                            currentBefore.ordinal,inputs.fs,inputs.topology,currentBefore.position,
                                                            currentBefore.capabilities,0,0,"",currentBefore.statusOrdinal,currentBefore.cwdHint,inputs.occupiedLegacyHandles);
    var current := io.GetCwdDirectoryIdentity();
    Model.InputsMatchModel(io);
    assert Model.Inputs(io) == inputs;
    ghost var currentAfter := Model.State(io);
    ghost var currentResponse := inputs.observations(currentRequest);
    assert C.DirectoryResponseFields(currentRequest,currentResponse) by {
      hide *;
      reveal C.DirectoryOperationSpec();
    }
    NativeProof.ResponseErrnos(currentRequest,currentResponse);
    ghost var currentCall := Spec.RuntimeObservation(currentBefore,currentAfter,
                                                     Spec.DirectoryAction(currentRequest,currentResponse));
    assert Spec.RuntimeObservationFields(inputs,currentCall) by {
      reveal Spec.RuntimeObservationFields();
    }
    Trace.SingleObservation(inputs,currentCall);
    Trace.ConcatTraces(inputs,before,currentBefore,currentAfter,calls,[currentCall]);
    calls := calls+[currentCall];
    NativeProof.StatusKind(currentRequest,currentResponse);
    if current.Err? {
      outcome := Spec.DirectoryFailed(Spec.CurrentDirectoryStatusFailed(C.ResultErrno(current)));
      ghost var selectedEvidence := PhysicalSpec.PhysicalEvidence(direct,[root],[current],[],calls,[0],[0]);
      assert PhysicalSpec.PhysicalSelectionFields(inputs,before,Model.State(io),outcome,selectedEvidence) by {
        reveal PhysicalSpec.PhysicalSelectionFields(), Spec.DirectoryOutcomeFields();
        reveal Spec.DirectoryActionFields(), Spec.ValidRecoveryFailure();
      }
      PhysicalProof.SelectionWitness(inputs,before,Model.State(io),outcome,selectedEvidence);
      return;
    }
    ghost var initialCalls := calls;
    assert initialCalls == [directCall,rootCall,currentCall];
    ghost var stepsBefore := Model.State(io);
    ghost var steps: seq<PhysicalSpec.ParentStep> := [];
    ghost var stepCalls: seq<Spec.RuntimeObservation> := [];
    ghost var boundaries: seq<nat> := [0];
    ghost var names: seq<string> := [];
    ghost var textBoundaries: seq<nat> := [0];
    PhysicalProof.EmptySteps(inputs,stepsBefore,root.v,current.v);
    var child := current.v;
    var directory := "";
    var height: nat := 1;
    assert PhysicalSpec.PathPartitionFields(names,directory,textBoundaries) by {
      reveal PhysicalSpec.PathPartitionFields();
    }
    assert initialCalls+stepCalls == calls;
    assert Spec.RuntimeTraceFields(inputs,before,Model.State(io),calls);
    assert Spec.RuntimeTraceFields(inputs,before,Model.State(io),initialCalls+stepCalls);
    while child.hostKey != root.v.hostKey
      invariant Model.Inputs(io) == inputs
      invariant height == |steps|+1
      invariant child == (if |steps| == 0 then current.v else steps[|steps|-1].parent)
      invariant forall i: nat | i < |steps| :: |steps[i].failure| == 0
      invariant names == seq(|steps|,i=>if 0 <= i < |steps| then steps[i].name else "")
      invariant (|steps| == 0 <==> directory == "")
      invariant directory == "" || BenchWorld.IsAbsolutePath(directory)
      invariant PhysicalSpec.PathPartitionFields(names,directory,textBoundaries)
      invariant PhysicalSpec.StepsWitnessFields(inputs,stepsBefore,Model.State(io),
                                                root.v,current.v,steps,stepCalls,boundaries)
      invariant Spec.RuntimeTraceFields(inputs,before,Model.State(io),initialCalls+stepCalls)
      decreases *
    {
      ghost var middle := Model.State(io);
      var parent,name,failure,parentEvidence := AscendAndFind(child,height,io);
      ghost var after := Model.State(io);
      ghost var step := PhysicalSpec.ParentStep(parent,name,failure,parentEvidence);
      PhysicalProof.AppendStep(inputs,stepsBefore,middle,after,root.v,current.v,
                               steps,stepCalls,boundaries,step);
      assert Spec.RuntimeTraceFields(inputs,middle,after,parentEvidence.calls) by {
        reveal ParentSpec.ParentAttemptFields();
      }
      Trace.ConcatTraces(inputs,before,middle,after,initialCalls+stepCalls,parentEvidence.calls);
      ghost var combinedCalls := (initialCalls+stepCalls)+parentEvidence.calls;
      steps := steps+[step];
      stepCalls := stepCalls+parentEvidence.calls;
      assert initialCalls+stepCalls == combinedCalls;
      assert Spec.RuntimeTraceFields(inputs,before,Model.State(io),initialCalls+stepCalls);
      boundaries := boundaries+[|stepCalls|];
      if |failure| != 0 {
        outcome := Spec.DirectoryFailed(failure[0]);
        ghost var selectedEvidence := PhysicalSpec.PhysicalEvidence(direct,[root],[current],steps,initialCalls+stepCalls,boundaries,textBoundaries);
        assert PhysicalSpec.PhysicalSelectionFields(inputs,before,Model.State(io),outcome,selectedEvidence) by {
          reveal PhysicalSpec.PhysicalSelectionFields(), Spec.DirectoryOutcomeFields();
          reveal Spec.DirectoryActionFields(), Spec.ValidRecoveryFailure();
        }
        PhysicalProof.SelectionWitness(inputs,before,Model.State(io),outcome,selectedEvidence);
        return;
      }
      PhysicalProof.PathPartitionSnoc(names,directory,textBoundaries,name);
      ghost var prefixLength := |"/"+name|;
      textBoundaries := [0]+seq(|textBoundaries|,
      i=>if 0 <= i < |textBoundaries| then prefixLength+textBoundaries[i] else 0);
      names := names+[name];
      directory := "/"+name+directory;
      PhysicalProof.PartitionIsAbsolute(names,directory,textBoundaries);
      child := parent;
      height := height+1;
    }
    outcome := Spec.DirectoryRecovered(if directory == "" then "/" else directory);
    ghost var selectedEvidence := PhysicalSpec.PhysicalEvidence(direct,[root],[current],steps,initialCalls+stepCalls,boundaries,textBoundaries);
    assert PhysicalSpec.PhysicalSelectionFields(inputs,before,Model.State(io),outcome,selectedEvidence) by {
      reveal PhysicalSpec.PhysicalSelectionFields(), Spec.DirectoryOutcomeFields();
      reveal Spec.DirectoryActionFields(), Spec.ValidRecoveryFailure();
    }
    PhysicalProof.SelectionWitness(inputs,before,Model.State(io),outcome,selectedEvidence);
  }

  method FlushPhysical(outcome: Spec.DirectoryOutcome, io: BenchIO.IO) returns (exit: int)
    requires Spec.DirectoryOutcomeFields(outcome)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Emission.PhysicalEmissionFields(outcome,old(io.stdout()),old(io.stderr()),
                                            io.stdout(),io.stderr(),io.trustedStreams(),exit)
  {
    var output: BenchWorld.Bytes := [];
    var diagnostics: BenchWorld.Bytes := [];
    var normalExit := 0;
    if outcome.DirectoryRecovered? {
      output := Text.CurrentDirectoryTextSpec(outcome.directory);
    } else {
      diagnostics := FormatRecoveryFailure(outcome.failure,io);
      normalExit := 1;
    }
    exit := Emit.Flush(output,diagnostics,normalExit,io);
  }

}
