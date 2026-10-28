include "../Spec/LsNativeSpec.dfy"

module LsNativeCore {
  import BenchIO
  import W = BenchWorld
  import C = IOContract
  import Spec = LsNativeSpec

  ghost function Inputs(io: BenchIO.IO): (inputs: Spec.Inputs)
    reads io.fsRegion,io.trustedNativeFailuresRegion,io.directoryStateRegion
    ensures inputs.fs == io.fs()
    ensures inputs.times == io.statusObservations()
    ensures inputs.failures == io.trustedNativeFailures()
    ensures inputs.directories == io.directoryObservations()
  {
    Spec.Inputs(io.fs(),io.statusObservations(),io.trustedNativeFailures(),io.directoryObservations())
  }

  ghost function State(io: BenchIO.IO): (state: Spec.State)
    reads io.fsRegion,io.directoryStateRegion,io.cwdRegion,io.statusObservationsRegion
    ensures state.context == io.cwdContext()
    ensures state.status == io.statusCursor()
    ensures C.CwdContextFields(io.fs(),state.context)
  {
    Spec.State(io.cwdContext(),io.statusCursor())
  }

  lemma DirectoriesMatchModel(io: BenchIO.IO)
    ensures Inputs(io).directories == io.directoryModel().observations
  {
    hide *;
    var state := io.directoryState();
  }

  method Status(path: W.Path, follow: bool, io: BenchIO.IO)
    returns (result: W.IOResult<W.FileStatus>, ghost call: Spec.Call)
    modifies io.directoryStateRegion,io.statusObservationsRegion
    ensures Inputs(io) == old(Inputs(io))
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures call.before == old(State(io)) && call.after == State(io)
    ensures call.action == Spec.StatusAction(path,follow,result)
    ensures Spec.CallFields(old(Inputs(io)),call)
  {
    hide *;
    ghost var inputs := Inputs(io);
    ghost var before := State(io);
    result := io.GetFileStatusAtCwd(path,follow);
    call := Spec.Call(before,State(io),Spec.StatusAction(path,follow,result));
    assert Spec.CallFields(inputs,call) by { reveal Spec.CallFields(); }
  }

  method Link(path: W.Path, io: BenchIO.IO)
    returns (result: W.IOResult<W.Path>, ghost call: Spec.Call)
    modifies io.directoryStateRegion
    ensures Inputs(io) == old(Inputs(io))
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures call.before == old(State(io)) && call.after == State(io)
    ensures call.action == Spec.LinkAction(path,result)
    ensures Spec.CallFields(old(Inputs(io)),call)
  {
    hide *;
    ghost var inputs := Inputs(io);
    ghost var before := State(io);
    result := io.ReadLinkAtCwd(path);
    call := Spec.Call(before,State(io),Spec.LinkAction(path,result));
    assert Spec.CallFields(inputs,call) by { reveal Spec.CallFields(); }
  }

  method Open(path: W.Path, dots: bool, io: BenchIO.IO)
    returns (result: W.IOResult<int>, ghost call: Spec.Call)
    modifies io.directoryStateRegion
    ensures Inputs(io) == old(Inputs(io))
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures call.before == old(State(io)) && call.after == State(io)
    ensures call.action == Spec.OpenAction(path,dots,result)
    ensures Spec.CallFields(old(Inputs(io)),call)
  {
    hide *;
    ghost var inputs := Inputs(io);
    ghost var before := State(io);
    result := io.OpenDirAtCwd(path,dots);
    call := Spec.Call(before,State(io),Spec.OpenAction(path,dots,result));
    assert Spec.CallFields(inputs,call) by { reveal Spec.CallFields(); }
  }

  method Read(handle: int, io: BenchIO.IO)
    returns (result: W.IOResult<W.DirectoryRead>, ghost call: Spec.Call)
    requires C.DirectoryOperationCapabilitiesCurrentFields(io.directoryTopology(),
                                                           io.directoryCapabilities(),W.DirectoryReadNext,handle,0)
    modifies io.directoryStateRegion
    ensures Inputs(io) == old(Inputs(io))
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures call.before == old(State(io)) && call.after == State(io)
    ensures call.action == Spec.ReadAction(handle,result)
    ensures Spec.CallFields(old(Inputs(io)),call)
  {
    hide *;
    ghost var inputs := Inputs(io);
    ghost var before := State(io);
    DirectoriesMatchModel(io);
    result := io.ReadDirectoryCapability(handle);
    DirectoriesMatchModel(io);
    call := Spec.Call(before,State(io),Spec.ReadAction(handle,result));
    assert Spec.CallFields(inputs,call) by {
      reveal Spec.CallFields(), C.DirectoryRequestForContextFields();
    }
  }

  method Close(handle: int, io: BenchIO.IO)
    returns (result: W.IOResult<W.Unit>, ghost call: Spec.Call)
    modifies io.directoryStateRegion
    ensures Inputs(io) == old(Inputs(io))
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures call.before == old(State(io)) && call.after == State(io)
    ensures call.action == Spec.CloseAction(handle,result)
    ensures Spec.CallFields(old(Inputs(io)),call)
  {
    hide *;
    ghost var inputs := Inputs(io);
    ghost var before := State(io);
    DirectoriesMatchModel(io);
    result := io.CloseDirectoryCapability(handle);
    DirectoriesMatchModel(io);
    call := Spec.Call(before,State(io),Spec.CloseAction(handle,result));
    assert Spec.CallFields(inputs,call) by {
      reveal Spec.CallFields(), C.DirectoryRequestForContextFields();
    }
  }

  method HandleStatus(handle: int, io: BenchIO.IO)
    returns (result: W.IOResult<W.FileStatus>, ghost call: Spec.Call)
    requires handle in io.directoryCapabilities() ==>
               C.DirectoryCapabilityAnchorCurrentFields(io.directoryTopology(),io.directoryCapabilities()[handle])
    modifies io.directoryStateRegion,io.statusObservationsRegion
    ensures Inputs(io) == old(Inputs(io))
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures call.before == old(State(io)) && call.after == State(io)
    ensures call.action == Spec.HandleStatusAction(handle,result)
    ensures Spec.CallFields(old(Inputs(io)),call)
  {
    hide *;
    ghost var inputs := Inputs(io);
    ghost var before := State(io);
    result := io.GetOpenDirectoryCapabilityStatus(handle);
    call := Spec.Call(before,State(io),Spec.HandleStatusAction(handle,result));
    assert Spec.CallFields(inputs,call) by { reveal Spec.CallFields(); }
  }
}
