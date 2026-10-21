include "ChmodObservationProof.dfy"

module ChmodVisitFrameProof {
  import W = BenchWorld
  import C = IOContract
  import Base = ChmodSpec
  import Schema = ChmodSchema
  import Spec = ChmodDescriptorSpec
  import Operand = ChmodOperandSpec
  import Identity = ChmodOperandProof
  import Directory = ChmodDirectoryRuntime
  import State = ChmodObservationProof
  import Frame = ChmodTraversalProof
  import FrameSpec = ChmodTraversalSpec

  lemma {:isolate_assertions} VisitFrame(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
                                         scope: Spec.Scope, display: string, operand: Operand.Operand, top: bool,
                                         active: set<W.HostInodeKey>, fs: W.FileSystem, native: W.CwdContext,
                                         cursor: nat, visit: Spec.Visit)
    requires C.CwdContextFields(fs, native)
    requires Spec.VisitFields(cmd, plan, scope, display, operand, top, active, fs, native, cursor, visit)
    ensures var result := Spec.Result(visit);
            C.CwdContextFields(result.fs, result.native) && FrameSpec.FrameFields(native, result.native) &&
            W.FileSystemTopologyUnchangedExceptMode(fs, result.fs) && result.native.capabilities == native.capabilities
    decreases visit
  {
    hide *;
    reveal Spec.VisitFields(), Spec.Result();
    var entry := visit.entry;
    assert entry.fs == fs && entry.native == native && entry.cursor == cursor &&
           entry.identity.displayPath == display && entry.identity.operand == operand && entry.identity.top == top by {
      reveal Spec.EntryFields();
    }
    State.EntryState(cmd, scope, display, operand, top, fs, native, cursor, entry);
    if visit.EntryVisit? {
      Identity.TopologyReflexive(fs);
    } else {
      var change := visit.change;
      State.ChangeState(cmd, plan, scope, entry, fs, entry.result.native, entry.result.cursor, change);
      Frame.Transitive(native, entry.result.native, change.result.native);
      var listing := visit.listing;
      if listing.ListingSkipped? {
      } else {
        var context := Base.AtCursor(scope.context, change.result.cursor);
        if listing.ListingOpenFailed? {
          Frame.Open(context, change.result.fs, change.result.native, operand,
                     listing.afterOpen, false, 0, listing.err);
          Frame.Transitive(native, change.result.native, listing.afterOpen);
          assert C.CwdContextFields(change.result.fs, listing.afterOpen) &&
                 listing.afterOpen.capabilities == change.result.native.capabilities by {
            reveal Operand.OpenFields(), C.OpenDirAtCwdSpec(), C.OpenDirAtDirSpec(),
                   C.OpenDirFromCwdTargetContractFields(), C.CwdContextReadStepFields();
          }
        } else {
          var handle := listing.handle;
          var afterOpen := listing.afterOpen;
          Frame.Open(context, change.result.fs, change.result.native, operand, afterOpen, true, handle, 0);
          Frame.Transitive(native, change.result.native, afterOpen);
          Identity.FreshCapability(context, change.result.fs, change.result.native, operand, afterOpen, handle);
          assert C.CwdContextFields(change.result.fs, afterOpen) by {
            reveal Operand.OpenFields(), C.OpenDirAtCwdSpec(), C.OpenDirAtDirSpec(), C.OpenDirFromCwdTargetContractFields();
          }
          var n := |listing.children|;
          var i: nat := 0;
          while i < n
            invariant i <= n
            invariant C.CwdContextFields(listing.states[i].fs, listing.states[i].native)
            invariant FrameSpec.FrameFields(native, listing.states[i].native)
            invariant W.FileSystemTopologyUnchangedExceptMode(fs, listing.states[i].fs)
            invariant handle in listing.states[i].native.capabilities && handle !in native.capabilities
            invariant listing.states[i].native.capabilities.Keys == native.capabilities.Keys+{handle}
            invariant forall h | h in native.capabilities :: listing.states[i].native.capabilities[h] == native.capabilities[h]
            invariant !listing.states[i].native.capabilities[handle].includeDots
            invariant C.DirectoryCapabilityReadCurrentFields(listing.states[i].native.topology,
                                                             listing.states[i].native.capabilities[handle])
            decreases n-i
          {
            var before := listing.states[i];
            var after := listing.states[i+1];
            var read := listing.readSteps[i];
            var child := listing.children[i];
            assert Spec.DirectoryStepFields(cmd, plan, scope, entry.identity, active, handle,
                                            before, after, read, child);
            reveal Spec.DirectoryStepFields(), Spec.ReadFields();
            Directory.ReadShape(before.fs, read.before, scope.directories, handle, before.cursor,
                                read.response, read.after);
            State.DirectoryState(before.fs, read.before, scope.directories, W.DirectoryReadNext,
                                 handle, before.cursor, read.response, read.after);
            Frame.Transitive(native, read.before, read.after);
            VisitFrame(cmd, plan, scope, W.AppendPath(display, read.response.read.name),
                       Operand.DirectoryOperand(handle, read.response.read.name), false, active+{entry.identity.key},
                       before.fs, read.after, before.cursor, child);
            var result := Spec.Result(child);
            assert after.fs == result.fs && after.native == result.native;
            Identity.TopologyTransitive(fs, before.fs, result.fs);
            Frame.Transitive(native, read.after, result.native);
            Frame.ReadCurrent(read.after, result.native, read.after.capabilities[handle]);
            assert after.native.capabilities == read.after.capabilities;
            assert read.after.capabilities.Keys == before.native.capabilities.Keys;
            forall h | h in native.capabilities
              ensures after.native.capabilities[h] == native.capabilities[h]
            {
              assert h != handle;
              assert read.after.capabilities[h] == read.before.capabilities[h];
            }
            i := i+1;
          }
          var last := listing.states[n];
          var terminal := listing.readSteps[n];
          assert terminal.before == last.native;
          assert C.ContextOperationSpec(last.fs, terminal.before, scope.directories, W.DirectoryReadNext,
                                        handle, 0, "", last.cursor, last.cursor, terminal.response, terminal.after) by {
            reveal Spec.ReadFields();
          }
          Directory.ReadShape(last.fs, terminal.before, scope.directories, handle, last.cursor,
                              terminal.response, terminal.after);
          State.DirectoryState(last.fs, terminal.before, scope.directories, W.DirectoryReadNext,
                               handle, last.cursor, terminal.response, terminal.after);
          Frame.Transitive(native, terminal.before, terminal.after);
          Directory.CloseShape(last.fs, terminal.after, scope.directories, handle, last.cursor,
                               listing.closeResponse, listing.afterClose);
          State.DirectoryState(last.fs, terminal.after, scope.directories, W.DirectoryClose,
                               handle, last.cursor, listing.closeResponse, listing.afterClose);
          Frame.Transitive(native, terminal.after, listing.afterClose);
          assert listing.afterClose.capabilities == native.capabilities;
        }
      }
    }
  }
}
