include "ChmodChangeRuntime.dfy"
include "ChmodDirectoryRuntime.dfy"

module ChmodDescriptorRuntime {
  import W = BenchWorld
  import BenchIO
  import C = IOContract
  import Base = ChmodCore
  import BaseSpec = ChmodSpec
  import BaseProof = ChmodProof
  import Recursive = ChmodRecursiveSpec
  import Spec = ChmodDescriptorSpec
  import Operand = ChmodOperandSpec
  import Dispatch = ChmodOperandCore
  import Identity = ChmodOperandProof
  import Entry = ChmodEntryRuntime
  import Change = ChmodChangeRuntime
  import Directory = ChmodDirectoryRuntime
  import Frame = ChmodTraversalProof
  import FrameSpec = ChmodTraversalSpec
  import Schema = ChmodSchema

  lemma {:isolate_assertions} AppendDirectoryPrefix(cmd: Schema.ChmodCmd, plan: BaseSpec.SpecModePlan,
    scope: Spec.Scope, identity: Spec.RuntimeIdentity, active: set<W.HostInodeKey>, handle: int,
    initial: Spec.State, readSteps: seq<Spec.DirectoryRead>, children: seq<Spec.Visit>,
    states: seq<Spec.State>, read: Spec.DirectoryRead, child: Spec.Visit, next: Spec.State)
    requires Spec.DirectoryPrefixFields(cmd, plan, scope, identity, active, handle,
      initial, readSteps, children, states, read.before)
    requires Spec.ReadFields(scope, states[|children|].fs, states[|children|].cursor, handle, read)
    requires read.response.err == 0 && read.response.read.DirectoryItem?
    requires Spec.VisitFields(cmd, plan, scope,
      W.AppendPath(identity.displayPath, read.response.read.name),
      Operand.DirectoryOperand(handle, read.response.read.name), false, active+{identity.key},
      states[|children|].fs, read.after, states[|children|].cursor, child)
    requires next == Spec.State(Spec.Result(child).fs, Spec.Result(child).cursor, Spec.Result(child).native,
      states[|children|].output+Spec.Result(child).output,
      states[|children|].diagnostics+Spec.Result(child).diagnostics,
      states[|children|].ok && Spec.Result(child).ok)
    ensures Spec.DirectoryPrefixFields(cmd, plan, scope, identity, active, handle, initial,
      readSteps+[read], children+[child], states+[next], next.native)
  {
    hide *;
    reveal Spec.DirectoryPrefixFields();
    assert Spec.DirectoryStepFields(cmd, plan, scope, identity, active, handle,
      states[|children|], next, read, child) by { reveal Spec.DirectoryStepFields(); }
    forall i: nat | i < |children|+1
      ensures Spec.DirectoryStepFields(cmd, plan, scope, identity, active, handle,
        (states+[next])[i], (states+[next])[i+1], (readSteps+[read])[i], (children+[child])[i])
    {
      if i < |children| {
        assert Spec.DirectoryStepFields(cmd, plan, scope, identity, active, handle,
          states[i], states[i+1], readSteps[i], children[i]);
      }
    }
  }

  lemma {:isolate_assertions} AppendFiles(file: string, files: seq<string>,
    cmd: Schema.ChmodCmd, plan: BaseSpec.SpecModePlan, scope: Spec.Scope,
    fs: W.FileSystem, native: W.CwdContext, cursor: nat, current: Spec.State,
    observation: Spec.Files, next: Spec.State, visit: Spec.Visit)
    requires Spec.FilesFields(files, cmd, plan, scope, fs, native, cursor, current, observation)
    requires Spec.FileStepFields(file, cmd, plan, scope, current, next, visit)
    ensures Spec.FilesFields(files+[file], cmd, plan, scope, fs, native, cursor, next,
      Spec.Files(observation.visits+[visit], observation.states+[next]))
  {
    hide *;
    reveal Spec.FilesFields();
    forall i: nat | i < |files|+1
      ensures Spec.FileStepFields((files+[file])[i], cmd, plan, scope,
        (observation.states+[next])[i], (observation.states+[next])[i+1], (observation.visits+[visit])[i])
    {
      if i < |files| {
        assert Spec.FileStepFields(files[i], cmd, plan, scope,
          observation.states[i], observation.states[i+1], observation.visits[i]);
      }
    }
  }

  method {:isolate_assertions} Visit(cmd: Schema.ChmodCmd, plan: Base.CoreModePlan, scope: Spec.Scope,
    display: string, operand: Operand.Operand, top: bool, active: set<W.HostInodeKey>,
    ghost universe: set<W.HostInodeKey>, io: BenchIO.IO, output: Base.Output)
    returns (ok: bool, ghost visit: Spec.Visit)
    requires Entry.ScopeFields(io, scope)
    requires Operand.AnchorFields(io, operand)
    requires cmd.recursive && cmd.preserveRoot ==> scope.root.RootChecked?
    requires active <= universe && io.cwdContext().topology.objects.Keys == universe
    modifies io.fsRegion, io.directoryStateRegion, io.statusObservationsRegion, output
    ensures Entry.ScopeFields(io, scope)
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures io.directoryObservations() == old(io.directoryObservations())
    ensures io.cwdContext().capabilities == old(io.cwdContext()).capabilities
    ensures FrameSpec.FrameFields(old(io.cwdContext()), io.cwdContext())
    ensures W.FileSystemTopologyUnchangedExceptMode(old(io.fs()), io.fs())
    ensures Operand.AnchorFields(io, operand)
    ensures Spec.VisitFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, display, operand, top, active,
      old(io.fs()), old(io.cwdContext()), old(io.statusCursor()), visit)
    ensures var result := Spec.Result(visit);
      result.fs == io.fs() && result.native == io.cwdContext() && result.cursor == io.statusCursor() &&
      result.ok == ok && output.stdout == old(output.stdout)+result.output &&
      output.stderr == old(output.stderr)+result.diagnostics
    decreases |universe-active|, 0
  {
    hide *;
    reveal Spec.Result();
    ghost var fs0 := io.fs();
    ghost var native0 := io.cwdContext();
    ghost var cursor0 := io.statusCursor();
    ghost var stdout0 := output.stdout;
    ghost var stderr0 := output.stderr;
    var identity, decision, entryOut, entryErr, entry := Entry.ReadEntry(cmd, scope, display, operand, top, io);
    output.stdout := output.stdout+entryOut;
    output.stderr := output.stderr+entryErr;
    Frame.Entry(cmd, scope, display, operand, top, fs0, native0, cursor0, entry);
    assert Entry.ScopeFields(io, scope) by { reveal Entry.ScopeFields(); }
    assert entry.fs == fs0 && entry.native == native0 && entry.cursor == cursor0 by { reveal Spec.EntryFields(); }
    assert entry.identity == identity && identity.displayPath == display &&
      identity.operand == operand && identity.top == top by { reveal Spec.EntryFields(); }
    if !decision.EntryReady? {
      ok := decision.EntrySkipped?;
      visit := Spec.EntryVisit(entry);
      Identity.TopologyReflexive(fs0);
      assert Spec.VisitFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, display, operand, top,
        active, fs0, native0, cursor0, visit) by { reveal Spec.VisitFields(); }
      return;
    }
    assert entry.fs == fs0 && entry.result.output == [] && entry.result.diagnostics == [] by {
      reveal Spec.EntryFields();
    }
    ghost var entryNative := io.cwdContext();
    C.CwdTargetRecordIsObservedFields(io.fs(), entryNative, entry.targets[0]);
    assert identity.key in entryNative.topology.objects;
    Frame.Projection(native0, entryNative);
    assert identity.key in universe;
    var parentOk, change := Change.Apply(cmd, plan, scope, identity, entry, io, output);
    Frame.Transitive(native0, entryNative, io.cwdContext());
    Frame.Projection(native0, io.cwdContext());
    if !cmd.recursive || !identity.isDirectory ||
      (identity.isSymlink && !Recursive.TraversalFollowSpec(cmd, top)) || identity.key in active {
      ok := parentOk;
      visit := Spec.NodeVisit(entry, change, Spec.ListingSkipped, change.result);
      assert Spec.VisitFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, display, operand, top,
        active, fs0, native0, cursor0, visit) by { reveal Spec.VisitFields(); }
      return;
    }
    ghost var changeFs := io.fs();
    ghost var changeNative := io.cwdContext();
    ok, visit := Children(cmd, plan, scope, identity, entry, change, active, universe, parentOk,
      stdout0, stderr0, io, output);
    Identity.TopologyTransitive(fs0, changeFs, io.fs());
    Frame.Transitive(native0, changeNative, io.cwdContext());
    assert Operand.AnchorSnapshot(fs0, native0, operand) by { reveal Operand.AnchorFields(); }
    Frame.Anchor(fs0, io.fs(), native0, io.cwdContext(), operand);
    assert Operand.AnchorFields(io, operand) by { reveal Operand.AnchorFields(); }
  }

  method {:isolate_assertions} Children(cmd: Schema.ChmodCmd, plan: Base.CoreModePlan, scope: Spec.Scope,
    identity: Spec.RuntimeIdentity, ghost entry: Spec.Entry, ghost change: Spec.Change,
    active: set<W.HostInodeKey>, ghost universe: set<W.HostInodeKey>, initialOk: bool,
    ghost stdout0: W.Bytes, ghost stderr0: W.Bytes, io: BenchIO.IO, output: Base.Output)
    returns (ok: bool, ghost visit: Spec.Visit)
    requires Entry.ScopeFields(io, scope) && Operand.AnchorFields(io, identity.operand)
    requires cmd.recursive && (!cmd.preserveRoot || scope.root.RootChecked?)
    requires entry.identity == identity && entry.decision.EntryReady?
    requires Spec.EntryFields(cmd, scope, identity.displayPath, identity.operand, identity.top,
      entry.fs, entry.native, entry.cursor, entry)
    requires Spec.ChangeFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, entry,
      entry.fs, entry.result.native, entry.result.cursor, change)
    requires identity.isDirectory && !(identity.isSymlink && !Recursive.TraversalFollowSpec(cmd, identity.top))
    requires active <= universe && identity.key in universe-active
    requires io.cwdContext().topology.objects.Keys == universe
    requires change.result.fs == io.fs() && change.result.native == io.cwdContext() &&
      change.result.cursor == io.statusCursor() && change.result.ok == initialOk
    requires output.stdout == stdout0+change.result.output && output.stderr == stderr0+change.result.diagnostics
    modifies io.fsRegion, io.directoryStateRegion, io.statusObservationsRegion, output
    ensures Entry.ScopeFields(io, scope)
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures io.directoryObservations() == old(io.directoryObservations())
    ensures io.cwdContext().capabilities == old(io.cwdContext()).capabilities
    ensures FrameSpec.FrameFields(old(io.cwdContext()), io.cwdContext())
    ensures W.FileSystemTopologyUnchangedExceptMode(old(io.fs()), io.fs())
    ensures Spec.VisitFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, identity.displayPath,
      identity.operand, identity.top, active, entry.fs, entry.native, entry.cursor, visit)
    ensures var result := Spec.Result(visit);
      result.fs == io.fs() && result.native == io.cwdContext() && result.cursor == io.statusCursor() &&
      result.ok == ok && output.stdout == stdout0+result.output && output.stderr == stderr0+result.diagnostics
    decreases |universe-(active+{identity.key})|, 1
  {
    hide *;
    reveal Spec.Result();
    ghost var fs0 := io.fs();
    ghost var native0 := io.cwdContext();
    ghost var cursor0 := io.statusCursor();
    ghost var context := BaseSpec.Context(io);
    assert context == BaseSpec.AtCursor(scope.context, cursor0) by {
      reveal Entry.ScopeFields(), BaseSpec.Context(), BaseSpec.AtCursor();
    }
    var openResult := Dispatch.Open(identity.operand, io);
    Frame.Open(context, fs0, native0, identity.operand, io.cwdContext(), openResult.Ok?,
      C.ResultValue(openResult, 0), C.ResultErrno(openResult));
    Frame.Projection(native0, io.cwdContext());
    assert Entry.ScopeFields(io, scope) by { reveal Entry.ScopeFields(); }
    assert io.directoryObservations() == scope.directories by { reveal Entry.ScopeFields(); }
    Identity.TopologyReflexive(fs0);
    if openResult.Err? {
      assert io.cwdContext().capabilities == native0.capabilities by { reveal Operand.AtOffset(); }
      var err := C.ResultErrno(openResult);
      var outChunk := if cmd.verbose then BaseSpec.AccessFailureMessageSpec(identity.displayPath) else [];
      var errChunk := if cmd.silent then [] else
        Recursive.ReadDirectoryText(identity.displayPath, Base.NativeErrnoTextCore(err, io));
      output.stdout := output.stdout+outChunk;
      output.stderr := output.stderr+errChunk;
      ok := false;
      ghost var result := Spec.State(io.fs(), io.statusCursor(), io.cwdContext(), change.result.output+outChunk,
        change.result.diagnostics+errChunk, false);
      visit := Spec.NodeVisit(entry, change, Spec.ListingOpenFailed(err, io.cwdContext()), result);
      assert Spec.VisitFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, identity.displayPath,
        identity.operand, identity.top, active, entry.fs, entry.native, entry.cursor, visit) by {
        reveal Spec.VisitFields(), C.ResultValue();
      }
      return;
    }
    var handle := openResult.v;
    ghost var afterOpen := io.cwdContext();
    assert C.ResultValue(openResult, 0) == handle by { reveal C.ResultValue(); }
    ghost var initial := change.result.(native := afterOpen);
    ghost var readSteps: seq<Spec.DirectoryRead> := [];
    ghost var children: seq<Spec.Visit> := [];
    ghost var states: seq<Spec.State> := [initial];
    ghost var terminal: Spec.DirectoryRead;
    var terminalErr := 0;
    var hadEntries := false;
    ok := initialOk;
    assert Spec.DirectoryPrefixFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, identity, active,
      handle, initial, readSteps, children, states, afterOpen) by { reveal Spec.DirectoryPrefixFields(); }
    while true
      invariant Entry.ScopeFields(io, scope)
      invariant io.dirHandles() == native0.legacyHandles && io.directoryOrigins() == native0.legacyOrigins
      invariant io.directoryObservations() == scope.directories
      invariant FrameSpec.FrameFields(native0, io.cwdContext())
      invariant W.FileSystemTopologyUnchangedExceptMode(fs0, io.fs())
      invariant io.cwdContext().topology.objects.Keys == universe
      invariant handle in io.cwdContext().capabilities && handle !in native0.capabilities
      invariant io.cwdContext().capabilities.Keys == native0.capabilities.Keys+{handle}
      invariant forall h | h in native0.capabilities :: io.cwdContext().capabilities[h] == native0.capabilities[h]
      invariant !io.cwdContext().capabilities[handle].includeDots
      invariant C.DirectoryCapabilityReadCurrentFields(io.cwdContext().topology, io.cwdContext().capabilities[handle])
      invariant Spec.DirectoryPrefixFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, identity, active,
        handle, initial, readSteps, children, states, io.cwdContext())
      invariant |states| == |children|+1 && hadEntries == (|children| > 0)
      invariant states[|children|].fs == io.fs() && states[|children|].native == io.cwdContext() &&
        states[|children|].cursor == io.statusCursor() && states[|children|].ok == ok
      invariant output.stdout == stdout0+states[|children|].output &&
        output.stderr == stderr0+states[|children|].diagnostics
      decreases |io.cwdContext().capabilities[handle].remaining|
    {
      ghost var beforeRead := io.cwdContext();
      ghost var beforeReadFs := io.fs();
      var read, observation := Directory.Read(scope, handle, io);
      Frame.Transitive(native0, beforeRead, io.cwdContext());
      Frame.Projection(native0, io.cwdContext());
      if read.Err? || read.v.DirectoryEnd? {
        terminal := observation;
        terminalErr := C.ResultErrno(read);
        break;
      }
      var name := read.v.name;
      ghost var readNative := io.cwdContext();
      assert Operand.AnchorFields(io, Operand.DirectoryOperand(handle, name)) by {
        reveal Operand.AnchorFields(), Operand.AnchorSnapshot(),
          C.DirectoryParentAnchorForContextRequestFields(), C.DirectoryCapabilityReadCurrentFields();
      }
      var childOk, child := Visit(cmd, plan, scope, W.AppendPath(identity.displayPath, name),
        Operand.DirectoryOperand(handle, name), false, active+{identity.key}, universe, io, output);
      Identity.TopologyTransitive(fs0, beforeReadFs, io.fs());
      Frame.Transitive(native0, readNative, io.cwdContext());
      Frame.Projection(native0, io.cwdContext());
      Frame.ReadCurrent(readNative, io.cwdContext(), readNative.capabilities[handle]);
      ghost var step := Spec.Result(child);
      ghost var last := states[|children|];
      ghost var next := Spec.State(step.fs, step.cursor, step.native, last.output+step.output,
        last.diagnostics+step.diagnostics, last.ok && step.ok);
      assert read.Ok? && observation.response.err == 0 && observation.response.read == read.v;
      AppendDirectoryPrefix(cmd, BaseProof.SpecModePlanOfCore(plan), scope, identity, active,
        handle, initial, readSteps, children, states, observation, child, next);
      states := states+[next];
      readSteps := readSteps+[observation];
      children := children+[child];
      hadEntries := true;
      ok := ok && childOk;
    }
    ghost var beforeClose := io.cwdContext();
    var closed, closeResponse := Directory.Close(scope, handle, io);
    Frame.Transitive(native0, beforeClose, io.cwdContext());
    assert io.cwdContext().capabilities == native0.capabilities;
    if terminalErr != 0 {
      if cmd.verbose { output.stdout := output.stdout+BaseSpec.AccessFailureMessageSpec(identity.displayPath); }
      if !cmd.silent {
        output.stderr := output.stderr+Recursive.TerminalReadDirectoryText(identity.displayPath, hadEntries,
          Base.NativeErrnoTextCore(terminalErr, io));
      }
      ok := false;
    }
    ghost var last := states[|children|];
    ghost var result := Spec.State(io.fs(), io.statusCursor(), io.cwdContext(),
      last.output+(if terminalErr != 0 && cmd.verbose then BaseSpec.AccessFailureMessageSpec(identity.displayPath) else []),
      last.diagnostics+(if terminalErr == 0 || cmd.silent then [] else
        Recursive.TerminalReadDirectoryText(identity.displayPath, hadEntries, C.CLocaleErrnoTextResult(terminalErr))),
      last.ok && terminalErr == 0);
    visit := Spec.NodeVisit(entry, change,
      Spec.ListingOpened(afterOpen, handle, readSteps+[terminal], children, states, closeResponse, io.cwdContext()), result);
    assert Spec.VisitFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, identity.displayPath,
      identity.operand, identity.top, active, entry.fs, entry.native, entry.cursor, visit) by {
      reveal Spec.VisitFields(), Spec.DirectoryPrefixFields();
      forall i: nat | i < |children|
        ensures Spec.DirectoryStepFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, identity, active, handle,
          states[i], states[i+1], (readSteps+[terminal])[i], children[i])
      {
        assert (readSteps+[terminal])[i] == readSteps[i];
      }
    }
  }

  method {:isolate_assertions} RunFiles(files: seq<string>, cmd: Schema.ChmodCmd, plan: Base.CoreModePlan,
    scope: Spec.Scope, io: BenchIO.IO, output: Base.Output)
    returns (allOk: bool, ghost observation: Spec.Files, ghost result: Spec.State)
    requires Entry.ScopeFields(io, scope)
    requires cmd.recursive && cmd.preserveRoot ==> scope.root.RootChecked?
    modifies io.fsRegion, io.directoryStateRegion, io.statusObservationsRegion, output
    ensures Entry.ScopeFields(io, scope)
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures io.directoryObservations() == old(io.directoryObservations())
    ensures io.cwdContext().capabilities == old(io.cwdContext()).capabilities
    ensures FrameSpec.FrameFields(old(io.cwdContext()), io.cwdContext())
    ensures W.FileSystemTopologyUnchangedExceptMode(old(io.fs()), io.fs())
    ensures Spec.FilesFields(files, cmd, BaseProof.SpecModePlanOfCore(plan), scope,
      old(io.fs()), old(io.cwdContext()), old(io.statusCursor()), result, observation)
    ensures result.fs == io.fs() && result.native == io.cwdContext() &&
      result.cursor == io.statusCursor() && result.ok == allOk
    ensures output.stdout == old(output.stdout)+result.output && output.stderr == old(output.stderr)+result.diagnostics
  {
    hide *;
    reveal Spec.Result();
    ghost var fs0 := io.fs();
    ghost var native0 := io.cwdContext();
    ghost var cursor0 := io.statusCursor();
    ghost var stdout0 := output.stdout;
    ghost var stderr0 := output.stderr;
    ghost var universe := native0.topology.objects.Keys;
    ghost var visits: seq<Spec.Visit> := [];
    ghost var states: seq<Spec.State> := [Spec.State(fs0, cursor0, native0, [], [], true)];
    allOk := true;
    var i: nat := 0;
    Identity.TopologyReflexive(fs0);
    Frame.Reflexive(native0);
    assert io.directoryObservations() == scope.directories by { reveal Entry.ScopeFields(); }
    assert Spec.FilesFields([], cmd, BaseProof.SpecModePlanOfCore(plan), scope, fs0, native0, cursor0,
      states[0], Spec.Files(visits, states)) by { reveal Spec.FilesFields(); }
    while i < |files|
      invariant i <= |files| && |visits| == i && |states| == i+1
      invariant Entry.ScopeFields(io, scope)
      invariant io.dirHandles() == native0.legacyHandles && io.directoryOrigins() == native0.legacyOrigins
      invariant io.directoryObservations() == scope.directories
      invariant io.cwdContext().capabilities == native0.capabilities
      invariant FrameSpec.FrameFields(native0, io.cwdContext())
      invariant W.FileSystemTopologyUnchangedExceptMode(fs0, io.fs())
      invariant io.cwdContext().topology.objects.Keys == universe
      invariant Spec.FilesFields(files[..i], cmd, BaseProof.SpecModePlanOfCore(plan), scope,
        fs0, native0, cursor0, states[i], Spec.Files(visits, states))
      invariant states[i].fs == io.fs() && states[i].native == io.cwdContext() &&
        states[i].cursor == io.statusCursor() && states[i].ok == allOk
      invariant output.stdout == stdout0+states[i].output && output.stderr == stderr0+states[i].diagnostics
      decreases |files|-i
    {
      ghost var beforeFs := io.fs();
      ghost var beforeNative := io.cwdContext();
      assert Operand.AnchorFields(io, Operand.CwdOperand(files[i])) by {
        reveal Operand.AnchorFields(), Operand.AnchorSnapshot();
      }
      var ok, visit := Visit(cmd, plan, scope, files[i], Operand.CwdOperand(files[i]), true, {}, universe, io, output);
      Identity.TopologyTransitive(fs0, beforeFs, io.fs());
      Frame.Transitive(native0, beforeNative, io.cwdContext());
      Frame.Projection(native0, io.cwdContext());
      ghost var step := Spec.Result(visit);
      ghost var next := Spec.State(step.fs, step.cursor, step.native,
        states[i].output+step.output, states[i].diagnostics+step.diagnostics, allOk && ok);
      assert Spec.FileStepFields(files[i], cmd, BaseProof.SpecModePlanOfCore(plan), scope, states[i], next, visit) by {
        reveal Spec.FileStepFields();
      }
      AppendFiles(files[i], files[..i], cmd, BaseProof.SpecModePlanOfCore(plan), scope, fs0, native0, cursor0,
        states[i], Spec.Files(visits, states), next, visit);
      assert files[..i]+[files[i]] == files[..i+1];
      states := states+[next];
      visits := visits+[visit];
      allOk := allOk && ok;
      i := i+1;
    }
    assert files[..i] == files;
    result := states[i];
    observation := Spec.Files(visits, states);
  }
}
