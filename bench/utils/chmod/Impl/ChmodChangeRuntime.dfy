include "../Spec/ChmodRecursiveSpec.dfy"
include "../Spec/ChmodSpec.dfy"
include "ChmodEntryRuntime.dfy"
include "../Proof/ChmodProof.dfy"
include "../Proof/ChmodTraversalProof.dfy"

module ChmodChangeRuntime {
  import Text = ChmodSpec
  import RecursiveText = ChmodRecursiveSpec
  import W = BenchWorld
  import BenchIO
  import C = IOContract
  import Base = ChmodCore
  import BaseSpec = ChmodSpec
  import BaseProof = ChmodProof
  import Recursive = ChmodRecursiveSpec
  import Operand = ChmodOperandSpec
  import Dispatch = ChmodOperandCore
  import Identity = ChmodOperandProof
  import Entry = ChmodEntryRuntime
  import Spec = ChmodDescriptorSpec
  import Schema = ChmodSchema
  import Frame = ChmodTraversalProof
  import FrameSpec = ChmodTraversalSpec

  lemma {:isolate_assertions} BridgeSuccessOutput(cmd:Schema.ChmodCmd,plan:Base.CoreModePlan,path:string,
                                                  before:bv32,requested:bv32,isDir:bool,fs:W.FileSystem,postOk:bool,postMode:bv32,postErr:int)
    ensures BaseSpec.SuccessOutputRelation(cmd,BaseProof.SpecModePlanOfCore(plan),path,before,requested,isDir,fs,
                                           postOk,postMode,postErr,BaseProof.SpecPathResultOfCore(Base.SuccessfulChangeResultForPost(cmd,plan,path,
                                                                                                                                     before,requested,isDir,fs,postOk,postMode,postErr)))
  {
    BaseProof.BridgeNaiveMode(plan,before,isDir);

    BaseProof.BridgeDiagnoseSurprise(cmd,plan,before,requested,isDir);

    if BaseSpec.SpecPostChangeLookupNeeded(cmd,requested) && postOk {
      BaseProof.BridgeDiagnoseSurprise(cmd,plan,before,postMode,isDir);

    }
    assert BaseSpec.SuccessOutputRelation(cmd,BaseProof.SpecModePlanOfCore(plan),path,before,requested,isDir,fs,
                                          postOk,postMode,postErr,BaseProof.SpecPathResultOfCore(Base.SuccessfulChangeResultForPost(cmd,plan,path,
                                                                                                                                    before,requested,isDir,fs,postOk,postMode,postErr))) by {
      hide *;
      reveal BaseSpec.SuccessOutputRelation(),Base.SuccessfulChangeResultForPost(),
             BaseProof.SpecPathResultOfCore(),BaseProof.SpecPathStatusOfCore();
      assert BaseSpec.SpecNaiveModeRelation(BaseProof.SpecModePlanOfCore(plan),before,isDir,Base.CoreNaiveMode(plan,before,isDir));
    }
  }

  method {:isolate_assertions} Finish(cmd: Schema.ChmodCmd, plan: Base.CoreModePlan, scope: Spec.Scope,
                                      native: Spec.RuntimeIdentity, ghost entry: Spec.Entry, before: bv32, requested: bv32,
                                      io: BenchIO.IO, output: Base.Output) returns (ok: bool, ghost result: Base.CorePathResult)
    requires Entry.ScopeFields(io, scope)
    requires entry.identity == native
    requires Operand.AnchorFields(io, native.operand)
    modifies io.directoryStateRegion, io.statusObservationsRegion, output
    ensures Entry.ScopeFields(io, scope)
    ensures FrameSpec.FrameFields(old(io.cwdContext()), io.cwdContext())
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures io.directoryObservations() == old(io.directoryObservations())
    ensures Spec.SuccessFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, entry,
                               old(io.fs()), old(io.cwdContext()), old(io.statusCursor()), before, requested,
                               io.statusCursor(), io.cwdContext(), BaseProof.SpecPathResultOfCore(result))
    ensures result.fs == io.fs() && result.ok == ok
    ensures output.stdout == old(output.stdout)+result.stdoutChunk && output.stderr == old(output.stderr)+result.stderrChunk
    ensures io.statusCursor() == old(io.statusCursor())+(if BaseSpec.SpecPostChangeLookupNeeded(cmd, requested) then 1 else 0)
    ensures io.cwdContext() == Operand.AtOffset(old(io.cwdContext()), if BaseSpec.SpecPostChangeLookupNeeded(cmd, requested) then 1 else 0)
    ensures Operand.AnchorFields(io, native.operand)
  {
    hide *;
    ghost var fs0 := io.fs();
    ghost var native0 := io.cwdContext();
    ghost var cursor0 := io.statusCursor();
    ghost var context := BaseSpec.Context(io);
    assert context == BaseSpec.AtCursor(scope.context, cursor0) by {
      reveal Entry.ScopeFields(), BaseSpec.Context(), BaseSpec.AtCursor();
    }
    var postOk := true;
    var postMode := requested;
    var postErr := 0;
    if BaseSpec.SpecPostChangeLookupNeeded(cmd, requested) {
      var post := Dispatch.ReadStatus(native.operand, true, io);
      postOk := post.Ok?;
      postMode := C.ResultValue(post, W.DEFAULT_FILE_STATUS).mode;
      postErr := C.ResultErrno(post);
      if post.Ok? { reveal C.ResultValue(); }
    } else {
      assert io.cwdContext() == Operand.AtOffset(native0, 0) by { reveal Operand.AtOffset(); }
    }
    Frame.Offset(native0, if BaseSpec.SpecPostChangeLookupNeeded(cmd, requested) then 1 else 0);
    ok := Base.AppendSuccessfulChangeOutputCore(cmd, plan, native.displayPath, before, requested, native.isDirectory,
                                                postOk, postMode, postErr, io, output);
    ghost var post := Operand.StatusAt(context, fs0, native0, native.operand, 0, true);
    ghost var actualResult := Base.SuccessfulChangeResultForPost(cmd, plan, native.displayPath, before, requested,
                                                                 native.isDirectory, fs0, postOk, postMode, postErr);
    result := Base.SuccessfulChangeResultForPost(cmd, plan, native.displayPath, before, requested, native.isDirectory,
                                                 fs0, post.Ok?, C.ResultValue(post, W.DEFAULT_FILE_STATUS).mode, C.ResultErrno(post));
    assert result == actualResult by { reveal Base.SuccessfulChangeResultForPost(); }
    BridgeSuccessOutput(cmd, plan, native.displayPath, before, requested, native.isDirectory, fs0,
                        post.Ok?, C.ResultValue(post, W.DEFAULT_FILE_STATUS).mode, C.ResultErrno(post));

    assert Spec.SuccessFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, entry, fs0, native0, cursor0,
                              before, requested, io.statusCursor(), io.cwdContext(), BaseProof.SpecPathResultOfCore(result)) by {
      reveal Spec.SuccessFields();
    }
    assert result.fs == fs0 by { reveal Base.SuccessfulChangeResultForPost(); }
    assert Entry.ScopeFields(io, scope) by { reveal Entry.ScopeFields(); }
  }

  method {:isolate_assertions} Apply(cmd: Schema.ChmodCmd, plan: Base.CoreModePlan, scope: Spec.Scope,
                                     native: Spec.RuntimeIdentity, ghost entry: Spec.Entry, io: BenchIO.IO, output: Base.Output)
    returns (ok: bool, ghost change: Spec.Change)
    requires Entry.ScopeFields(io, scope)
    requires entry.identity == native
    requires entry.fs == io.fs() && entry.result.cursor == io.statusCursor() && entry.result.native == io.cwdContext()
    requires Operand.AnchorFields(io, native.operand)
    modifies io.fsRegion, io.directoryStateRegion, io.statusObservationsRegion, output
    ensures Entry.ScopeFields(io, scope)
    ensures FrameSpec.FrameFields(old(io.cwdContext()), io.cwdContext())
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures io.directoryObservations() == old(io.directoryObservations())
    ensures io.cwdContext().capabilities == old(io.cwdContext()).capabilities
    ensures W.FileSystemTopologyUnchangedExceptMode(old(io.fs()), io.fs())
    ensures Operand.AnchorFields(io, native.operand)
    ensures Spec.ChangeFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, entry,
                              old(io.fs()), old(io.cwdContext()), old(io.statusCursor()), change)
    ensures change.result.fs == io.fs() && change.result.native == io.cwdContext() &&
            change.result.cursor == io.statusCursor() && change.result.ok == ok
    ensures output.stdout == old(output.stdout)+change.result.output && output.stderr == old(output.stderr)+change.result.diagnostics
  {
    hide *;
    reveal Operand.AtOffset();
    ghost var fs0 := io.fs();
    ghost var native0 := io.cwdContext();
    ghost var cursor0 := io.statusCursor();
    ghost var context := BaseSpec.Context(io);
    assert context == BaseSpec.AtCursor(scope.context, cursor0) by {
      reveal Entry.ScopeFields(), BaseSpec.Context(), BaseSpec.AtCursor();
    }
    assert scope.cwd == io.cwd() && scope.now == io.now() by { reveal Entry.ScopeFields(); }
    var mode := Dispatch.ReadStatus(native.operand, native.metadataFollow, io);
    ghost var readNative := io.cwdContext();
    Frame.Offset(native0, 1);
    if mode.Err? {
      var err := C.ResultErrno(mode);
      var kind := Recursive.ResolutionFailureKindSpec(cmd, native.top, native.isSymlink, err);
      var outChunk := RecursiveText.RecursiveAccessStdoutSpec(cmd, native.displayPath);
      var errChunk := RecursiveText.NativeAccessText(cmd, native.displayPath, kind, Base.NativeErrnoTextCore(err, io));
      output.stdout := output.stdout+outChunk; output.stderr := output.stderr+errChunk; ok := false;
      change := Spec.Change(Spec.State(fs0, io.statusCursor(), io.cwdContext(), outChunk, errChunk, ok),
                            fs0, io.cwdContext(), 0, 0 as bv32);
      assert Spec.ChangeFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, entry, fs0, native0, cursor0, change) by {
        reveal Spec.ChangeFields();
      }
      Identity.TopologyReflexive(fs0);
      assert Entry.ScopeFields(io, scope) by { reveal Entry.ScopeFields(); }
      return;
    }
    var desired := Base.CorePlannedMode(plan, mode.v.mode, native.isDirectory);
    BaseProof.BridgePlannedMode(plan, mode.v.mode, native.isDirectory);
    var changed := Dispatch.SetMode(native.operand, Spec.ModeFollow(cmd, native.top), desired, io);
    ghost var afterSet := io.fs();
    ghost var afterNative := io.cwdContext();
    var setErr := C.ResultErrno(changed);
    assert Operand.SetFields(BaseSpec.AtCursor(context, cursor0+1), scope.now, fs0, Operand.AtOffset(native0, 1),
                             native.operand, Spec.ModeFollow(cmd, native.top), desired, afterSet, afterNative, changed.Ok?, setErr) by {
      reveal BaseSpec.Context(), BaseSpec.AtCursor(), Entry.ScopeFields();
    }
    Frame.Mode(BaseSpec.AtCursor(context, cursor0+1), scope.now, fs0, readNative, native.operand,
               Spec.ModeFollow(cmd, native.top), desired, afterSet, afterNative, changed.Ok?, setErr);
    Frame.Transitive(native0, readNative, afterNative);
    if changed.Err? {
      var outChunk: W.Bytes;
      var errChunk: W.Bytes;
      if BaseSpec.ModeNotSupported(setErr) {
        outChunk := RecursiveText.RecursiveSkipStdoutSpec(cmd, native.displayPath); errChunk := []; ok := true;
      } else {
        outChunk := if cmd.verbose then Text.FailedChangeMessageSpec(native.displayPath, mode.v.mode, desired) else [];
        errChunk := if cmd.silent then [] else Text.ChangeErrorMessageSpec(native.displayPath, Base.NativeErrnoTextCore(setErr, io));
        ok := false;
      }
      output.stdout := output.stdout+outChunk; output.stderr := output.stderr+errChunk;
      change := Spec.Change(Spec.State(afterSet, io.statusCursor(), afterNative, outChunk, errChunk, ok),
                            afterSet, afterNative, setErr, desired);
      assert Spec.ChangeFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, entry, fs0, native0, cursor0, change) by {
        reveal Spec.ChangeFields();
      }
      assert Entry.ScopeFields(io, scope) by { reveal Entry.ScopeFields(); }
      return;
    }
    assert Entry.ScopeFields(io, scope) by { reveal Entry.ScopeFields(); }
    var finished, result := Finish(cmd, plan, scope, native, entry, mode.v.mode, W.NormalizeMode(desired), io, output);
    Frame.Transitive(native0, afterNative, io.cwdContext());
    ok := finished;
    change := Spec.Change(Spec.State(afterSet, io.statusCursor(), io.cwdContext(), result.stdoutChunk, result.stderrChunk, ok),
                          afterSet, afterNative, setErr, desired);
    assert Spec.ChangeFields(cmd, BaseProof.SpecModePlanOfCore(plan), scope, entry, fs0, native0, cursor0, change) by {
      reveal Spec.ChangeFields(), BaseProof.SpecPathResultOfCore();
    }
    assert Entry.ScopeFields(io, scope) by { reveal Entry.ScopeFields(); }
  }
}
