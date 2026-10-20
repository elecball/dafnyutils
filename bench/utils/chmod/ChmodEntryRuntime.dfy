include "ChmodDescriptorSpec.dfy"
include "ChmodOperandCore.dfy"
include "ChmodCore.dfy"
include "ChmodEntryProof.dfy"

module ChmodEntryRuntime {
  import W = BenchWorld
  import Errno = Errnos
  import BenchIO
  import C = IOContract
  import Base = ChmodCore
  import BaseSpec = ChmodSpec
  import Recursive = ChmodRecursiveSpec
  import Operand = ChmodOperandSpec
  import Dispatch = ChmodOperandCore
  import Proof = ChmodOperandProof
  import Targets = ChmodEntryProof
  import Spec = ChmodDescriptorSpec
  import Schema = ChmodSchema

  ghost predicate ScopeFields(io:BenchIO.IO,scope:Spec.Scope)
    reads io.trustedNativeFailuresRegion,io.cwdRegion,io.nowRegion,
      io.statusObservationsRegion,io.directoryStateRegion
  {
    io.statusObservations()==scope.context.times && io.trustedNativeFailures()==scope.context.failures &&
    io.cwd()==scope.cwd && scope.context.cwd==scope.cwd && io.now()==scope.now &&
    io.directoryObservations()==scope.directories
  }

  method {:isolate_assertions} ReadEntry(cmd:Schema.ChmodCmd,scope:Spec.Scope,display:string,
    operand:Operand.Operand,top:bool,io:BenchIO.IO)
    returns (native:Spec.RuntimeIdentity,decision:Spec.Decision,output:W.Bytes,diagnostics:W.Bytes,ghost entry:Spec.Entry)
    requires ScopeFields(io,scope)
    requires Operand.AnchorFields(io,operand)
    requires cmd.recursive && cmd.preserveRoot ==> scope.root.RootChecked?
    modifies io.directoryStateRegion,io.statusObservationsRegion
    ensures io.dirHandles()==old(io.dirHandles()) && io.directoryOrigins()==old(io.directoryOrigins())
    ensures io.directoryObservations()==old(io.directoryObservations())
    ensures io.directoryCapabilities()==old(io.directoryCapabilities())
    ensures Operand.AnchorFields(io,operand)
    ensures Spec.EntryFields(cmd,scope,display,operand,top,old(io.fs()),old(io.cwdContext()),old(io.statusCursor()),entry)
    ensures entry.identity==native && entry.decision==decision
    ensures entry.result.fs==io.fs() && entry.result.native==io.cwdContext() && entry.result.cursor==io.statusCursor()
    ensures entry.result.output==output && entry.result.diagnostics==diagnostics
    ensures entry.result.ok==(decision.EntrySkipped? || decision.EntryReady?)
    // The same inode identity/kind guarantees hold for every authenticated live
    // target, including a detached object that has no namespace pathname.
    ensures decision.EntryReady? ==> |entry.targets|==1
    ensures decision.EntryReady? ==> C.CwdTargetFields(io.fs(),io.cwdContext(),entry.targets[0])
    ensures decision.EntryReady? ==> native.key==C.CwdTargetRecordFields(io.fs(),io.cwdContext(),entry.targets[0]).hostKey
    ensures decision.EntryReady? ==> (native.isDirectory <==> C.CwdTargetRecordFields(io.fs(),io.cwdContext(),entry.targets[0]).node.Directory?)
    // Retain the original namespace guarantees whenever the target is named.
    ensures decision.EntryReady? ==> var paths:=C.CwdTargetNamedPathFields(io.cwdContext(),entry.targets[0]);
      |paths|==1 ==> (W.FsContainsPath(io.fs(),paths[0]) && native.key==io.fs().inodes[W.FsIdAt(io.fs(),paths[0])].hostKey && native.isDirectory==W.FsNodeAt(io.fs(),paths[0]).Directory?)
  {
    hide *;
    assert scope.cwd==io.cwd() by { reveal ScopeFields(); }
    ghost var fs0:=io.fs();
    ghost var native0:=io.cwdContext();
    ghost var lastRawNative:=native0;
    ghost var cursor0:=io.statusCursor();
    ghost var context:=BaseSpec.Context(io);
    assert context==BaseSpec.AtCursor(scope.context,cursor0) by { reveal ScopeFields(),BaseSpec.Context(),BaseSpec.AtCursor(); }
    var raw:=Dispatch.ReadStatus(operand,false,io);
    ghost var first:=raw;
    var attempts:nat:=1;
    reveal Operand.AtOffset();
    if top && raw.Err? {
      ghost var retryContext:=BaseSpec.Context(io);
      assert retryContext==BaseSpec.AtCursor(context,cursor0+1) by { reveal ScopeFields(),BaseSpec.Context(),BaseSpec.AtCursor(); }
      lastRawNative:=io.cwdContext();
      raw:=Dispatch.ReadStatus(operand,false,io);
      attempts:=2;
      Proof.ShiftStatus(context,fs0,native0,operand,1,false);
      Proof.OffsetAddition(native0,1,1);
    }
    assert lastRawNative==Operand.AtOffset(native0,attempts-1);
    assert io.cwdContext()==Operand.AtOffset(native0,attempts);
    assert raw.Ok?==Operand.StatusAt(context,fs0,native0,operand,attempts-1,false).Ok?;
    assert C.ResultErrno(raw)==C.ResultErrno(Operand.StatusAt(context,fs0,native0,operand,attempts-1,false));
    if raw.Ok? { assert raw.v==Operand.StatusAt(context,fs0,native0,operand,attempts-1,false).v; }
    if raw.Err? {
      var err:=C.ResultErrno(raw);
      native:=Spec.RuntimeIdentity(display,operand,top,false,false,false,W.HostInodeKey(0,0));
      decision:=Spec.EntryFailed(err,Recursive.RecursiveAccess);
      output:=Recursive.RecursiveAccessStdoutSpec(cmd,display);
      diagnostics:=Recursive.NativeAccessText(cmd,display,Recursive.RecursiveAccess,Base.NativeErrnoTextCore(err,io));
      entry:=Spec.Entry(native,fs0,native0,cursor0,attempts,[],decision,
        Spec.State(fs0,io.statusCursor(),io.cwdContext(),output,diagnostics,false));
      assert Spec.EntryFields(cmd,scope,display,operand,top,fs0,native0,cursor0,entry) by { reveal Spec.EntryFields(); }
      return;
    }
    var isLink:=raw.v.kind==W.SymlinkKind;
    ghost var rawTarget:=Operand.ResolveTarget(fs0,lastRawNative,operand,false).v;
    Targets.SameTopologyTarget(fs0,lastRawNative,native0,rawTarget);
    ghost var directoryContext:=BaseSpec.Context(io);
    ghost var beforeMetadata:=io.cwdContext();
    assert directoryContext==BaseSpec.AtCursor(context,cursor0+attempts) by { reveal ScopeFields(),BaseSpec.Context(),BaseSpec.AtCursor(); }
    var directory:=Dispatch.ReadStatus(operand,Spec.MetadataFollow(cmd,top),io);
    Proof.ShiftStatus(context,fs0,native0,operand,attempts,Spec.MetadataFollow(cmd,top));
    Proof.OffsetAddition(native0,attempts,1);
    assert io.cwdContext()==Operand.AtOffset(native0,attempts+1);
    assert directory.Ok?==Operand.StatusAt(context,fs0,native0,operand,attempts,Spec.MetadataFollow(cmd,top)).Ok?;
    assert C.ResultErrno(directory)==C.ResultErrno(Operand.StatusAt(context,fs0,native0,operand,attempts,Spec.MetadataFollow(cmd,top)));
    if directory.Ok? { assert directory.v==Operand.StatusAt(context,fs0,native0,operand,attempts,Spec.MetadataFollow(cmd,top)).v; }
    if directory.Err? {
      var err:=C.ResultErrno(directory);
      if isLink && !Spec.ModeFollow(cmd,top) && Spec.MetadataFollow(cmd,top) && err==Errno.ENOENT {
        native:=Spec.RuntimeIdentity(display,operand,top,true,false,false,raw.v.hostKey);
        decision:=Spec.EntryReady; output:=[]; diagnostics:=[];
        entry:=Spec.Entry(native,fs0,native0,cursor0,attempts,[rawTarget],decision,
          Spec.State(fs0,io.statusCursor(),io.cwdContext(),output,diagnostics,true));
        Targets.SameTopologyTarget(fs0,native0,io.cwdContext(),rawTarget);
        Targets.NamedTargetRecord(fs0,io.cwdContext(),rawTarget);
      } else {
        native:=Spec.RuntimeIdentity(display,operand,top,isLink,false,Spec.MetadataFollow(cmd,top),raw.v.hostKey);
        var kind:=Recursive.ResolutionFailureKindSpec(cmd,top,isLink,err);
        decision:=Spec.EntryFailed(err,kind); output:=Recursive.RecursiveAccessStdoutSpec(cmd,display);
        diagnostics:=Recursive.NativeAccessText(cmd,display,kind,Base.NativeErrnoTextCore(err,io));
        entry:=Spec.Entry(native,fs0,native0,cursor0,attempts,[],decision,
          Spec.State(fs0,io.statusCursor(),io.cwdContext(),output,diagnostics,false));
      }
      assert Spec.EntryFields(cmd,scope,display,operand,top,fs0,native0,cursor0,entry) by { reveal Spec.EntryFields(); }
      return;
    }
    ghost var resolved:=Operand.ResolveTarget(fs0,beforeMetadata,operand,Spec.MetadataFollow(cmd,top)).v;
    Targets.SameTopologyTarget(fs0,beforeMetadata,native0,resolved);
    Targets.SameTopologyTarget(fs0,native0,io.cwdContext(),resolved);
    Targets.NamedTargetRecord(fs0,io.cwdContext(),resolved);
    var isDirectory:=directory.v.kind==W.DirectoryKind;
    native:=Spec.RuntimeIdentity(display,operand,top,isLink,isDirectory,Spec.MetadataFollow(cmd,top),directory.v.hostKey);
    if cmd.recursive && cmd.preserveRoot && isDirectory && scope.root.RootChecked? && native.key==scope.root.key {
      var alias:=display!="/";
      decision:=Spec.EntryPreserved(alias); output:=[]; diagnostics:=Recursive.RootPreserveMessageSpec(display,alias);
    } else { decision:=Spec.EntryReady; output:=[]; diagnostics:=[]; }
    entry:=Spec.Entry(native,fs0,native0,cursor0,attempts,[resolved],decision,
      Spec.State(fs0,io.statusCursor(),io.cwdContext(),output,diagnostics,decision.EntryReady?));
    assert Spec.EntryFields(cmd,scope,display,operand,top,fs0,native0,cursor0,entry) by { reveal Spec.EntryFields(); }
  }
}
