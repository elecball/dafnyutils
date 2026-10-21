include "RmTextCore.dfy"
include "RmWorldPathCore.dfy"
include "RmSchema.dfy"
include "RmSpec.dfy"
include "RmProof.dfy"

module RmCore {
  import Text = RmTextCore
  import RawPath = RmWorldPathCore
  import opened BenchWorld
  import BenchIO
  import R = Results
  import Schema = RmSchema
  import Spec = RmSpec
  import Facts = RmProof
  import Errno = Errnos
  import C = IOContract
  import Utf8Semantics = RmUtf8Core
  import PathCore = RmPathCore

  class OutputBuffer {
    var output: Bytes
    var diagnostics: Bytes
    constructor()
      ensures output == [] && diagnostics == []
    {
      output := [];
      diagnostics := [];
    }
  }

  method CannotRemoveMessage(io: BenchIO.IO, path: Path, err: int) returns (text: Bytes)
    ensures text == Spec.CannotRemoveText(path,err)
  {
    var quoted := io.QuoteafPath(path);
    var reason := io.GetCLocaleErrnoText(err);
    text := Text.CannotRemoveMessage(quoted,reason);
  }

  method RefusalMessage(io: BenchIO.IO, path: Path, why: Spec.Refusal) returns (text: Bytes)
    ensures text == Spec.RefusalText(path,why)
  {
    var quoted := io.QuoteafPath(path);
    var quotedParent := io.QuoteafPath(Spec.ChildPath(path,".."));
    text := Text.RefusalMessage(path,why,quoted,quotedParent);
  }

  method ModeErrorMessage(io: BenchIO.IO, mode: Schema.RmMode) returns (text: Bytes)
    ensures text == Spec.ModeErrorText(mode)
  {
    var quoted: Bytes := [];
    if mode.ModeInvalidPreserve? { quoted := io.QuoteafPath(mode.value); }
    else if mode.ModeInvalidInteractive? {
      quoted := io.QuoteArgument(Utf8Semantics.Encode(mode.value));
    }
    text := Spec.ModeErrorMessage(mode,quoted);
  }

  method CommandPath(path: Path) returns (value: Path)
    ensures Spec.CommandPath(path,value)
  {
    var trimmed := PathCore.TrimTrailingSlashes(path);
    value := if |path| > 0 && path[|path|-1] == '/' && trimmed != "/"
    then trimmed + "/" else trimmed;
    Facts.TrimmedSummaryGivesCommandPath(path,trimmed,value);
  }

  method InspectPath(io: BenchIO.IO, path: Path) returns (status: IOResult<FileTimeStatus>)
    ensures Spec.StatusResult(io.fs(),io.trustedFilesystem(),path,status)
  {
    var lookup := PathCore.TrimTrailingSlashes(path);
    Facts.TrimmedSummaryGivesStatusPath(path,lookup);
    status := io.GetFileTimes(lookup,false);
  }

  method ReadDirectory(io: BenchIO.IO, path: Path) returns (listing: Spec.Listing)
    modifies io.dirHandlesRegion
    ensures Spec.Listed(Spec.ObservationContextFor(io), io.fs(),path,listing)
    ensures io.dirHandles() == old(io.dirHandles())
  {
    ghost var beforeHandles := io.dirHandles();
    ghost var context := Spec.ObservationContextFor(io);
    var openResult := io.OpenDir(path,false);
    assert C.OpenDirOutcomeFields(io.fs(),path,openResult.Ok?,C.ResultErrno(openResult)) by {
      hide *; reveal Spec.ObservationContextFor();
      reveal C.OpenDirSpec;
      reveal C.OpenDirContractFields;
    }
    if openResult.Err? {
      assert 0 < C.ResultErrno(openResult) by {
        hide *; reveal Spec.ObservationContextFor();
        reveal C.OpenDirOutcomeFields;
        reveal Errno.EINVAL;
      }
      assert io.dirHandles() == beforeHandles;
      listing := Spec.Listing([],{},C.ResultErrno(openResult),0);
      assert C.OpenDirSpec(io.fs(), context.handles, context.failures, io.dirHandles(),
                           path, false, false, 0, listing.openError) by {
        hide *; reveal Spec.ObservationContextFor(); reveal Spec.ObservationContextFor(), C.ResultValue(), C.ResultErrno();
      }
      Facts.ListingOpenFailureWitness(context, io.fs(), path, listing, io.dirHandles());
      assert Spec.ObservationContextFor(io) == context by { reveal Spec.ObservationContextFor(); }
      assert Spec.Listed(context, io.fs(),path,listing) by {
        hide *; reveal Spec.ObservationContextFor();
        reveal Spec.Listed;
      }
      hide *; reveal Spec.ObservationContextFor();
      return;
    }
    assert C.OpenDirOutcomeFields(io.fs(),path,true,0);
    var handle := openResult.v;
    ghost var initial := io.dirHandles()[handle].remaining;
    ghost var resolved := io.dirHandles()[handle].path;
    assert C.ResolvePathForMetadataFields(io.fs(),path,true) == R.Ok(resolved);
    assert FsContainsPath(io.fs(),resolved);
    assert initial == C.DirectoryEntriesForPathFields(io.fs(),resolved);
    Facts.EntryNamesUnique(io.fs(),resolved);
    ghost var initialHandles := io.dirHandles();
    ghost var steps: seq<Spec.DirectoryObservation> := [];
    ghost var beforeEnd := io.dirHandles();
    ghost var afterEnd := io.dirHandles();
    ghost var endKind := UnknownDirentKind;
    ghost var seen: set<DirEntry> := {};
    var names: seq<string> := [];
    var readError := 0;
    while true
      modifies io.dirHandlesRegion
      invariant handle in io.dirHandles()
      invariant io.dirHandles()[handle].DirHandleState?
      invariant io.dirHandles()[handle].path == resolved
      invariant io.dirHandles().Keys == beforeHandles.Keys + {handle}
      invariant forall h :: h in beforeHandles ==> io.dirHandles()[h] == beforeHandles[h]
      invariant seen + io.dirHandles()[handle].remaining == initial
      invariant seen * io.dirHandles()[handle].remaining == {}
      invariant Spec.Names(names) == Spec.EntryNames(seen)
      invariant |Spec.Names(names)| == |names|
      invariant Spec.ReadPrefix(io.fs(), context, handle, initialHandles, names, steps, io.dirHandles())
      invariant readError == 0
      decreases |io.dirHandles()[handle].remaining|
    {
      ghost var prior := io.dirHandles();
      var result := io.ReadDir(handle);
      assert 0 <= C.ResultErrno(result) by {
        hide *; reveal Spec.ObservationContextFor();
        reveal C.ReadDirSpec;
        reveal C.ReadDirContractFields;
      }
      if result.Err? {
        beforeEnd, afterEnd, endKind := prior, io.dirHandles(), UnknownDirentKind;
        readError := C.ResultErrno(result);
        break;
      } else if result.v.DirectoryEnd? {
        beforeEnd, afterEnd, endKind := prior, io.dirHandles(), UnknownDirentKind;
        assert prior[handle].remaining == {};
        break;
      } else {
        var name := result.v.name;
        ghost var step := Spec.DirectoryObservation(prior, io.dirHandles(), true, name, result.v.kind, 0);
        Facts.AppendReadPrefix(context, io.fs(), handle, initialHandles, names, steps,
                               prior, io.dirHandles(), name, result.v.kind);
        steps := steps + [step];
        ghost var entry :| entry in prior[handle].remaining && entry.name == name &&
                           io.dirHandles()[handle].remaining == prior[handle].remaining - {entry};
        assert name !in Spec.Names(names) by {
          if name in Spec.Names(names) {
            var previous :| previous in seen && previous.name == name;
            assert previous == entry;
          }
        }
        Facts.AppendDirectoryName(names,seen,entry);
        seen := seen + {entry};
        names := names + [name];
        assert Spec.ReadPrefix(io.fs(), context, handle, initialHandles, names, steps, io.dirHandles());
      }
    }
    assert 0 <= readError;
    assert readError == 0 ==> io.dirHandles()[handle].remaining == {};
    assert Spec.Names(names) <= Spec.EntryNames(initial) by {
      hide *; reveal Spec.ObservationContextFor();
      reveal Spec.EntryNames;
    }
    assert readError == 0 ==> Spec.Names(names) == Spec.EntryNames(initial);
    listing := Spec.Listing(names,initial,0,readError);
    assert exists candidate: Path ::
        C.ResolvePathForMetadataFields(io.fs(),path,true) == R.Ok(candidate) &&
        FsContainsPath(io.fs(),candidate) &&
        listing.entries == C.DirectoryEntriesForPathFields(io.fs(),candidate);
    assert Spec.ReadPrefix(io.fs(), context, handle, initialHandles, names, steps, beforeEnd);
    var closeResult := io.CloseDir(handle);
    assert io.dirHandles() == beforeHandles;
    assert C.OpenDirSpec(io.fs(), context.handles, context.failures, initialHandles,
                         path, false, true, handle, 0) by { hide *; reveal Spec.ObservationContextFor(); reveal Spec.ObservationContextFor(), C.ResultValue(), C.ResultErrno(); }
    assert C.CloseDirSpec(afterEnd, context.failures, context.handles,
                          handle, closeResult.Ok?, C.ResultErrno(closeResult)) by { hide *; reveal Spec.ObservationContextFor(); reveal Spec.ObservationContextFor(), C.ResultValue(), C.ResultErrno(); }
    Facts.ListingReadWitness(context, io.fs(), path, listing, initialHandles, handle,
                             steps, beforeEnd, afterEnd, endKind, closeResult.Ok?, C.ResultErrno(closeResult));
    assert Spec.ObservationContextFor(io) == context by { reveal Spec.ObservationContextFor(); }
    assert Spec.Listed(context, io.fs(),path,listing) by {
      hide *; reveal Spec.ObservationContextFor();
      reveal Spec.Listed();
    }
    hide *; reveal Spec.ObservationContextFor();
  }

  method Excise(raw: Schema.RmCmdRaw, io: BenchIO.IO, buffer: OutputBuffer, path: Path, directory: bool,
                earlierError: int) returns (failed: bool, ok: bool, err: int)
    modifies io.fsRegion, buffer
    ensures Spec.Attempt(raw,path,directory,old(io.now()),old(io.trustedFilesystem()),
                         old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,ok,err,earlierError,failed)
    ensures Spec.HostKeys(io.fs()) <= Spec.HostKeys(old(io.fs()))
  {
    ghost var before: FileSystem := io.fs();
    var result: IOResult<Unit>;
    if directory { result := io.RemoveDirectory(path); }
    else { result := io.UnlinkPath(path); }
    ok := result.Ok?;
    err := C.ResultErrno(result);
    // Native removal establishes the exact relation consumed by RemovalKeys.
    hide C.RemoveDirectorySpec;
    hide C.UnlinkPathSpec;
    assert Spec.HostKeys(io.fs()) <= Spec.HostKeys(before) by {
      hide *; reveal Spec.ObservationContextFor();
      Facts.RemovalKeys(before,io.fs(),path,directory,io.now(),io.trustedFilesystem(),ok,err);
    }
    failed := !ok && !Spec.Ignored(raw,err);
    if ok && raw.verbose {
      var quoted := io.QuoteafPath(path);
      buffer.output := buffer.output + Spec.RemovedMessage(quoted,directory);
    }
    if failed {
      var text := CannotRemoveMessage(io,path,Spec.ReportedErrno(err,earlierError));
      buffer.diagnostics := buffer.diagnostics + text;
    }
    assert Spec.Attempt(raw,path,directory,old(io.now()),old(io.trustedFilesystem()),
                        old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,ok,err,earlierError,failed) by {
      hide *; reveal Spec.ObservationContextFor();
      reveal Spec.Attempt;
      reveal Spec.RemovedText;
    }
    hide *; reveal Spec.ObservationContextFor();
  }

  method Remove(raw: Schema.RmCmdRaw, io: BenchIO.IO, buffer: OutputBuffer, path: Path, top: bool,
                rootKey: HostInodeKey, rootDevice: int, seen: set<HostInodeKey>, ghost universe: set<HostInodeKey>)
    returns (failed: bool, ghost proof: Spec.Removal)
    requires Spec.HostKeys(io.fs()) <= universe
    modifies io.fsRegion, io.dirHandlesRegion, buffer
    ensures Spec.RemoveJudgment(Spec.ObservationContextFor(io), raw,path,top,Spec.RemovalScope(rootKey,rootDevice,seen),old(io.now()),old(io.trustedFilesystem()),
                                old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,failed,proof)
    ensures Spec.HostKeys(io.fs()) <= universe
    ensures io.dirHandles() == old(io.dirHandles())
    decreases universe - seen, 3
  {
    var status := InspectPath(io,path);
    assert Spec.StatusResult(io.fs(),io.trustedFilesystem(),path,status);
    // InspectPath separately proves this exact native query contract.
    hide C.GetFileTimesSpec;
    if status.Err? || !status.v.isDir {
      var bad, ok, err := Excise(raw,io,buffer,path,false,0);
      failed := bad;
      proof := Spec.Atomic(status,false,Spec.Listing([],{},0,0),ok,err);
      hide *; reveal Spec.ObservationContextFor();
      Facts.AtomicJudgment(Spec.ObservationContextFor(io), raw,path,top,rootKey,rootDevice,seen,io.now(),io.trustedFilesystem(),
                           old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,failed,
                           status,false,Spec.Listing([],{},0,0),ok,err);
      hide *; reveal Spec.ObservationContextFor();
      return;
    }
    failed, proof := RemoveDirectory(raw,io,buffer,path,top,rootKey,rootDevice,seen,universe,status);
    hide *; reveal Spec.ObservationContextFor();
  }

  method RemoveDirectory(raw: Schema.RmCmdRaw, io: BenchIO.IO, buffer: OutputBuffer, path: Path, top: bool,
                         rootKey: HostInodeKey, rootDevice: int, seen: set<HostInodeKey>, ghost universe: set<HostInodeKey>, status: IOResult<FileTimeStatus>)
    returns (failed: bool, ghost proof: Spec.Removal)
    requires Spec.HostKeys(io.fs()) <= universe
    requires status.Ok? && status.v.isDir
    requires Spec.StatusResult(io.fs(),io.trustedFilesystem(),path,status)
    modifies io.fsRegion, io.dirHandlesRegion, buffer
    ensures Spec.RemoveJudgment(Spec.ObservationContextFor(io), raw,path,top,Spec.RemovalScope(rootKey,rootDevice,seen),old(io.now()),old(io.trustedFilesystem()),
                                old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,failed,proof)
    ensures Spec.HostKeys(io.fs()) <= universe
    ensures io.dirHandles() == old(io.dirHandles())
    decreases universe - seen, 2
  {
    Facts.StatusKey(io.fs(),io.trustedFilesystem(),path,status);
    // Preserve the established query relation without expanding its resolver.
    hide C.GetFileTimesSpec;
    var why := BasicRefusalCore(raw,path,top,rootKey,rootDevice,seen,status.v);
    var parent: IOResult<FileTimeStatus> := status;
    if why != Spec.NoRefusal {
      var text := RefusalMessage(io,path,why);
      buffer.diagnostics := buffer.diagnostics + text;
      proof := Spec.Refused(status,why,parent);
      failed := true;
      hide *; reveal Spec.ObservationContextFor();
      Facts.RefusedJudgment(Spec.ObservationContextFor(io), raw,path,top,rootKey,rootDevice,seen,io.now(),io.trustedFilesystem(),
                            old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,failed,status,why,parent);
      hide *; reveal Spec.ObservationContextFor();
      return;
    }
    if raw.recursive && raw.preserveAll && top {
      parent := InspectPath(io,Spec.ChildPath(path,".."));
      if parent.Err? { why := Spec.ParentRefusal; }
      else if parent.v.device != status.v.device { why := Spec.PreserveDeviceRefusal; }
      if why != Spec.NoRefusal {
        var text := RefusalMessage(io,path,why);
        buffer.diagnostics := buffer.diagnostics + text;
        proof := Spec.Refused(status,why,parent);
        failed := true;
        hide *; reveal Spec.ObservationContextFor();
        Facts.RefusedJudgment(Spec.ObservationContextFor(io), raw,path,top,rootKey,rootDevice,seen,io.now(),io.trustedFilesystem(),
                              old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,failed,status,why,parent);
        hide *; reveal Spec.ObservationContextFor();
        return;
      }
    }
    assert Spec.ParentAllowed(raw,path,top,status.v,io.fs(),io.trustedFilesystem());
    if !raw.recursive {
      var bad, ok, err := Excise(raw,io,buffer,path,true,0);
      failed := bad;
      proof := Spec.Atomic(status,true,Spec.Listing([],{},0,0),ok,err);
      hide *; reveal Spec.ObservationContextFor();
      Facts.AtomicJudgment(Spec.ObservationContextFor(io), raw,path,top,rootKey,rootDevice,seen,io.now(),io.trustedFilesystem(),
                           old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,failed,
                           status,true,Spec.Listing([],{},0,0),ok,err);
      hide *; reveal Spec.ObservationContextFor();
      return;
    }
    var key := HostInodeKey(status.v.device,status.v.inode);
    Facts.StatusKey(io.fs(),io.trustedFilesystem(),path,status);
    assert key in universe && key !in seen;
    failed, proof := RemoveHierarchy(raw,io,buffer,path,top,rootKey,rootDevice,seen,universe,status);
    hide *; reveal Spec.ObservationContextFor();
  }

  method RemoveHierarchy(raw: Schema.RmCmdRaw, io: BenchIO.IO, buffer: OutputBuffer, path: Path, top: bool,
                         rootKey: HostInodeKey, rootDevice: int, seen: set<HostInodeKey>, ghost universe: set<HostInodeKey>, status: IOResult<FileTimeStatus>)
    returns (failed: bool, ghost proof: Spec.Removal)
    requires Spec.HostKeys(io.fs()) <= universe
    requires status.Ok? && status.v.isDir
    requires Spec.StatusResult(io.fs(),io.trustedFilesystem(),path,status)
    requires raw.recursive
    requires Spec.BasicRefusal(raw,path,top,rootKey,rootDevice,seen,status.v) == Spec.NoRefusal
    requires Spec.ParentAllowed(raw,path,top,status.v,io.fs(),io.trustedFilesystem())
    requires HostInodeKey(status.v.device,status.v.inode) in universe - seen
    modifies io.fsRegion, io.dirHandlesRegion, buffer
    ensures Spec.RemoveJudgment(Spec.ObservationContextFor(io), raw,path,top,Spec.RemovalScope(rootKey,rootDevice,seen),old(io.now()),old(io.trustedFilesystem()),
                                old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,failed,proof)
    ensures Spec.HostKeys(io.fs()) <= universe
    ensures io.dirHandles() == old(io.dirHandles())
    decreases universe - seen, 1
  {
    Facts.StatusKey(io.fs(),io.trustedFilesystem(),path,status);
    // Preserve the established query relation without expanding its resolver.
    hide C.GetFileTimesSpec;
    hide BenchWorld.ValidInodeFileSystemData;
    hide C.ValidFilesystemObservation;
    var listing := ReadDirectory(io,path);
    if listing.openError != 0 || (listing.readError != 0 && listing.order == []) {
      var earlier := if listing.openError != 0 then listing.openError else listing.readError;
      var bad, ok, err := Excise(raw,io,buffer,path,true,earlier);
      failed := bad;
      proof := Spec.Atomic(status,true,listing,ok,err);
      hide *; reveal Spec.ObservationContextFor();
      Facts.AtomicJudgment(Spec.ObservationContextFor(io), raw,path,top,rootKey,rootDevice,seen,io.now(),io.trustedFilesystem(),
                           old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,failed,
                           status,true,listing,ok,err);
      hide *; reveal Spec.ObservationContextFor();
      return;
    }
    failed, proof := ProcessHierarchy(raw,io,buffer,path,top,rootKey,rootDevice,seen,universe,status,listing);
    hide *; reveal Spec.ObservationContextFor();
  }

  method ProcessHierarchy(raw: Schema.RmCmdRaw, io: BenchIO.IO, buffer: OutputBuffer, path: Path, top: bool,
                          rootKey: HostInodeKey, rootDevice: int, seen: set<HostInodeKey>, ghost universe: set<HostInodeKey>, status: IOResult<FileTimeStatus>, listing: Spec.Listing)
    returns (failed: bool, ghost proof: Spec.Removal)
    requires Spec.HostKeys(io.fs()) <= universe
    requires status.Ok? && status.v.isDir
    requires Spec.StatusResult(io.fs(),io.trustedFilesystem(),path,status)
    requires raw.recursive
    requires Spec.BasicRefusal(raw,path,top,rootKey,rootDevice,seen,status.v) == Spec.NoRefusal
    requires Spec.ParentAllowed(raw,path,top,status.v,io.fs(),io.trustedFilesystem())
    requires HostInodeKey(status.v.device,status.v.inode) in universe - seen
    requires Spec.Listed(Spec.ObservationContextFor(io), io.fs(),path,listing) && listing.openError == 0
    requires listing.readError == 0 || |listing.order| > 0
    modifies io.fsRegion, io.dirHandlesRegion, buffer
    ensures Spec.RemoveJudgment(Spec.ObservationContextFor(io), raw,path,top,Spec.RemovalScope(rootKey,rootDevice,seen),old(io.now()),old(io.trustedFilesystem()),
                                old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,failed,proof)
    ensures Spec.HostKeys(io.fs()) <= universe
    ensures io.dirHandles() == old(io.dirHandles())
    decreases universe - seen, 0
  {
    ghost var context := Spec.ObservationContextFor(io);
    assert Spec.Listed(context, io.fs(), path, listing);
    Facts.StatusKey(io.fs(),io.trustedFilesystem(),path,status);
    // Preserve the established query relation without expanding its resolver.
    hide C.GetFileTimesSpec;
    var key := HostInodeKey(status.v.device,status.v.inode);
    ghost var states: seq<FileSystem> := [io.fs()];
    ghost var outputs := [buffer.output];
    ghost var errors := [buffer.diagnostics];
    ghost var children: seq<Spec.Removal> := [];
    ghost var failures: seq<bool> := [];
    var anyFailure := false;
    var i := 0;
    // StatusKey and the empty child partition are established; subsequent
    // judgments come from the separately proved, terminating Remove contract.
    hide Spec.RemoveJudgment;
    hide BenchWorld.ValidInodeFileSystemData;
    hide C.ValidFilesystemObservation;
    while i < |listing.order|
      modifies io.fsRegion, io.dirHandlesRegion, buffer
      invariant 0 <= i <= |listing.order|
      invariant Spec.HostKeys(io.fs()) <= universe
      invariant io.dirHandles() == old(io.dirHandles())
      invariant Spec.ObservationContextFor(io) == context
      invariant |states| == i+1 && |outputs| == i+1 && |errors| == i+1
      invariant |children| == i && |failures| == i
      invariant states[0] == old(io.fs()) && states[i] == io.fs()
      invariant outputs[0] == old(buffer.output) && outputs[i] == buffer.output
      invariant errors[0] == old(buffer.diagnostics) && errors[i] == buffer.diagnostics
      invariant anyFailure == Spec.HasFailure(failures)
      invariant forall j: int :: 0 <= j < i ==>
                                   Spec.RemoveJudgment(context, raw,Spec.ChildPath(path,listing.order[j]),false,Spec.RemovalScope(rootKey,
                                                                                                                                  if top then status.v.device else rootDevice,seen + {key}),io.now(),io.trustedFilesystem(),
                                                       states[j],states[j+1],outputs[j],outputs[j+1],errors[j],errors[j+1],failures[j],children[j])
      decreases |listing.order|-i
    {
      var bad, child := Remove(raw,io,buffer,Spec.ChildPath(path,listing.order[i]),false,
                               rootKey,if top then status.v.device else rootDevice,seen + {key},universe);
      // The exact recursive judgment is established by the terminating call.
      hide *; reveal Spec.ObservationContextFor();
      Facts.AppendFailure(failures,bad);
      states := states + [io.fs()];
      outputs := outputs + [buffer.output];
      errors := errors + [buffer.diagnostics];
      children := children + [child];
      failures := failures + [bad];
      anyFailure := anyFailure || bad;
      i := i + 1;
    }
    // The loop has established every child judgment in the complete partition.
    hide Spec.RemoveJudgment;
    var ok := false;
    var err := 0;
    if listing.readError != 0 {
      var reason := io.GetCLocaleErrnoText(listing.readError);
      assert Spec.TraversalMessage(path,reason) == Spec.TraversalText(path,listing.readError);
      buffer.diagnostics := buffer.diagnostics + Text.TraversalMessage(path,reason);
      failed := true;
    } else if anyFailure { failed := true; }
    else { failed, ok, err := Excise(raw,io,buffer,path,true,0); }
    proof := Spec.Hierarchy(status,listing,children,states,outputs,errors,failures,ok,err);
    // Each child and the final native effect already establish their exact contracts.
    hide *; reveal Spec.ObservationContextFor();
    Facts.HierarchyJudgment(context, raw,path,top,rootKey,rootDevice,seen,io.now(),io.trustedFilesystem(),
                            old(io.fs()),io.fs(),old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,failed,
                            status,listing,children,states,outputs,errors,failures,ok,err);
    hide *; reveal Spec.ObservationContextFor();
  }

  twostate predicate CoreSummary(raw: Schema.RmCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion,
          io.nowRegion, io.trustedFilesystemRegion, io.trustedStreamsRegion, io.trustedNativeFailuresRegion
  { Spec.Spec(raw,io,exit) }

  method Prepare(raw: Schema.RmCmdRaw, io: BenchIO.IO, buffer: OutputBuffer) returns (exit: int)
    requires buffer.output == [] && buffer.diagnostics == []
    modifies io.fsRegion, io.dirHandlesRegion, buffer
    ensures Spec.Prepared(Spec.ObservationContextFor(io), raw,io.now(),io.trustedFilesystem(),old(io.fs()),io.fs(),buffer.output,buffer.diagnostics,exit)
    ensures io.dirHandles() == old(io.dirHandles())
  {
    // Keep recursive judgments folded until their local witness is ready.
    hide Spec.OperandsJudgment, Spec.RemoveJudgment, Spec.StatusResult;
    hide Spec.ListingObservation, Spec.ReadPrefix;
    hide C.ValidFilesystemObservation, BenchWorld.ValidInodeFileSystemData;
    ghost var context := Spec.ObservationContextFor(io);
    if raw.mode == Schema.ModeHelp {
      buffer.output := Spec.HelpTextSpec();
      exit := 0;
      return;
    }
    if raw.mode == Schema.ModeVersion {
      buffer.output := Spec.VersionTextSpec();
      exit := 0;
      return;
    }
    if raw.mode != Schema.ModeRun {
      var text := ModeErrorMessage(io,raw.mode);
      buffer.diagnostics := text;
      exit := 1;
      return;
    }
    if |raw.operands| == 0 {
      if !raw.force { buffer.diagnostics := Spec.MissingOperandText(); }
      exit := if raw.force then 0 else 1;
      return;
    }
    var root: IOResult<FileTimeStatus> := R.Ok(FileTimeStatus(0,0,0,0,false,false,0,0,0));
    if raw.recursive && raw.preserveRoot {
      root := InspectPath(io,"/");
      if root.Err? {
        var reason := io.GetCLocaleErrnoText(C.ResultErrno(root));
        buffer.diagnostics := Text.RootAttributesMessage(reason);
        exit := 1;
        return;
      }
    }
    // The optional root observation is established before the operand partition.
    hide C.GetFileTimesSpec;
    var rootKey := HostInodeKey(root.v.device,root.v.inode);
    ghost var universe := Spec.HostKeys(io.fs());
    ghost var states: seq<FileSystem> := [io.fs()];
    ghost var outputs := [buffer.output];
    ghost var errors := [buffer.diagnostics];
    ghost var proofs: seq<Spec.Removal> := [];
    ghost var failures: seq<bool> := [];
    var anyFailure := false;
    var i := 0;
    // The root query and empty operand partition are established before
    // composing exact Remove judgments with AppendOperandJudgment.
    hide Spec.RemoveJudgment;
    hide BenchWorld.ValidInodeFileSystemData;
    hide C.ValidFilesystemObservation;
    while i < |raw.operands|
      modifies io.fsRegion, io.dirHandlesRegion, buffer
      invariant 0 <= i <= |raw.operands|
      invariant Spec.HostKeys(io.fs()) <= universe
      invariant io.dirHandles() == old(io.dirHandles())
      invariant Spec.ObservationContextFor(io) == context
      invariant |states| == i+1 && |outputs| == i+1 && |errors| == i+1
      invariant |proofs| == i && |failures| == i
      invariant states[0] == old(io.fs()) && states[i] == io.fs()
      invariant outputs[0] == old(buffer.output) && outputs[i] == buffer.output
      invariant errors[0] == old(buffer.diagnostics) && errors[i] == buffer.diagnostics
      invariant anyFailure == Spec.HasFailure(failures)
      invariant forall j: int :: 0 <= j < i ==>
                                   Facts.OperandJudgment(context, raw,raw.operands[j],rootKey,io.now(),io.trustedFilesystem(),
                                                         states[j],states[j+1],outputs[j],outputs[j+1],errors[j],errors[j+1],failures[j],proofs[j])
      decreases |raw.operands|-i
    {
      var path := CommandPath(raw.operands[i]);
      var bad, proof := Remove(raw,io,buffer,path,true,rootKey,0,{},universe);
      Facts.NormalizedOperand(context, raw,raw.operands[i],path,rootKey,io.now(),io.trustedFilesystem(),
                              states[i],io.fs(),outputs[i],buffer.output,errors[i],buffer.diagnostics,bad,proof);
      // Preserve the established judgment while extending the operand partition.
      hide *; reveal Spec.ObservationContextFor();
      Facts.AppendOperandJudgment(context, raw,io.now(),io.trustedFilesystem(),rootKey,i,states,outputs,errors,
                                  failures,proofs,io.fs(),buffer.output,buffer.diagnostics,bad,proof);
      Facts.AppendFailure(failures,bad);
      states := states + [io.fs()];
      outputs := outputs + [buffer.output];
      errors := errors + [buffer.diagnostics];
      proofs := proofs + [proof];
      failures := failures + [bad];
      anyFailure := anyFailure || bad;
      i := i+1;
    }
    // The complete operand partition is now established by the loop.
    hide Spec.RemoveJudgment;
    exit := if anyFailure then 1 else 0;
    Facts.AssembleOperands(context, raw,io.now(),io.trustedFilesystem(),rootKey,old(io.fs()),io.fs(),
                           old(buffer.output),buffer.output,old(buffer.diagnostics),buffer.diagnostics,exit,states,outputs,errors,failures,proofs);
    // AssembleOperands has separately proved this exact existential judgment.
    hide *; reveal Spec.ObservationContextFor();
    Facts.AssemblePrepared(context, raw,io.now(),io.trustedFilesystem(),old(io.fs()),io.fs(),buffer.output,buffer.diagnostics,exit,root);
    hide *; reveal Spec.ObservationContextFor();
  }

  method Flush(output: Bytes, diagnostics: Bytes, removalExit: int, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.StreamResults(old(io.stdout()),io.stdout(),old(io.stderr()),io.stderr(),io.trustedStreams(),
                               output,diagnostics,removalExit,exit)
  {
    ghost var observations := io.trustedStreams();
    ghost var beforeOut, beforeErr := io.stdout(), io.stderr();
    var outResult := io.WriteStdout(output);
    var outErr := C.ResultErrno(outResult);
    ghost var outObservation := observations(StreamWriteStdout(beforeOut,output));
    assert outObservation.StreamWriteResult? && outObservation.err == outErr;
    var finalDiagnostic := diagnostics;
    if outErr != 0 {
      var reason := io.GetCLocaleErrnoText(outErr);
      finalDiagnostic := diagnostics + Text.WriteErrorText(reason);
    }
    assert finalDiagnostic == diagnostics + (if outObservation.err == 0 then []
                                             else Spec.WriteErrorText(C.CLocaleErrnoTextResult(outObservation.err)));
    var errResult := io.WriteStderr(finalDiagnostic);
    ghost var errObservation := observations(StreamWriteStderr(beforeErr,finalDiagnostic));
    assert errObservation.StreamWriteResult? && errObservation.err == C.ResultErrno(errResult);
    exit := if removalExit == 0 && outErr == 0 && C.ResultErrno(errResult) == 0 then 0 else 1;
  }

  method RunCore(raw: Schema.RmCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
    ensures Spec.Spec(raw,io,exit)
    ensures CoreSummary(raw,io,exit)
  {
    ghost var context := Spec.ObservationContextFor(io);
    var buffer := new OutputBuffer();
    var removalExit := Prepare(raw,io,buffer);
    exit := Flush(buffer.output,buffer.diagnostics,removalExit,io);
    assert Spec.ObservationContextFor(io) == context by { reveal Spec.ObservationContextFor(); }
    assert Spec.Spec(raw,io,exit) by {
      hide *; reveal Spec.ObservationContextFor();
      reveal Spec.Spec;
    }
    hide *; reveal Spec.ObservationContextFor();
    reveal CoreSummary;
  }
  function DotOperandCore(path: Path): bool
  {
    Spec.DotOperand(path)
  } by method {
    var stripped := RawPath.StripLeadingSlash(path);
    var parts := RawPath.SplitSegments(stripped, 0, 0);
    return |parts| > 0 && parts[|parts| - 1] in {".", ".."};
  }

  function BasicRefusalCore(raw: Schema.RmCmdRaw, path: Path, top: bool,
                            rootKey: HostInodeKey, rootDevice: int, seen: set<HostInodeKey>, status: FileTimeStatus): Spec.Refusal
  {
    Spec.BasicRefusal(raw, path, top, rootKey, rootDevice, seen, status)
  } by method {
    return if !raw.recursive && !raw.directory then Spec.DirectoryRefusal
      else if !raw.recursive then Spec.NoRefusal
      else if top && DotOperandCore(path) then Spec.DotRefusal
      else if top && raw.preserveRoot && HostInodeKey(status.device, status.inode) == rootKey then Spec.RootRefusal
      else if !top && raw.oneFileSystem && status.device != rootDevice then Spec.DeviceRefusal
      else if HostInodeKey(status.device, status.inode) in seen then Spec.CycleRefusal
      else Spec.NoRefusal;
  }

}
