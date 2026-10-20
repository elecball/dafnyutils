include "RmSpec.dfy"
include "../../core/PathCore.dfy"

module RmProof {
  import opened BenchWorld
  import Spec = RmSpec
  import C = IOContract
  import LookupProof = WorldLookupProof
  import Schema = RmSchema
  import Paths = MvPathSpec
  import PathCore = MvPathCore

  lemma TrimmedSummaryGivesStatusPath(path: Path, value: Path)
    requires PathCore.TrimmedSummary(path,value)
    ensures Spec.StatusPath(path,value)
  {
    if |path| == 0 {
    } else if Paths.SlashesOnly(path) {
    } else {
      var end :| 0 < end <= |path| && value == path[..end] && path[end-1] != '/' &&
        forall i :: end <= i < |path| ==> path[i] == '/';
      var trailing := path[end..];
      assert Paths.SlashesOnly(trailing);
      assert Paths.PathWithoutTrailingSlashes(path,value,trailing);
    }
  }

  lemma TrimmedSummaryGivesCommandPath(path: Path, trimmed: Path, value: Path)
    requires PathCore.TrimmedSummary(path,trimmed)
    requires value == (if |path| > 0 && path[|path|-1] == '/' && trimmed != "/"
      then trimmed + "/" else trimmed)
    ensures Spec.CommandPath(path,value)
  {
    if |path| == 0 {
    } else if Paths.SlashesOnly(path) {
    } else {
      var end :| 0 < end <= |path| && trimmed == path[..end] && path[end-1] != '/' &&
        forall i :: end <= i < |path| ==> path[i] == '/';
      var trailing := path[end..];
      assert Paths.SlashesOnly(trailing);
      assert Paths.PathWithoutTrailingSlashes(path,trimmed,trailing);
      assert (|trailing| > 0) == (path[|path|-1] == '/');
    }
  }

  lemma StatusKey(fs: FileSystem, trusted: C.ValidFilesystemObservations,
    path: Path, status: IOResult<FileTimeStatus>)
    requires Spec.StatusResult(fs,trusted,path,status)
    requires status.Ok?
    ensures HostInodeKey(status.v.device,status.v.inode) in Spec.HostKeys(fs)
  {
  }

  lemma RemovalKeys(before: FileSystem, after: FileSystem, path: Path, directory: bool,
    now: int, trusted: C.ValidFilesystemObservations, ok: bool, err: int)
    requires (if directory then C.RemoveDirectorySpec(before,now,trusted,after,path,ok,err)
      else C.UnlinkPathSpec(before,now,trusted,after,path,ok,err)) == true
    ensures Spec.HostKeys(after) <= Spec.HostKeys(before)
  {
    assert (if ok then C.EntryRemovalEffectFields(before,path,directory,after)
      else C.FailedFilesystemEffectFields(before,after)) by {
      hide *;
      reveal C.RemoveDirectorySpec;
      reveal C.UnlinkPathSpec;
      reveal C.TrustedFilesystemEffectContractFields;
      reveal C.ValidFilesystemObservation;
    }
    hide *;
    reveal C.EntryRemovalEffectFields;
    reveal C.FailedFilesystemEffectFields;
    reveal C.TraversalRecordEffectFields;
    reveal C.ParentDirectoryEffectFields;
    reveal Spec.HostKeys;
    assert after.inodes.Keys <= before.inodes.Keys;
    forall id | id in after.inodes
      ensures after.inodes[id].hostKey == before.inodes[id].hostKey
    {
    }
    forall key | key in Spec.HostKeys(after)
      ensures key in Spec.HostKeys(before)
    {
      var id :| id in after.inodes && after.inodes[id].hostKey == key;
    }
  }

  lemma EntryNamesUnique(fs: FileSystem, path: Path)
    requires FsContainsPath(fs,path)
    ensures forall a,b :: (a in C.DirectoryEntriesForPathFields(fs,path) &&
      b in C.DirectoryEntriesForPathFields(fs,path) && a.name == b.name) ==> a == b
  {
    var tree := InodeFsLookupTreeSegments(fs.inodes,fs.namespace,PathSegments(path)).v;
    LookupProof.InodeLookupTreeWellFormed(fs.inodes,fs.namespace,PathSegments(path),tree);
    forall a,b | a in C.DirectoryEntriesForPathFields(fs,path) &&
      b in C.DirectoryEntriesForPathFields(fs,path) && a.name == b.name
      ensures a == b
    {
      var na :| na in tree.children && C.ValidLeafName(na) &&
        a == C.EntryForNode(na,C.InodeTreeChildNodeFields(fs,tree,na));
      var nb :| nb in tree.children && C.ValidLeafName(nb) &&
        b == C.EntryForNode(nb,C.InodeTreeChildNodeFields(fs,tree,nb));
      EntryForNodeName(na,C.InodeTreeChildNodeFields(fs,tree,na));
      EntryForNodeName(nb,C.InodeTreeChildNodeFields(fs,tree,nb));
    }
  }
  lemma AppendDirectoryName(names: seq<string>, seen: set<DirEntry>, entry: DirEntry)
    requires Spec.Names(names) == Spec.EntryNames(seen)
    requires |Spec.Names(names)| == |names|
    requires entry.name !in Spec.Names(names)
    ensures Spec.Names(names + [entry.name]) == Spec.EntryNames(seen + {entry})
    ensures |Spec.Names(names + [entry.name])| == |names + [entry.name]|
  {
    hide *;
    reveal Spec.Names;
    reveal Spec.EntryNames;
    forall name | name in Spec.Names(names + [entry.name])
      ensures name in Spec.Names(names) + {entry.name}
    {
      var j :| 0 <= j < |names|+1 && (names+[entry.name])[j] == name;
      if j < |names| {
        assert names[j] == name;
      } else {
        assert j == |names|;
      }
    }
    forall name | name in Spec.Names(names) + {entry.name}
      ensures name in Spec.Names(names + [entry.name])
    {
      if name == entry.name {
        assert (names+[entry.name])[|names|] == name;
      } else {
        var j :| 0 <= j < |names| && names[j] == name;
        assert (names+[entry.name])[j] == name;
      }
    }
    assert Spec.Names(names + [entry.name]) == Spec.Names(names) + {entry.name};
    assert Spec.EntryNames(seen + {entry}) == Spec.EntryNames(seen) + {entry.name};
  }

  lemma EntryForNodeName(name: string, node: FsNode)
    requires C.ValidLeafName(name)
    ensures C.EntryForNode(name,node).name == name
  {
    assert LeafName(name) == name;
  }

  lemma AppendReadPrefix(context: Spec.ObservationContext, fs: FileSystem,
    handle: int, initialHandles: map<int, DirHandleState>,
    names: seq<string>, steps: seq<Spec.DirectoryObservation>,
    before: map<int, DirHandleState>, after: map<int, DirHandleState>, name: string, kind: DirectoryEntryKind)
    requires Spec.ReadPrefix(fs, context, handle, initialHandles, names, steps, before)
    requires C.ReadDirSpec(fs, before, context.failures, after, handle, true, name, kind, 0)
    ensures Spec.ReadPrefix(fs, context, handle, initialHandles,
      names + [name], steps + [Spec.DirectoryObservation(before, after, true, name, kind, 0)], after)
  {
    hide *;
    reveal Spec.ReadPrefix();
    var next := steps + [Spec.DirectoryObservation(before, after, true, name, kind, 0)];
    forall i: nat | i < |next|
      ensures C.ReadDirSpec(fs, next[i].before, context.failures, next[i].after,
        handle, next[i].more, next[i].name, next[i].kind, next[i].err) &&
        next[i].more && next[i].err == 0 && next[i].name == (names + [name])[i] &&
        (i > 0 ==> next[i-1].after == next[i].before)
    {
      if i < |steps| {
        assert next[i] == steps[i];
        if i > 0 { assert next[i-1] == steps[i-1]; }
      } else {
        assert i == |steps|;
        if i > 0 { assert next[i-1] == steps[|steps|-1]; }
      }
    }
  }

  lemma ListingOpenFailureWitness(context: Spec.ObservationContext, fs: FileSystem,
    path: Path, listing: Spec.Listing, afterOpen: map<int, DirHandleState>)
    requires listing.openError != 0
    requires C.OpenDirSpec(fs, context.handles, context.failures, afterOpen,
      path, false, false, 0, listing.openError)
    ensures Spec.ListingObservation(fs, context, path, listing)
  {
    hide *;
    reveal Spec.ListingObservation();
  }

  lemma ListingReadWitness(context: Spec.ObservationContext, fs: FileSystem,
    path: Path, listing: Spec.Listing, afterOpen: map<int, DirHandleState>, handle: int,
    steps: seq<Spec.DirectoryObservation>, beforeEnd: map<int, DirHandleState>,
    afterEnd: map<int, DirHandleState>, endKind: DirectoryEntryKind,
    closeOk: bool, closeErr: int)
    requires listing.openError == 0
    requires C.OpenDirSpec(fs, context.handles, context.failures, afterOpen, path, false, true, handle, 0)
    requires Spec.ReadPrefix(fs, context, handle, afterOpen, listing.order, steps, beforeEnd)
    requires C.ReadDirSpec(fs, beforeEnd, context.failures, afterEnd,
      handle, false, "", endKind, listing.readError)
    requires C.CloseDirSpec(afterEnd, context.failures, context.handles, handle, closeOk, closeErr)
    ensures Spec.ListingObservation(fs, context, path, listing)
  {
    hide *;
    reveal Spec.ListingObservation();
  }

  lemma AtomicJudgment(context: Spec.ObservationContext, raw: Schema.RmCmdRaw, path: Path, top: bool,
    rootKey: HostInodeKey, rootDevice: int, seen: set<HostInodeKey>, now: int,
    trusted: C.ValidFilesystemObservations, before: FileSystem, after: FileSystem,
    out0: Bytes, out1: Bytes, err0: Bytes, err1: Bytes, failed: bool,
    status: IOResult<FileTimeStatus>, directory: bool, listing: Spec.Listing, ok: bool, err: int)
    requires Spec.StatusResult(before,trusted,path,status)
    requires if directory then
      status.Ok? && status.v.isDir &&
      Spec.BasicRefusal(raw,path,top,rootKey,rootDevice,seen,status.v) == Spec.NoRefusal &&
      Spec.ParentAllowed(raw,path,top,status.v,before,trusted) &&
      (!raw.recursive || (Spec.Listed(context, before,path,listing) &&
        (listing.openError != 0 || (listing.readError != 0 && listing.order == []))))
      else status.Err? || !status.v.isDir
    requires Spec.Attempt(raw,path,directory,now,trusted,before,after,out0,out1,err0,err1,ok,err,
      if raw.recursive && directory then
        (if listing.openError != 0 then listing.openError else listing.readError) else 0,failed) == true
    ensures Spec.RemoveJudgment(context, raw,path,top,Spec.RemovalScope(rootKey,rootDevice,seen),now,trusted,before,after,
      out0,out1,err0,err1,failed,Spec.Atomic(status,directory,listing,ok,err))
  {
    hide *;
    reveal Spec.RemoveJudgment;
  }

  lemma RefusedJudgment(context: Spec.ObservationContext, raw: Schema.RmCmdRaw, path: Path, top: bool,
    rootKey: HostInodeKey, rootDevice: int, seen: set<HostInodeKey>, now: int,
    trusted: C.ValidFilesystemObservations, before: FileSystem, after: FileSystem,
    out0: Bytes, out1: Bytes, err0: Bytes, err1: Bytes, failed: bool,
    status: IOResult<FileTimeStatus>, why: Spec.Refusal, parent: IOResult<FileTimeStatus>)
    requires Spec.StatusResult(before,trusted,path,status)
    requires status.Ok? && status.v.isDir && why != Spec.NoRefusal
    requires why == Spec.BasicRefusal(raw,path,top,rootKey,rootDevice,seen,status.v) ||
      (Spec.BasicRefusal(raw,path,top,rootKey,rootDevice,seen,status.v) == Spec.NoRefusal &&
       raw.recursive && raw.preserveAll && top &&
       Spec.StatusResult(before,trusted,Spec.ChildPath(path,".."),parent) &&
       (if parent.Err? then why == Spec.ParentRefusal
        else parent.v.device != status.v.device && why == Spec.PreserveDeviceRefusal))
    requires after == before && out1 == out0 && err1 == err0 + Spec.RefusalText(path,why) && failed
    ensures Spec.RemoveJudgment(context, raw,path,top,Spec.RemovalScope(rootKey,rootDevice,seen),now,trusted,before,after,
      out0,out1,err0,err1,failed,Spec.Refused(status,why,parent))
  {
    hide *;
    reveal Spec.RemoveJudgment;
  }

  lemma HierarchyJudgment(context: Spec.ObservationContext, raw: Schema.RmCmdRaw, path: Path, top: bool,
    rootKey: HostInodeKey, rootDevice: int, seen: set<HostInodeKey>, now: int,
    trusted: C.ValidFilesystemObservations, before: FileSystem, after: FileSystem,
    out0: Bytes, out1: Bytes, err0: Bytes, err1: Bytes, failed: bool,
    status: IOResult<FileTimeStatus>, listing: Spec.Listing, children: seq<Spec.Removal>,
    states: seq<FileSystem>, outputs: seq<Bytes>, errors: seq<Bytes>, failures: seq<bool>, ok: bool, err: int)
    requires Spec.StatusResult(before,trusted,path,status)
    requires status.Ok? && status.v.isDir && raw.recursive
    requires Spec.BasicRefusal(raw,path,top,rootKey,rootDevice,seen,status.v) == Spec.NoRefusal
    requires Spec.ParentAllowed(raw,path,top,status.v,before,trusted)
    requires Spec.Listed(context, before,path,listing) && listing.openError == 0
    requires listing.readError == 0 || |listing.order| > 0
    requires |children| == |listing.order| && |failures| == |listing.order|
    requires |states| == |listing.order|+1 && |outputs| == |listing.order|+1 && |errors| == |listing.order|+1
    requires states[0] == before && outputs[0] == out0 && errors[0] == err0
    requires forall i: int :: 0 <= i < |listing.order| ==>
      Spec.RemoveJudgment(context, raw,Spec.ChildPath(path,listing.order[i]),false,Spec.RemovalScope(rootKey,
        if top then status.v.device else rootDevice,
        seen + {HostInodeKey(status.v.device,status.v.inode)}),now,trusted,
        states[i],states[i+1],outputs[i],outputs[i+1],errors[i],errors[i+1],failures[i],children[i])
    requires if listing.readError != 0 then
      after == states[|listing.order|] && out1 == outputs[|listing.order|] &&
      err1 == errors[|listing.order|] + Spec.TraversalText(path,listing.readError) && failed
      else if Spec.HasFailure(failures) then
        after == states[|listing.order|] && out1 == outputs[|listing.order|] && err1 == errors[|listing.order|] && failed
      else Spec.Attempt(raw,path,true,now,trusted,states[|listing.order|],after,
        outputs[|listing.order|],out1,errors[|listing.order|],err1,ok,err,0,failed)
    ensures Spec.RemoveJudgment(context, raw,path,top,Spec.RemovalScope(rootKey,rootDevice,seen),now,trusted,before,after,
      out0,out1,err0,err1,failed,Spec.Hierarchy(status,listing,children,states,outputs,errors,failures,ok,err))
  {
    hide *;
    reveal Spec.RemoveJudgment;
  }

  lemma AppendFailure(failures: seq<bool>, failed: bool)
    ensures Spec.HasFailure(failures + [failed]) == (Spec.HasFailure(failures) || failed)
  {
    hide *;
    reveal Spec.HasFailure;
    if Spec.HasFailure(failures+[failed]) {
      var j :| 0 <= j < |failures|+1 && (failures+[failed])[j];
      if j < |failures| {
        assert failures[j];
      } else {
        assert j == |failures| && failed;
      }
    }
    if Spec.HasFailure(failures) {
      var j :| 0 <= j < |failures| && failures[j];
      assert (failures+[failed])[j];
    }
    if failed {
      assert (failures+[failed])[|failures|];
    }
  }

  ghost predicate OperandJudgment(context: Spec.ObservationContext, raw: Schema.RmCmdRaw, operand: Path, rootKey: HostInodeKey,
    now: int, trusted: C.ValidFilesystemObservations, before: FileSystem, after: FileSystem,
    out0: Bytes, out1: Bytes, err0: Bytes, err1: Bytes, failed: bool, proof: Spec.Removal)
  {
    exists path: Path :: Spec.CommandPath(operand,path) &&
      Spec.RemoveJudgment(context, raw,path,true,Spec.RemovalScope(rootKey,0,{}),now,trusted,
        before,after,out0,out1,err0,err1,failed,proof)
  }

  lemma NormalizedOperand(context: Spec.ObservationContext, raw: Schema.RmCmdRaw, operand: Path, path: Path, rootKey: HostInodeKey,
    now: int, trusted: C.ValidFilesystemObservations, before: FileSystem, after: FileSystem,
    out0: Bytes, out1: Bytes, err0: Bytes, err1: Bytes, failed: bool, proof: Spec.Removal)
    requires Spec.CommandPath(operand,path)
    requires Spec.RemoveJudgment(context, raw,path,true,Spec.RemovalScope(rootKey,0,{}),now,trusted,
      before,after,out0,out1,err0,err1,failed,proof) == true
    ensures OperandJudgment(context, raw,operand,rootKey,now,trusted,before,after,out0,out1,err0,err1,failed,proof)
  {
    hide *;
    reveal OperandJudgment;
  }

  lemma AppendOperandJudgment(context: Spec.ObservationContext, raw: Schema.RmCmdRaw, now: int, trusted: C.ValidFilesystemObservations,
    rootKey: HostInodeKey, i: int, states: seq<FileSystem>, outputs: seq<Bytes>, errors: seq<Bytes>,
    failures: seq<bool>, proofs: seq<Spec.Removal>, after: FileSystem, output: Bytes, diagnostics: Bytes,
    failed: bool, proof: Spec.Removal)
    requires 0 <= i < |raw.operands|
    requires |states| == i+1 && |outputs| == i+1 && |errors| == i+1
    requires |failures| == i && |proofs| == i
    requires forall j: int :: 0 <= j < i ==>
      OperandJudgment(context, raw,raw.operands[j],rootKey,now,trusted,
        states[j],states[j+1],outputs[j],outputs[j+1],errors[j],errors[j+1],failures[j],proofs[j])
    requires OperandJudgment(context, raw,raw.operands[i],rootKey,now,trusted,
      states[i],after,outputs[i],output,errors[i],diagnostics,failed,proof) == true
    ensures forall j: int :: 0 <= j < i+1 ==>
      OperandJudgment(context, raw,raw.operands[j],rootKey,now,trusted,
        (states+[after])[j],(states+[after])[j+1],(outputs+[output])[j],(outputs+[output])[j+1],
        (errors+[diagnostics])[j],(errors+[diagnostics])[j+1],(failures+[failed])[j],(proofs+[proof])[j])
  {
    // Both the existing partition and its new final judgment are exact premises.
    hide *;
    forall j | 0 <= j < i+1
      ensures OperandJudgment(context, raw,raw.operands[j],rootKey,now,trusted,
        (states+[after])[j],(states+[after])[j+1],(outputs+[output])[j],(outputs+[output])[j+1],
        (errors+[diagnostics])[j],(errors+[diagnostics])[j+1],(failures+[failed])[j],(proofs+[proof])[j])
    {
      if j < i {
      } else {
        assert j == i;
      }
    }
  }

  lemma AssembleOperands(context: Spec.ObservationContext, raw: Schema.RmCmdRaw, now: int, trusted: C.ValidFilesystemObservations,
    rootKey: HostInodeKey, before: FileSystem, after: FileSystem,
    out0: Bytes, out1: Bytes, err0: Bytes, err1: Bytes, exit: int,
    states: seq<FileSystem>, outputs: seq<Bytes>, errors: seq<Bytes>, failures: seq<bool>, proofs: seq<Spec.Removal>)
    requires |states| == |raw.operands|+1 && |outputs| == |raw.operands|+1 && |errors| == |raw.operands|+1
    requires |failures| == |raw.operands| && |proofs| == |raw.operands|
    requires states[0] == before && states[|raw.operands|] == after
    requires outputs[0] == out0 && outputs[|raw.operands|] == out1
    requires errors[0] == err0 && errors[|raw.operands|] == err1
    requires forall i: int :: 0 <= i < |raw.operands| ==>
      OperandJudgment(context, raw,raw.operands[i],rootKey,now,trusted,
        states[i],states[i+1],outputs[i],outputs[i+1],errors[i],errors[i+1],failures[i],proofs[i])
    requires exit == (if Spec.HasFailure(failures) then 1 else 0)
    ensures Spec.OperandsJudgment(context, raw,now,trusted,rootKey,before,after,out0,out1,err0,err1,exit)
  {
    forall i | 0 <= i < |raw.operands|
      ensures exists path: Path ::
        Spec.CommandPath(raw.operands[i],path) &&
        Spec.RemoveJudgment(context, raw,path,true,Spec.RemovalScope(rootKey,0,{}),now,trusted,
          states[i],states[i+1],outputs[i],outputs[i+1],errors[i],errors[i+1],failures[i],proofs[i])
    {
      assert OperandJudgment(context, raw,raw.operands[i],rootKey,now,trusted,
        states[i],states[i+1],outputs[i],outputs[i+1],errors[i],errors[i+1],failures[i],proofs[i]);
    }
  }

  lemma AssemblePrepared(context: Spec.ObservationContext, raw: Schema.RmCmdRaw, now: int, trusted: C.ValidFilesystemObservations,
    before: FileSystem, after: FileSystem, output: Bytes, diagnostics: Bytes, exit: int,
    root: IOResult<FileTimeStatus>)
    requires raw.mode == Schema.ModeRun && |raw.operands| > 0 && root.Ok?
    requires (raw.recursive && raw.preserveRoot) ==> Spec.StatusResult(before,trusted,"/",root)
    requires !(raw.recursive && raw.preserveRoot) ==> root.v.device == 0 && root.v.inode == 0
    requires Spec.OperandsJudgment(context, raw,now,trusted,HostInodeKey(root.v.device,root.v.inode),
      before,after,[],output,[],diagnostics,exit)
    ensures Spec.Prepared(context, raw,now,trusted,before,after,output,diagnostics,exit)
  {}

}
