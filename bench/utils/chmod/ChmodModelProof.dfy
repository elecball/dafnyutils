include "../../core/IOContract.dfy"
include "ChmodWorldLookupProof.dfy"

module ChmodModelProof {
  import Result = Results
  import opened BenchWorld
  import opened C = IOContract
  import LookupProof = ChmodWorldLookupProof

  lemma InodeTopologyLookupTreeFields(
    before: FileSystem,
    after: FileSystem,
    tree: InodeTree,
    segs: seq<string>
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    ensures InodeFsLookupTreeSegments(
              before.inodes, tree, segs
            ) == InodeFsLookupTreeSegments(after.inodes, tree, segs)
    decreases |segs|
  {
    reveal FileSystemTopologyUnchangedExceptMode();
    if tree.id in before.inodes && |segs| > 0 {
      assert tree.id in after.inodes;
      assert NodeShapeUnchangedExceptMode(
          before.inodes[tree.id].node,
          after.inodes[tree.id].node
        );
      match (
          before.inodes[tree.id].node,
          after.inodes[tree.id].node
        )
      case (Directory(_, _, _), Directory(_, _, _)) =>
        if segs[0] in tree.children {
          InodeTopologyLookupTreeFields(
            before, after, tree.children[segs[0]], segs[1..]
          );
        }
      case (Regular(_, _, _, _), Regular(_, _, _, _)) =>
      case (Symlink(_, _, _, _), Symlink(_, _, _, _)) =>
      case (Inaccessible(_), Inaccessible(_)) =>
      case _ =>
        assert false by {
          reveal NodeShapeUnchangedExceptMode();
        }
    }
  }

  lemma FileSystemTopologyLookupSegmentsFields(
    before: FileSystem,
    after: FileSystem,
    segs: seq<string>
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    ensures FsLookupSegments(before, segs) ==
            FsLookupSegments(after, segs)
  {
    reveal FileSystemTopologyUnchangedExceptMode();
    assert before.namespace == after.namespace;
    InodeTopologyLookupTreeFields(
      before, after, before.namespace, segs
    );
  }

  lemma FileSystemTopologyPathFields(
    before: FileSystem,
    after: FileSystem,
    path: Path
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    ensures FsContainsPath(before, path) == FsContainsPath(after, path)
    ensures FsContainsPath(before, path) ==>
              NodeShapeUnchangedExceptMode(
                FsNodeAt(before, path), FsNodeAt(after, path)
              )
  {
    FileSystemTopologyLookupSegmentsFields(
      before, after, PathSegments(path)
    );
    reveal FsContainsPath(), FsLookupNode(), FsNodeAt();
    reveal InodeFsContainsPath(), InodeFsLookupNode(),
           InodeFsLookupId(), FsLookupSegments();
    if FsContainsPath(before, path) {
      var id := InodeFsLookupId(before, path).v;
      reveal FileSystemTopologyUnchangedExceptMode();
      assert id in before.inodes;
      assert id in after.inodes;
    }
  }

  lemma DirectNoFollowResultEqualExceptModeFields(
    before: FileSystem,
    after: FileSystem,
    path: Path
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    ensures DirectNoFollowResultFields(before, path) ==
            DirectNoFollowResultFields(after, path)
    ensures TerminalNoFollowResultFields(before, path) ==
            TerminalNoFollowResultFields(after, path)
  {
    FileSystemTopologyPathFields(before, after, path);
    FileSystemTopologyLookupSegmentsFields(
      before,
      after,
      PathSegments(path)
    );
    reveal DirectNoFollowResultFields(), TerminalNoFollowResultFields();
    reveal FsLookupNode(), InodeFsLookupNode(), InodeFsLookupId();
    if FsContainsPath(before, path) {
      reveal FileSystemTopologyUnchangedExceptMode();
      reveal NodeShapeUnchangedExceptMode();
    }
  }

  lemma DirectNoFollowSuccessContainsFields(fs: FileSystem, path: Path)
    requires DirectNoFollowResultFields(fs, path).Ok?
    ensures FsContainsPath(fs, path)
  {
    reveal DirectNoFollowResultFields();
    reveal FsLookupNode(), FsContainsPath();
    reveal InodeFsLookupNode(), InodeFsContainsPath();
  }

  lemma TerminalNoFollowSuccessContainsFields(fs: FileSystem, path: Path)
    requires TerminalNoFollowResultFields(fs, path).Ok?
    ensures FsContainsPath(fs, path)
  {
    reveal TerminalNoFollowResultFields();
    if path != "" {
      DirectNoFollowSuccessContainsFields(fs, path);
    } else {
      reveal FsLookupNode(), FsContainsPath();
      reveal InodeFsLookupNode(), InodeFsContainsPath();
    }
  }

  lemma ResolveRawNextSymlinkStepFields(
    fs: FileSystem, segs: seq<string>, i: nat, current: Path,
    seen: set<Path>, fuel: nat, followTerminalSymlink: bool,
    requireDirectory: bool, link: Path, target: Path
  )
    requires i < |segs|
    requires segs[i] != "." && segs[i] != ".."
    requires fuel > 0 && link != ""
    requires FsContainsPath(fs, AppendPath(current, segs[i]))
    requires FsNodeAt(fs, AppendPath(current, segs[i])).Symlink?
    requires FsNodeAt(fs, AppendPath(current, segs[i])).target == link
    requires DirectNoFollowResultFields(fs, AppendPath(current, segs[i])).Ok?
    requires i + 1 < |segs| || followTerminalSymlink || requireDirectory
    requires ResolveRawSymlinkSegmentsFields(
               fs, segs, i, current, seen, fuel, followTerminalSymlink, false,
               requireDirectory) == Result.Ok(target)
    ensures ResolveRawSymlinkSegmentsFields(
              fs, RawPathSegmentsFields(link) + segs[i + 1..], 0,
              if IsAbsolutePath(link) then "/" else ParentPath(AppendPath(current, segs[i])),
              seen + {AppendPath(current, segs[i])}, fuel - 1, followTerminalSymlink, false,
              requireDirectory || (i + 1 == |segs| && HasTrailingSlash(link))) == Result.Ok(target)
  {
    reveal ResolveRawSymlinkSegmentsFields();
  }

  lemma ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
    before: FileSystem,
    after: FileSystem,
    segs: seq<string>,
    i: nat,
    current: Path,
    seen: set<Path>,
    fuel: nat,
    followTerminalSymlink: bool,
    requireDirectory: bool,
    beforeTarget: Path,
    afterTarget: Path
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    requires i <= |segs|
    requires ResolveRawSymlinkSegmentsFields(
               before, segs, i, current, seen, fuel,
               followTerminalSymlink, false, requireDirectory
             ) == Result.Ok(beforeTarget)
    requires ResolveRawSymlinkSegmentsFields(
               after, segs, i, current, seen, fuel,
               followTerminalSymlink, false, requireDirectory
             ) == Result.Ok(afterTarget)
    ensures beforeTarget == afterTarget
    decreases fuel, |segs| - i
  {
    reveal ResolveRawSymlinkSegmentsFields();
    if i == |segs| {
      DirectNoFollowResultEqualExceptModeFields(before, after, current);
      assert TerminalNoFollowResultFields(before, current).Ok?;
      assert TerminalNoFollowResultFields(after, current).Ok?;
      TerminalNoFollowSuccessContainsFields(before, current);
      TerminalNoFollowSuccessContainsFields(after, current);
      FileSystemTopologyPathFields(before, after, current);
      match (FsNodeAt(before, current), FsNodeAt(after, current))
      case (Regular(_, _, _, _), Regular(_, _, _, _)) =>
      case (Directory(_, _, _), Directory(_, _, _)) =>
      case (Inaccessible(_), Inaccessible(_)) =>
      case (Symlink(beforeLink, _, _, _), Symlink(afterLink, _, _, _)) =>
        assert beforeLink == afterLink by {
          reveal NodeShapeUnchangedExceptMode();
        }
        if followTerminalSymlink || requireDirectory {
          assert beforeLink != "";
          assert fuel > 0;
          ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
            before,
            after,
            RawPathSegmentsFields(beforeLink),
            0,
            if IsAbsolutePath(beforeLink) then "/" else ParentPath(current),
            seen + {current},
            fuel - 1,
            followTerminalSymlink,
            requireDirectory || HasTrailingSlash(beforeLink),
            beforeTarget,
            afterTarget
          );
        }
      case _ =>
        assert false by {
          reveal NodeShapeUnchangedExceptMode();
        }
    } else if segs[i] == "." || segs[i] == ".." {
      DirectNoFollowResultEqualExceptModeFields(before, after, current);
      assert TerminalNoFollowResultFields(before, current).Ok?;
      assert TerminalNoFollowResultFields(after, current).Ok?;
      TerminalNoFollowSuccessContainsFields(before, current);
      TerminalNoFollowSuccessContainsFields(after, current);
      FileSystemTopologyPathFields(before, after, current);
      match (FsNodeAt(before, current), FsNodeAt(after, current))
      case (Regular(_, _, _, _), Regular(_, _, _, _)) =>
      case (Directory(_, _, _), Directory(_, _, _)) =>
        ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
          before,
          after,
          segs,
          i + 1,
          if segs[i] == ".." then ParentPath(current) else current,
          seen,
          fuel,
          followTerminalSymlink,
          requireDirectory,
          beforeTarget,
          afterTarget
        );
      case (Inaccessible(_), Inaccessible(_)) =>
      case (Symlink(beforeLink, _, _, _), Symlink(afterLink, _, _, _)) =>
        assert beforeLink == afterLink by {
          reveal NodeShapeUnchangedExceptMode();
        }
        assert beforeLink != "";
        assert fuel > 0;
        ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
          before,
          after,
          RawPathSegmentsFields(beforeLink) + segs[i..],
          0,
          if IsAbsolutePath(beforeLink) then "/" else ParentPath(current),
          seen + {current},
          fuel - 1,
          followTerminalSymlink,
          requireDirectory,
          beforeTarget,
          afterTarget
        );
      case _ =>
        assert false by {
          reveal NodeShapeUnchangedExceptMode();
        }
    } else {
      var next := AppendPath(current, segs[i]);
      DirectNoFollowResultEqualExceptModeFields(before, after, next);
      assert DirectNoFollowResultFields(before, next).Ok?;
      assert DirectNoFollowResultFields(after, next).Ok?;
      DirectNoFollowSuccessContainsFields(before, next);
      DirectNoFollowSuccessContainsFields(after, next);
      FileSystemTopologyPathFields(before, after, next);
      match (FsNodeAt(before, next), FsNodeAt(after, next))
      case (Regular(_, _, _, _), Regular(_, _, _, _)) =>
      case (Directory(_, _, _), Directory(_, _, _)) =>
        ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
          before,
          after,
          segs,
          i + 1,
          next,
          seen,
          fuel,
          followTerminalSymlink,
          requireDirectory,
          beforeTarget,
          afterTarget
        );
      case (Inaccessible(_), Inaccessible(_)) =>
      case (Symlink(beforeLink, _, _, _), Symlink(afterLink, _, _, _)) =>
        assert beforeLink == afterLink by {
          reveal NodeShapeUnchangedExceptMode();
        }
        if i + 1 < |segs| || followTerminalSymlink || requireDirectory {
          assert beforeLink != "";
          assert fuel > 0;
          var remaining := segs[i + 1..];
          ResolveRawNextSymlinkStepFields(
            before, segs, i, current, seen, fuel,
            followTerminalSymlink, requireDirectory, beforeLink, beforeTarget);
          ResolveRawNextSymlinkStepFields(
            after, segs, i, current, seen, fuel,
            followTerminalSymlink, requireDirectory, beforeLink, afterTarget);
          var restarted := RawPathSegmentsFields(beforeLink) + remaining;
          var restartCurrent := if IsAbsolutePath(beforeLink) then "/" else ParentPath(next);
          var restartDirectory := requireDirectory ||
                                  (|remaining| == 0 && HasTrailingSlash(beforeLink));
          assert (|remaining| == 0) == (i + 1 == |segs|);
          hide *;
          assert ResolveRawSymlinkSegmentsFields(
              before, restarted, 0, restartCurrent, seen + {next}, fuel - 1,
              followTerminalSymlink, false, restartDirectory) == Result.Ok(beforeTarget);
          assert ResolveRawSymlinkSegmentsFields(
              after, restarted, 0, restartCurrent, seen + {next}, fuel - 1,
              followTerminalSymlink, false, restartDirectory) == Result.Ok(afterTarget);
          ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
            before,
            after,
            restarted,
            0,
            restartCurrent,
            seen + {next},
            fuel - 1,
            followTerminalSymlink,
            restartDirectory,
            beforeTarget,
            afterTarget
          );
        }
      case _ =>
        assert false by {
          reveal NodeShapeUnchangedExceptMode();
        }
    }
  }

  lemma ResolvePathForMetadataSuccessfulTargetsEqualExceptModeFields(
    before: FileSystem,
    after: FileSystem,
    path: Path,
    follow: bool,
    beforeTarget: Path,
    afterTarget: Path
  )
    requires FileSystemTopologyUnchangedExceptMode(before, after)
    requires ResolvePathForMetadataFields(before, path, follow) ==
             Result.Ok(beforeTarget)
    requires ResolvePathForMetadataFields(after, path, follow) ==
             Result.Ok(afterTarget)
    ensures beforeTarget == afterTarget
  {
    assert path != "";
    assert ResolvePathThroughSymlinkComponentsFields(
        before, path, follow
      ) == Result.Ok(beforeTarget) by {
      reveal ResolvePathForMetadataFields();
    }
    assert ResolvePathThroughSymlinkComponentsFields(
        after, path, follow
      ) == Result.Ok(afterTarget) by {
      reveal ResolvePathForMetadataFields();
    }
    assert SYMLINK_MAX_DEPTH > 0 by {
      reveal SYMLINK_MAX_DEPTH;
    }
    assert ResolveRawSymlinkSegmentsFields(
        before,
        RawPathSegmentsFields(path),
        0,
        if IsAbsolutePath(path) then "/" else "",
        {},
        SYMLINK_MAX_DEPTH,
        follow,
        false,
        HasTrailingSlash(path)
      ) == Result.Ok(beforeTarget) by {
      reveal ResolvePathThroughSymlinkComponentsFields();
      reveal ResolvePathThroughSymlinkComponentsWithVisitedFields();
    }
    assert ResolveRawSymlinkSegmentsFields(
        after,
        RawPathSegmentsFields(path),
        0,
        if IsAbsolutePath(path) then "/" else "",
        {},
        SYMLINK_MAX_DEPTH,
        follow,
        false,
        HasTrailingSlash(path)
      ) == Result.Ok(afterTarget) by {
      reveal ResolvePathThroughSymlinkComponentsFields();
      reveal ResolvePathThroughSymlinkComponentsWithVisitedFields();
    }
    ResolveRawSuccessfulTargetsEqualExceptModeFieldsInternal(
      before,
      after,
      RawPathSegmentsFields(path),
      0,
      if IsAbsolutePath(path) then "/" else "",
      {},
      SYMLINK_MAX_DEPTH,
      follow,
      HasTrailingSlash(path),
      beforeTarget,
      afterTarget
    );
  }

  lemma SplitOffset(prefix: string, suffix: string, i: nat, start: nat)
    requires start <= i <= |suffix|
    ensures SplitSegments(prefix+suffix,|prefix|+i,|prefix|+start) ==
            SplitSegments(suffix,i,start)
    decreases |suffix|-i
  {
    assert (prefix+suffix)[|prefix|+start..|prefix|+i] == suffix[start..i];
    assert (prefix+suffix)[|prefix|+start..] == suffix[start..];
    if i < |suffix| {
      assert (prefix+suffix)[|prefix|+i] == suffix[i];
      if suffix[i] == '/' {
        SplitOffset(prefix,suffix,i+1,i+1);
      } else {
        SplitOffset(prefix,suffix,i+1,start);
      }
    }
  }

  lemma SplitSlashFreeHead(head: string, tail: string, i: nat)
    requires i <= |head|
    requires '/' !in head
    ensures SplitSegments(head+tail,i,0) == SplitSegments(head+tail,|head|,0)
    decreases |head|-i
  {
    if i < |head| {
      assert (head+tail)[i] == head[i];
      SplitSlashFreeHead(head,tail,i+1);
    }
  }

  lemma JoinedSegmentsSplit(segments: seq<string>)
    requires SimpleSegments(segments)
    ensures SplitSegments(JoinSegments(segments),0,0) == segments
    decreases |segments|
  {
    hide SplitSegments();
    if |segments| > 0 {
      var head := segments[0];
      assert InodeChildNameValid(head);
      assert |head| > 0;
      if |segments| == 1 {
        SplitSlashFreeHead(head,"",0);
        assert head+"" == head;
        assert SplitSegments(head+"",0,0) == SplitSegments(head+"",|head|,0);
        assert JoinSegments(segments) == head;
        assert SplitSegments(head,|head|,0) == [head] by {
          reveal SplitSegments();
          assert head[..|head|] == head;
        }
        assert segments == [head];
        calc {
           SplitSegments(JoinSegments(segments),0,0);
        == SplitSegments(head,0,0);
        == SplitSegments(head,|head|,0);
        == [head];
        == segments;
        }
      } else {
        var tail := JoinSegments(segments[1..]);
        assert SimpleSegments(segments[1..]);
        JoinedSegmentsSplit(segments[1..]);
        SplitSlashFreeHead(head,"/"+tail,0);
        assert head+("/"+tail) == head+"/"+tail;
        SplitOffset(head+"/",tail,0,0);
        assert JoinSegments(segments) == head+"/"+tail;
        assert (head+"/"+tail)[..|head|] == head;
        assert (head+"/"+tail)[|head|] == '/';
        assert SplitSegments(head+"/"+tail,|head|,0) ==
               [head]+SplitSegments(head+"/"+tail,|head|+1,|head|+1) by {
          reveal SplitSegments();
        }
        assert segments == [head]+segments[1..];
      }
    } else {
      assert JoinSegments(segments) == "";
      assert SplitSegments("",0,0) == [] by { reveal SplitSegments(); }
    }
  }

  lemma NormalizeSimpleSegments(segments: seq<string>, i: nat, prefix: seq<string>)
    requires i <= |segments|
    requires SimpleSegments(segments)
    ensures NormalizeSegments(segments,i,prefix) == prefix+segments[i..]
    decreases |segments|-i
  {
    if i < |segments| {
      NormalizeSimpleSegments(segments,i+1,prefix+[segments[i]]);
      assert segments[i..] == [segments[i]]+segments[i+1..];
    }
  }

  lemma BuiltSegmentsFields(segments: seq<string>)
    requires SimpleSegments(segments)
    ensures IsAbsolutePath(BuildPath(true,segments))
    ensures PathSegments(BuildPath(true,segments)) == segments
    ensures NormalizePath(BuildPath(true,segments)) == BuildPath(true,segments)
    ensures ParentPath(BuildPath(true,segments)) ==
            BuildPath(true,if |segments| == 0 then [] else segments[..|segments|-1])
  {
    JoinedSegmentsSplit(segments);
    NormalizeSimpleSegments(segments,0,[]);
    if |segments| == 0 {
      assert BuildPath(true,segments) == "/";
    } else {
      assert |segments[0]| > 0;
      assert |JoinSegments(segments)| > 0;
      assert BuildPath(true,segments) == "/"+JoinSegments(segments);
    }
    assert StripLeadingSlash(BuildPath(true,segments)) == JoinSegments(segments);
  }

  lemma LookupSegmentsSimple(inodes: map<InodeId,InodeRecord>, tree: InodeTree,
                             segments: seq<string>, found: InodeTree)
    requires InodeTreeWellFormed(tree,inodes)
    requires InodeFsLookupTreeSegments(inodes,tree,segments) == Result.Ok(found)
    ensures SimpleSegments(segments)
    decreases |segments|
  {
    if |segments| > 0 {
      LookupSegmentsSimple(inodes,tree.children[segments[0]],segments[1..],found);
      assert InodeChildNameValid(segments[0]);
      forall i: nat | i < |segments|
        ensures InodeChildNameValid(segments[i])
      {
        if i > 0 {
          assert segments[i] == segments[1..][i-1];
        }
      }
    }
  }

  ghost function CanonicalExistingPathFields(fs: FileSystem,path: Path): (canonical: Path)
    requires FsContainsPath(fs,path)
    ensures canonical == BuildPath(true,PathSegments(path))
    ensures IsAbsolutePath(canonical)
    ensures NormalizePath(canonical) == canonical
    ensures FsContainsPath(fs,canonical)
    ensures FsIdAt(fs,canonical) == FsIdAt(fs,path)
    ensures FsNodeAt(fs,canonical) == FsNodeAt(fs,path)
  {
    reveal ValidInodeFileSystemData(), InodeNamespaceWellFormed();
    reveal FsContainsPath(), InodeFsContainsPath(), InodeFsLookupId();
    var segments := PathSegments(path);
    var tree := InodeFsLookupTreeSegments(fs.inodes,fs.namespace,segments).v;
    LookupSegmentsSimple(fs.inodes,fs.namespace,segments,tree);
    BuiltSegmentsFields(segments);
    var canonical := BuildPath(true,segments);
    assert PathSegments(canonical) == segments;
    reveal FsIdAt(),FsNodeAt(),InodeFsNodeAt(),InodeFsLookupNode();
    canonical
  }

  lemma {:isolate_assertions} ModeChangedRecordFacts(record:InodeRecord,mode:bv32,now:int)
    requires InodeStorageConsistent(record) && InodeKindConsistent(record)
    ensures var after:=ModeChangedRecordFields(record,mode,now);
            after.hostKey==record.hostKey && after.links==record.links && after.kind==record.kind &&
            after.ownership==record.ownership && after.storage==record.storage &&
            InodeStorageConsistent(after) && InodeKindConsistent(after) &&
            InodeSameNodeKind(record.node,after.node) && NodeShapeUnchangedExceptMode(record.node,after.node)
    ensures !record.node.Inaccessible? ==> var after:=ModeChangedRecordFields(record,mode,now);
                                           NodeMode(after.node)==NormalizeMode(mode) && NodeTimes(after.node)==NodeTimes(record.node).(ctimeSec:=now,ctimeNsec:=0)
  {
    hide *;
    reveal ModeChangedRecordFields(),InodeRecordWithNode(),WithNodeMode(),WithNodeChangeTime(),WithNodeTimes(),NodeTimes(),NodeMode();
    reveal InodeStorageConsistent(),InodeKindConsistent(),NodeStorageSize(),InodeSameNodeKind(),NodeShapeUnchangedExceptMode(),NormalizeMode();
    assert NormalizeMode(NormalizeMode(mode)) == NormalizeMode(mode);
    if !record.node.Inaccessible? {
      var after := ModeChangedRecordFields(record,mode,now);
      assert NodeMode(after.node) == NormalizeMode(mode) by {
        match record.node
        case Regular(_,_,_,_) =>
        case Directory(_,_,_) =>
        case Symlink(_,_,_,_) =>
        case Inaccessible(_) =>
      }
    }
  }

  lemma CwdTargetRecordIsObservedFields(fs: FileSystem,context: CwdContext,target: CwdTarget)
    requires CwdContextFields(fs,context)
    requires CwdTargetFields(fs,context,target)
    ensures CwdTargetRecordFields(fs,context,target).hostKey in context.topology.objects
    ensures context.topology.objects[CwdTargetRecordFields(fs,context,target).hostKey] ==
            CwdTargetRecordFields(fs,context,target)
  {
    reveal CwdContextFields(), CwdTargetFields(), CwdTargetRecordFields();
    reveal LiveDirectoryTopologyFields(), LiveObjectRecordsFields();
    match target
    case CwdNamedTarget(path) =>
      reveal ValidInodeFileSystemData(),InodeNamespaceWellFormed();
             reveal FsContainsPath(),InodeFsContainsPath(),InodeFsLookupId();
                    var tree := InodeFsLookupTreeSegments(fs.inodes,fs.namespace,PathSegments(path)).v;
                    LookupProof.InodeLookupTreeWellFormed(fs.inodes,fs.namespace,PathSegments(path),tree);
                    reveal InodeTreeWellFormed(),FsIdAt();
    case CwdDirectoryTarget(position) =>
    case CwdEntryTarget(parent,name) =>
  }
}
