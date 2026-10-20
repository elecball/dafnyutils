include "ChmodOperandProof.dfy"

module ChmodPathProof {
  import W = BenchWorld
  import C = IOContract
  import R = Results

  lemma {:isolate_assertions} RawNonlinkFollow(fs: W.FileSystem, segments: seq<string>, index: nat,
    current: W.Path, seen: set<W.Path>, fuel: nat, directory: bool, target: W.Path)
    requires index <= |segments|
    requires C.ResolveRawSymlinkSegmentsFields(fs, segments, index, current, seen, fuel,
      false, false, directory) == R.Ok(target)
    requires W.FsContainsPath(fs, target) && !W.FsNodeAt(fs, target).Symlink?
    ensures C.ResolveRawSymlinkSegmentsFields(fs, segments, index, current, seen, fuel,
      true, false, directory) == R.Ok(target)
    decreases fuel, |segments|-index
  {
    hide *;
    reveal C.ResolveRawSymlinkSegmentsFields();
    if index == |segments| {
      assert C.TerminalNoFollowResultFields(fs, current).Ok?;
      C.TerminalNoFollowSuccessContainsFields(fs, current);
      if W.FsNodeAt(fs, current).Symlink? {
        var link := W.FsNodeAt(fs, current).target;
        assert directory && link != "" && fuel > 0;
        RawNonlinkFollow(fs, C.RawPathSegmentsFields(link), 0,
          if W.IsAbsolutePath(link) then "/" else W.ParentPath(current), seen+{current}, fuel-1,
          directory || C.HasTrailingSlash(link), target);
      }
    } else if segments[index] == "." || segments[index] == ".." {
      assert C.TerminalNoFollowResultFields(fs, current).Ok?;
      C.TerminalNoFollowSuccessContainsFields(fs, current);
      if W.FsNodeAt(fs, current).Directory? {
        RawNonlinkFollow(fs, segments, index+1,
          if segments[index] == ".." then W.ParentPath(current) else current, seen, fuel, directory, target);
      } else if W.FsNodeAt(fs, current).Symlink? {
        var link := W.FsNodeAt(fs, current).target;
        assert link != "" && fuel > 0;
        RawNonlinkFollow(fs, C.RawPathSegmentsFields(link)+segments[index..], 0,
          if W.IsAbsolutePath(link) then "/" else W.ParentPath(current), seen+{current}, fuel-1, directory, target);
      }
    } else {
      var next := W.AppendPath(current, segments[index]);
      assert C.DirectNoFollowResultFields(fs, next).Ok?;
      C.DirectNoFollowSuccessContainsFields(fs, next);
      if W.FsNodeAt(fs, next).Directory? {
        RawNonlinkFollow(fs, segments, index+1, next, seen, fuel, directory, target);
      } else if W.FsNodeAt(fs, next).Symlink? {
        var link := W.FsNodeAt(fs, next).target;
        assert index+1 < |segments| || directory;
        assert link != "" && fuel > 0;
        var remaining := segments[index+1..];
        RawNonlinkFollow(fs, C.RawPathSegmentsFields(link)+remaining, 0,
          if W.IsAbsolutePath(link) then "/" else W.ParentPath(next), seen+{next}, fuel-1,
          directory || (|remaining| == 0 && C.HasTrailingSlash(link)), target);
      }
    }
  }

  lemma {:isolate_assertions} MetadataNonlinkFollow(fs: W.FileSystem, path: W.Path, target: W.Path)
    requires C.ResolvePathForMetadataFields(fs, path, false) == R.Ok(target)
    requires !W.FsNodeAt(fs, target).Symlink?
    ensures C.ResolvePathForMetadataFields(fs, path, true) == R.Ok(target)
  {
    hide *;
    reveal C.ResolvePathForMetadataFields(), C.ResolvePathThroughSymlinkComponentsFields(),
      C.ResolvePathThroughSymlinkComponentsWithVisitedFields();
    assert path != "";
    RawNonlinkFollow(fs, C.RawPathSegmentsFields(path), 0,
      if W.IsAbsolutePath(path) then "/" else "", {}, W.SYMLINK_MAX_DEPTH,
      C.HasTrailingSlash(path), target);
  }

  lemma {:isolate_assertions} RawNonlinkModes(before: W.FileSystem, after: W.FileSystem,
    segments: seq<string>, index: nat, current: W.Path, seen: set<W.Path>, fuel: nat,
    directory: bool, target: W.Path, observed: W.Path)
    requires W.FileSystemTopologyUnchangedExceptMode(before, after)
    requires index <= |segments|
    requires C.ResolveRawSymlinkSegmentsFields(before, segments, index, current, seen, fuel,
      false, false, directory) == R.Ok(target)
    requires W.FsContainsPath(before, target) && !W.FsNodeAt(before, target).Symlink?
    requires C.ResolveRawSymlinkSegmentsFields(after, segments, index, current, seen, fuel,
      true, false, directory) == R.Ok(observed)
    ensures C.ResolveRawSymlinkSegmentsFields(after, segments, index, current, seen, fuel,
      false, false, directory) == R.Ok(observed)
    decreases fuel, |segments|-index
  {
    hide *;
    reveal C.ResolveRawSymlinkSegmentsFields();
    if index == |segments| || segments[index] == "." || segments[index] == ".." {
      assert C.TerminalNoFollowResultFields(before, current).Ok?;
      C.TerminalNoFollowSuccessContainsFields(before, current);
      C.FileSystemTopologyPathFields(before, after, current);
      reveal W.NodeShapeUnchangedExceptMode();
      if W.FsNodeAt(before, current).Directory? && index < |segments| {
        RawNonlinkModes(before, after, segments, index+1,
          if segments[index] == ".." then W.ParentPath(current) else current,
          seen, fuel, directory, target, observed);
      } else if W.FsNodeAt(before, current).Symlink? {
        var link := W.FsNodeAt(before, current).target;
        assert link != "" && fuel > 0;
        if index == |segments| {
          assert directory;
          RawNonlinkModes(before, after, C.RawPathSegmentsFields(link), 0,
            if W.IsAbsolutePath(link) then "/" else W.ParentPath(current), seen+{current}, fuel-1,
            directory || C.HasTrailingSlash(link), target, observed);
        } else {
          RawNonlinkModes(before, after, C.RawPathSegmentsFields(link)+segments[index..], 0,
            if W.IsAbsolutePath(link) then "/" else W.ParentPath(current), seen+{current}, fuel-1,
            directory, target, observed);
        }
      }
    } else {
      var next := W.AppendPath(current, segments[index]);
      assert C.DirectNoFollowResultFields(before, next).Ok?;
      C.DirectNoFollowSuccessContainsFields(before, next);
      C.FileSystemTopologyPathFields(before, after, next);
      reveal W.NodeShapeUnchangedExceptMode();
      if W.FsNodeAt(before, next).Directory? {
        RawNonlinkModes(before, after, segments, index+1, next, seen, fuel, directory, target, observed);
      } else if W.FsNodeAt(before, next).Symlink? {
        var link := W.FsNodeAt(before, next).target;
        assert index+1 < |segments| || directory;
        assert link != "" && fuel > 0;
        var remaining := segments[index+1..];
        RawNonlinkModes(before, after, C.RawPathSegmentsFields(link)+remaining, 0,
          if W.IsAbsolutePath(link) then "/" else W.ParentPath(next), seen+{next}, fuel-1,
          directory || (|remaining| == 0 && C.HasTrailingSlash(link)), target, observed);
      }
    }
  }

  lemma {:isolate_assertions} MetadataNonlinkModes(before: W.FileSystem, after: W.FileSystem,
    path: W.Path, target: W.Path, observed: W.Path)
    requires W.FileSystemTopologyUnchangedExceptMode(before, after)
    requires C.ResolvePathForMetadataFields(before, path, false) == R.Ok(target)
    requires !W.FsNodeAt(before, target).Symlink?
    requires C.ResolvePathForMetadataFields(after, path, true) == R.Ok(observed)
    ensures C.ResolvePathForMetadataFields(after, path, false) == R.Ok(observed)
  {
    hide *;
    reveal C.ResolvePathForMetadataFields(), C.ResolvePathThroughSymlinkComponentsFields(),
      C.ResolvePathThroughSymlinkComponentsWithVisitedFields();
    assert path != "";
    RawNonlinkModes(before, after, C.RawPathSegmentsFields(path), 0,
      if W.IsAbsolutePath(path) then "/" else "", {}, W.SYMLINK_MAX_DEPTH,
      C.HasTrailingSlash(path), target, observed);
  }
}
