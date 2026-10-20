include "ChmodSpec.dfy"

module ChmodOperandSpec {
  import W = BenchWorld
  import C = IOContract
  import Base = ChmodSpec
  import BenchIO

  datatype Operand = CwdOperand(path: W.Path) | DirectoryOperand(parent: int, path: W.Path)

  // This path belongs only to the old connected-path mathematical bridge.
  ghost function ModelPath(cwd: W.Path, native: W.CwdContext, operand: Operand): W.Path
  {
    if operand.CwdOperand? then C.AtCwdPathFields(cwd, operand.path)
    else if operand.path == "" || W.IsAbsolutePath(operand.path) then operand.path
    else if operand.parent in native.capabilities &&
      native.capabilities[operand.parent].position in native.topology.nodes &&
      |native.topology.nodes[native.capabilities[operand.parent].position].pathname| == 1 then
      W.AppendPath(native.topology.nodes[native.capabilities[operand.parent].position].pathname[0], operand.path)
    else C.AtDirPathFields(native.legacyHandles, operand.parent, operand.path)
  }

  ghost function AtOffset(context: W.CwdContext, offset: nat): W.CwdContext
  {
    context.(ordinal := context.ordinal + offset)
  }

  ghost function StatusAt(context: Base.ObservationContext, fs: W.FileSystem,
    native: W.CwdContext, operand: Operand, offset: nat, follow: bool): W.IOResult<W.FileStatus>
  {
    if operand.CwdOperand? then
      C.ObservedNativeStatusAtCwdResultFields(context.times, context.failures,
        context.cursor + offset, fs, AtOffset(native, offset), operand.path, follow)
    else
      C.ObservedNativeStatusAtDirResultFields(context.times, context.failures,
        context.cursor + offset, fs, AtOffset(native, offset), operand.parent, operand.path, follow)
  }

  ghost predicate StatusFields(context: Base.ObservationContext, fs: W.FileSystem,
    native: W.CwdContext, operand: Operand, follow: bool, afterCursor: nat, afterNative: W.CwdContext,
    ok: bool, status: W.FileStatus, err: int)
  {
    C.CwdContextReadStepFields(native, afterNative) &&
    if operand.CwdOperand? then
      C.GetFileStatusAtCwdSpec(context.times, context.failures, context.cursor, afterCursor,
        fs, native, operand.path, follow, ok, status, err)
    else
      C.GetFileStatusAtDirSpec(context.times, context.failures, context.cursor, afterCursor,
        fs, native, operand.parent, operand.path, follow, ok, status, err)
  }

  ghost predicate SetFields(context: Base.ObservationContext, now: int, fs: W.FileSystem,
    native: W.CwdContext, operand: Operand, follow: bool, mode: bv32,
    afterFs: W.FileSystem, afterNative: W.CwdContext, ok: bool, err: int)
  {
    if operand.CwdOperand? then
      C.SetFileModeAtCwdSpec(fs, native, now, context.failures, afterFs, afterNative,
        operand.path, follow, mode, ok, err)
    else
      C.SetFileModeAtDirSpec(fs, native, now, context.failures, afterFs, afterNative,
        operand.parent, operand.path, follow, mode, ok, err)
  }

  ghost predicate OpenFields(context: Base.ObservationContext, fs: W.FileSystem,
    native: W.CwdContext, operand: Operand, afterNative: W.CwdContext,
    ok: bool, handle: int, err: int)
  {
    if operand.CwdOperand? then
      C.OpenDirAtCwdSpec(fs, native, context.failures, afterNative,
        operand.path, false, ok, handle, err)
    else
      C.OpenDirAtDirSpec(fs, native, context.failures, afterNative,
        operand.parent, operand.path, false, ok, handle, err)
  }

  ghost predicate AnchorSnapshot(fs: W.FileSystem, native: W.CwdContext, operand: Operand)
  {
    operand.CwdOperand? ||
    C.DirectoryParentAnchorForContextRequestFields(fs, native, operand.parent, operand.path)
  }

  ghost predicate AnchorFields(io: BenchIO.IO, operand: Operand)
    reads io.fsRegion, io.cwdRegion, io.dirHandlesRegion, io.directoryStateRegion
  {
    AnchorSnapshot(io.fs(), io.cwdContext(), operand)
  }

  ghost function ResolveTarget(fs: W.FileSystem, native: W.CwdContext,
    operand: Operand, follow: bool): W.IOResult<W.CwdTarget>
  {
    if operand.CwdOperand? then C.ResolvePathAtCwdForMetadataFields(fs, native, operand.path, follow)
    else C.ResolvePathAtDirContextForMetadataFields(fs, native, operand.parent, operand.path, follow)
  }

  ghost predicate StructureFields(fs: W.FileSystem, native: W.CwdContext, operand: Operand,
    follow: bool, ok: bool, status: W.FileStatus, err: int)
  {
    if operand.CwdOperand? then
      C.GetFileStatusAtCwdStructureContractFields(fs, native, operand.path, follow, ok, status, err)
    else
      C.GetFileStatusAtDirContextStructureContractFields(fs, native, operand.parent, operand.path,
        follow, ok, status, err)
  }

  ghost function DirectoryKey(fs: W.FileSystem, path: W.Path): W.HostInodeKey
  {
    if W.FsContainsPath(fs, path) && W.FsIdAt(fs, path) in fs.inodes then
      fs.inodes[W.FsIdAt(fs, path)].hostKey
    else W.HostInodeKey(0, 0)
  }

  ghost predicate ActivePathsFields(fs: W.FileSystem, paths: set<W.Path>)
  {
    forall path | path in paths :: W.FsContainsPath(fs, path) && W.FsNodeAt(fs, path).Directory?
  }

  ghost function ActiveKeys(fs: W.FileSystem, paths: set<W.Path>): set<W.HostInodeKey>
  {
    set path | path in paths && W.FsContainsPath(fs, path) :: DirectoryKey(fs, path)
  }

  ghost function ActiveSegments(paths: set<W.Path>): set<seq<string>>
  {
    set path | path in paths :: W.PathSegments(path)
  }
}
