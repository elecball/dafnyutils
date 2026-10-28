include "../Spec/ReadlinkSchema.dfy"

module ReadlinkContextProof {
  import W = BenchWorld
  import S = ReadlinkSchema

  lemma ReadCountSnoc(files: seq<W.Path>, path: W.Path)
    ensures S.NativeReadCount(files+[path]) == S.NativeReadCount(files)+(if path == "" then 0 else 1)
  {
    var before := set i: nat | i < |files| && files[i] != "" :: i;
    var after := set i: nat | i < |files+[path]| && (files+[path])[i] != "" :: i;
    assert after == before+(if path == "" then {} else {|files|}) by {
      forall i | i in after
        ensures i in before+(if path == "" then {} else {|files|})
      {
        if i < |files| {
          assert (files+[path])[i] == files[i];
        } else {
          assert i == |files|;
          assert (files+[path])[i] == path;
        }
      }
      forall i | i in before+(if path == "" then {} else {|files|})
        ensures i in after
      {
        if i < |files| {
          assert (files+[path])[i] == files[i];
        } else {
          assert i == |files|;
          assert (files+[path])[i] == path;
        }
      }
    }
    assert |files| !in before;
  }

  lemma OffsetZero(cmd: S.ReadlinkCmd)
    ensures S.WithNativeReadOffset(cmd,[]) == cmd
  {
    assert S.NativeReadCount([]) == 0;
    match cmd.nativeReads
    case UnboundNativeReads =>
    case BoundNativeReads(failures,context) =>
      assert context.(ordinal := context.ordinal+0) == context;
  }

  lemma OffsetSnoc(cmd: S.ReadlinkCmd, files: seq<W.Path>, path: W.Path)
    ensures S.WithNativeReadOffset(cmd,files+[path]).nativeReads ==
            (match S.WithNativeReadOffset(cmd,files).nativeReads
             case UnboundNativeReads => S.UnboundNativeReads
             case BoundNativeReads(failures,context) =>
               S.BoundNativeReads(failures,context.(ordinal := context.ordinal+(if path == "" then 0 else 1))))
  {
    ReadCountSnoc(files,path);
    match cmd.nativeReads
    case UnboundNativeReads =>
    case BoundNativeReads(failures,context) =>
      assert context.(ordinal := context.ordinal+S.NativeReadCount(files)+
        (if path == "" then 0 else 1)) ==
             context.(ordinal := context.ordinal+S.NativeReadCount(files)).(ordinal :=
             context.ordinal+S.NativeReadCount(files)+(if path == "" then 0 else 1));
  }
}
