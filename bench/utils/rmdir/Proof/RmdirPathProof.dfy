include "../Spec/RmdirPathSpec.dfy"
include "../Impl/RmdirPathCore.dfy"

module RmdirPathProof {
  import Core = RmdirPathCore
  import Spec = RmdirPathSpec

  lemma DirnameValueSummaryGivesRelation(path: string, value: string)
    requires Core.DirnameValueSummary(path, value)
    ensures Spec.DirnameRelation(path, value)
  {
    reveal Spec.DirnameRelation();
    if |path| == 0 {
    } else if forall i {:trigger path[i]} :: 0 <= i < |path| ==> path[i] == '/' {
      assert Spec.SlashesOnly(path);
    } else {
      var trimmed :|
        Core.TrimmedSummary(path, trimmed) &&
        (if trimmed == "/" then
           value == "/"
         else
           exists slash: int ::
             Core.LastSlashSummary(trimmed, |trimmed|, slash) &&
             (if slash == -1 then
                value == "."
              else if slash == 0 then
                value == "/"
              else
                Core.TrimmedSummary(trimmed[..slash], value)));
      var end :|
        0 < end <= |path| &&
        trimmed == path[..end] &&
        path[end - 1] != '/' &&
        forall i :: end <= i < |path| ==> path[i] == '/';
      var trailing := path[end..];
      assert path == trimmed + trailing;
      assert Spec.SlashesOnly(trailing);
      assert Spec.PathWithoutTrailingSlashes(path, trimmed, trailing);
      assert trimmed != "/";
      var slash :|
        Core.LastSlashSummary(trimmed, |trimmed|, slash) &&
        (if slash == -1 then
           value == "."
         else if slash == 0 then
           value == "/"
         else
           Core.TrimmedSummary(trimmed[..slash], value));
      if slash == -1 {
        assert Spec.SlashFree(trimmed);
      } else {
        var prefix := trimmed[..slash];
        var component := trimmed[slash + 1..];
        assert trimmed == prefix + "/" + component;
        assert 0 < |component|;
        assert Spec.SlashFree(component);
        assert forall i :: 0 <= i < |trimmed| && Spec.IsSlash(trimmed[i]) ==>
                             i <= |prefix|;
        assert Spec.MaximalDirnamePrefix(trimmed, prefix, component);
        if slash == 0 {
          assert Spec.NormalizedDirnamePrefix(prefix, value);
        } else {
          assert Core.TrimmedSummary(prefix, value);
          if forall i {:trigger prefix[i]} :: 0 <= i < |prefix| ==> prefix[i] == '/' {
            assert Spec.SlashesOnly(prefix);
          } else {
            var prefixEnd :|
              0 < prefixEnd <= |prefix| &&
              value == prefix[..prefixEnd] &&
              prefix[prefixEnd - 1] != '/' &&
              forall i :: prefixEnd <= i < |prefix| ==> prefix[i] == '/';
            var prefixTrailing := prefix[prefixEnd..];
            assert prefix == value + prefixTrailing;
            assert Spec.SlashesOnly(prefixTrailing);
          }
          assert Spec.NormalizedDirnamePrefix(prefix, value);
        }
      }
    }
  }

}
