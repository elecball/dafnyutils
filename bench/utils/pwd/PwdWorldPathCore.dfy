include "../../core/World.dfy"

module PwdWorldPathCore {
  import W = BenchWorld

  function StripLeadingSlash(path: string): string
  {
    W.StripLeadingSlash(path)
  } by method {
    return if |path| > 0 && path[0] == '/' then path[1..] else path;
  }

  function SplitSegments(path: string, i: int, start: int): seq<string>
    requires 0 <= start <= i <= |path|
    decreases |path| - i
  {
    W.SplitSegments(path, i, start)
  } by method {
    if i >= |path| {
      return if start >= |path| then [] else [path[start..i]];
    }
    if path[i] == '/' {
      var head := if i == start then [] else [path[start..i]];
      return head + SplitSegments(path, i + 1, i + 1);
    }
    return SplitSegments(path, i + 1, start);
  }

}
