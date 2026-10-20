include "../../core/World.dfy"

module MvWorldPathCore {
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

  function NormalizeSegments(segments: seq<string>, i: int, acc: seq<string>): seq<string>
    requires 0 <= i <= |segments|
    decreases |segments| - i
  {
    W.NormalizeSegments(segments, i, acc)
  } by method {
    if i >= |segments| {
      return acc;
    }
    if segments[i] == "" || segments[i] == "." {
      return NormalizeSegments(segments, i + 1, acc);
    }
    if segments[i] == ".." {
      return NormalizeSegments(segments, i + 1,
        if |acc| == 0 then acc else acc[..|acc| - 1]);
    }
    return NormalizeSegments(segments, i + 1, acc + [segments[i]]);
  }

  function PathSegments(path: string): seq<string>
  {
    W.PathSegments(path)
  } by method {
    var stripped := StripLeadingSlash(path);
    var parts := SplitSegments(stripped, 0, 0);
    return NormalizeSegments(parts, 0, []);
  }

  function LeafName(path: string): string
  {
    W.LeafName(path)
  } by method {
    var parts := PathSegments(path);
    return if |parts| == 0 then "" else parts[|parts| - 1];
  }

  function AppendPath(parent: string, child: string): string
  {
    W.AppendPath(parent, child)
  } by method {
    if parent == "" {
      return child;
    }
    if parent == "/" {
      return "/" + child;
    }
    return parent + "/" + child;
  }

}
