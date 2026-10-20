include "LnSpec.dfy"

module LnPathCore {
  import Spec = LnSpec

  function TrimTrailingSlashes(path: string): string
    decreases |path|
  {
    Spec.TrimTrailingSlashes(path)
  } by method {
    if |path| > 0 && path[|path| - 1] == '/' {
      return TrimTrailingSlashes(path[..|path| - 1]);
    }
    return path;
  }

  function LastSlash(path: string): int
    ensures -1 <= LastSlash(path) < |path|
    decreases |path|
  {
    Spec.LastSlash(path)
  } by method {
    if |path| == 0 {
      return -1;
    }
    if path[|path| - 1] == '/' {
      return |path| - 1;
    }
    return LastSlash(path[..|path| - 1]);
  }

  function BaseName(path: string): string
  {
    Spec.BaseName(path)
  } by method {
    var trimmed := TrimTrailingSlashes(path);
    if |trimmed| == 0 {
      return if |path| == 0 then "" else "/";
    }
    var lastSlash := LastSlash(trimmed);
    return trimmed[lastSlash + 1..];
  }

  function InDirectory(directory: string, source: string): string
  {
    Spec.InDirectory(directory, source)
  } by method {
    var name := BaseName(source);
    return directory +
      (if |directory| > 0 && directory[|directory| - 1] == '/' then "" else "/") + name;
  }
}
