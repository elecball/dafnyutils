include "../../core/World.dfy"

module ReadlinkWorldPathCore {
  import W = BenchWorld

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
