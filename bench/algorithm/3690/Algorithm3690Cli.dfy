include "Algorithm3690.dfy"

module Algorithm3690Cli {
  import BenchIO
  import BenchWorld
  import BenchItem
  import Algorithm3690
  import Spec = Algorithm3690Spec

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var sys := BenchIO.Process();
    var input := sys.ReadStdin();
    if input.Err? {
      var written := sys.WriteStderr(Spec.InvalidInputText());
      if written.Err? { BenchIO.Exit(1); }
      BenchIO.Exit(1);
      return;
    }
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var item := new Algorithm3690.Algorithm3690BenchmarkItem(input.v);
    var exit := BenchItem.RunMain(item, ["algorithm-3690"] + effectiveArgs, sys);
    BenchIO.Exit(exit);
  }
}
