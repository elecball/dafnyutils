include "Algorithm4.dfy"

module Algorithm4Cli {
  import BenchIO
  import BenchWorld
  import BenchItem
  import Algorithm4
  import Spec = Algorithm4Spec

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
    var item := new Algorithm4.Algorithm4BenchmarkItem(input.v);
    var exit := BenchItem.RunMain(item, ["algorithm-4"] + effectiveArgs, sys);
    BenchIO.Exit(exit);
  }
}
