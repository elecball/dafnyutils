include "Join.dfy"

module JoinCli {
  import BenchIO
  import BenchItem
  import Join

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    // Match the repository's .NET entry convention.
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["join"] + effectiveArgs;
    var io := BenchIO.Process();
    var item := new Join.JoinBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, io);
    BenchIO.Exit(exit);
  }
}
