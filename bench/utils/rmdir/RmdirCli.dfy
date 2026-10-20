include "Rmdir.dfy"

module RmdirCli {
  import BenchIO
  import BenchItem
  import Rmdir

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    // Match the repository's .NET entry convention.
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["rmdir"] + effectiveArgs;
    var io := BenchIO.Process();
    var item := new Rmdir.RmdirBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, io);
    BenchIO.Exit(exit);
  }
}
