include "Tsort.dfy"

module TsortCli {
  import BenchIO
  import BenchItem
  import Tsort

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["tsort"] + effectiveArgs;
    var io := BenchIO.Process();
    var item := new Tsort.TsortBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, io);
    BenchIO.Exit(exit);
  }
}
