include "../../core/IO.dfy"
include "Cut.dfy"

module CutCli {
  import BenchIO
  import Cut
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["cut"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Cut.CutBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
