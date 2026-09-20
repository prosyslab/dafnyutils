include "../../core/IO.dfy"
include "Head.dfy"

module HeadCli {
  import BenchIO
  import Head
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["head"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Head.HeadBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
