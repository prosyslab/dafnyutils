include "../../core/IO.dfy"
include "Wc.dfy"

module WcCli {
  import BenchIO
  import Wc
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["wc"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Wc.WcBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
