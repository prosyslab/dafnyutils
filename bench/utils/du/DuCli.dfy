include "../../core/IO.dfy"
include "Du.dfy"

module DuCli {
  import BenchIO
  import Du
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["du"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Du.DuBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
