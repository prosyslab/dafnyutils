include "../../core/IO.dfy"
include "Csplit.dfy"

module CsplitCli {
  import BenchIO
  import BenchItem
  import Csplit

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["csplit"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Csplit.CsplitBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
