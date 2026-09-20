include "../../core/IO.dfy"
include "Ln.dfy"

module LnCli {
  import BenchIO
  import Ln
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["ln"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Ln.LnBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
