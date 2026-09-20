include "../../core/IO.dfy"
include "Factor.dfy"

module FactorCli {
  import BenchIO
  import Factor
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["factor"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Factor.FactorBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
