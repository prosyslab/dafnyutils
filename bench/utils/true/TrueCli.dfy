include "../../core/IO.dfy"
include "True.dfy"

module TrueCli {
  import BenchIO
  import True
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["true"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new True.TrueBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
