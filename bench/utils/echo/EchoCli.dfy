include "../../core/IO.dfy"
include "Echo.dfy"

module EchoCli {
  import BenchIO
  import Echo
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["echo"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Echo.EchoBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
