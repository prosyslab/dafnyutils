include "../../core/IO.dfy"
include "Expand.dfy"

module ExpandCli {
  import BenchIO
  import Expand
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["expand"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Expand.ExpandBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
