include "../../core/IO.dfy"
include "Tail.dfy"

module TailCli {
  import BenchIO
  import Tail
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["tail"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Tail.TailBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
