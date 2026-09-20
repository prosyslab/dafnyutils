include "../../core/IO.dfy"
include "Uniq.dfy"

module UniqCli {
  import BenchIO
  import Uniq
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["uniq"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Uniq.UniqBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
