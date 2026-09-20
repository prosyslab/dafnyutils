include "../../core/IO.dfy"
include "Comm.dfy"

module CommCli {
  import BenchIO
  import Comm
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["comm"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Comm.CommBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
