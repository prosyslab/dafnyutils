include "../../core/IO.dfy"
include "Ls.dfy"

module LsCli {
  import BenchIO
  import BenchItem
  import Ls

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["ls"] + effectiveArgs;
    var io := BenchIO.Process();
    var item := new Ls.LsBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, io);
    BenchIO.Exit(exit);
  }
}
