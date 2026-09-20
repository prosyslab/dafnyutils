include "../../core/IO.dfy"
include "Tac.dfy"

module TacCli {
  import BenchIO
  import Tac
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["tac"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Tac.TacBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
