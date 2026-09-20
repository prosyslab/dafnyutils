include "../../core/IO.dfy"
include "Tee.dfy"

module TeeCli {
  import BenchIO
  import Tee
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["tee"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Tee.TeeBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
