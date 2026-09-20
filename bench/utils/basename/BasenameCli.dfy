include "../../core/IO.dfy"
include "Basename.dfy"

module BasenameCli {
  import BenchIO
  import Basename
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["basename"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Basename.BasenameBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
