include "../../core/IO.dfy"
include "Readlink.dfy"

module ReadlinkCli {
  import BenchIO
  import Readlink
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["readlink"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Readlink.ReadlinkBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
