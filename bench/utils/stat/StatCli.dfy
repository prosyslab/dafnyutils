include "../../core/IO.dfy"
include "Stat.dfy"

module StatCli {
  import BenchIO
  import Stat
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["stat"] + effectiveArgs;
    var io := BenchIO.Process();
    var item := new Stat.StatBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, io);
    BenchIO.Exit(exit);
  }
}
