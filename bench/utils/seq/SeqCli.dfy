include "../../core/IO.dfy"
include "Seq.dfy"

module SeqCli {
  import BenchIO
  import Seq
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["seq"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Seq.SeqBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
