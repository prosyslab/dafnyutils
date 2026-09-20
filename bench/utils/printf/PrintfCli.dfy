include "../../core/IO.dfy"
include "Printf.dfy"

module PrintfCli {
  import BenchIO
  import Printf
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["printf"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Printf.PrintfBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
