include "../../core/IO.dfy"
include "Nl.dfy"

module NlCli {
  import BenchIO
  import Nl
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["nl"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Nl.NlBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
