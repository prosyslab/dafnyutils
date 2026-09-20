include "../../core/IO.dfy"
include "Cat.dfy"

module CatCli {
  import BenchIO
  import Cat
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["cat"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Cat.CatBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
