include "../../core/IO.dfy"
include "Touch.dfy"

module TouchCli {
  import BenchIO
  import Touch
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["touch"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Touch.TouchBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
