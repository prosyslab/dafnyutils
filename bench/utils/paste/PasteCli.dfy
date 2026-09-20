include "../../core/IO.dfy"
include "Paste.dfy"

module PasteCli {
  import BenchIO
  import Paste
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["paste"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Paste.PasteBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
