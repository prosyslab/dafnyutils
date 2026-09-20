include "../../core/IO.dfy"
include "Base64.dfy"

module Base64Cli {
  import BenchIO
  import Base64
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["base64"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Base64.Base64BenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
