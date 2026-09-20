include "../../core/IO.dfy"
include "Pwd.dfy"

module PwdCli {
  import BenchIO
  import Pwd
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["pwd"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Pwd.PwdBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
