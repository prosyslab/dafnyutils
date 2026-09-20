include "../../core/IO.dfy"
include "Chmod.dfy"

module ChmodCli {
  import BenchIO
  import Chmod

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["chmod"] + effectiveArgs;
    var sys := BenchIO.Process();
    var exit := Chmod.RunCli(argv, sys);
    BenchIO.Exit(exit);
  }
}
