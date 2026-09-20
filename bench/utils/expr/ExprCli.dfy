include "../../core/IO.dfy"
include "Expr.dfy"

module ExprCli {
  import BenchIO
  import Expr
  import BenchItem

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["expr"] + effectiveArgs;
    var sys := BenchIO.Process();
    var item := new Expr.ExprBenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, sys);
    BenchIO.Exit(exit);
  }
}
