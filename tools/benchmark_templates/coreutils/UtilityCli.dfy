include "{{CLASS_NAME}}.dfy"

module {{CLASS_NAME}}Cli {
  import BenchIO
  import BenchItem
  import {{CLASS_NAME}}

  method {:main} Main(args: seq<string>)
    modifies BenchIO.Process().Footprint()
    decreases *
  {
    // Match the repository's .NET entry convention.
    var effectiveArgs := if |args| > 0 && args[0] == "dotnet" then args[1..] else args;
    var argv := ["{{TASK_ID}}"] + effectiveArgs;
    var io := BenchIO.Process();
    var item := new {{CLASS_NAME}}.{{CLASS_NAME}}BenchmarkItem();
    var exit := BenchItem.RunMain(item, argv, io);
    BenchIO.Exit(exit);
  }
}
