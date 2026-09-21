include "Copy.dfy"

module CopyCli {
  import BenchIO
  import Copy

  method {:main} Main()
    modifies BenchIO.Process().stdinRegion, BenchIO.Process().stdoutRegion
  {
    var exit := Copy.RunCore(BenchIO.Process());
    BenchIO.Exit(exit);
  }
}
