include "../../../bench/core/IO.dfy"

module StreamCopy {
  import BenchIO

  method CopyInput(io: BenchIO.IO) returns (readErr: int, writeErr: int)
    modifies io.stdinRegion, io.stdoutRegion
    ensures readErr == 0 && writeErr == 0 ==>
      io.stdin() == [] && io.stdout() == old(io.stdout()) + old(io.stdin())
  {
    var data;
    data, readErr := io.ReadStdinWithOutcome();
    var committed;
    committed, writeErr := io.WriteStdoutWithOutcome(data);
  }

  method {:main} Main()
    modifies BenchIO.Process().stdinRegion, BenchIO.Process().stdoutRegion
  {
    var readErr, writeErr := CopyInput(BenchIO.Process());
    BenchIO.Exit(if readErr == 0 && writeErr == 0 then 0 else 1);
  }
}
