include "CopyCore.dfy"
include "CopyProof.dfy"

module Copy {
  import BenchIO
  import CopySpec
  import CopyCore
  import CopyProof

  method RunCore(io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion
    ensures CopySpec.Spec(io, exit)
  {
    var readErr, writeErr := CopyCore.CopyInput(io);
    exit := if readErr == 0 && writeErr == 0 then 0 else 1;
    CopyProof.CopyResultImpliesSpec(io, readErr, writeErr, exit);
  }
}
