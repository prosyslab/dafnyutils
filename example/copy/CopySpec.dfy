include "../../bench/core/IO.dfy"

module CopySpec {
  import BenchIO
  import BenchWorld
  import C = IOContract

  twostate predicate CopyResult(io: BenchIO.IO, readErr: int, writeErr: int)
    reads io.stdinRegion, io.stdoutRegion, io.trustedStreamsRegion
  {
    exists data: BenchWorld.Bytes, committed: nat ::
      C.ReadStdinWithOutcomeSpec(
        old(io.stdin()), old(io.trustedStreams()), io.stdin(), data, readErr) &&
      C.WriteStdoutWithOutcomeSpec(
        old(io.stdout()), old(io.trustedStreams()), io.stdout(), data, committed, writeErr)
  }

  twostate predicate Spec(io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.trustedStreamsRegion
  {
    (exists readErr: int, writeErr: int ::
      CopyResult(io, readErr, writeErr) &&
      exit == (if readErr == 0 && writeErr == 0 then 0 else 1)) &&
    (exit == 0 ==>
      io.stdin() == [] && io.stdout() == old(io.stdout()) + old(io.stdin()))
  }
}
