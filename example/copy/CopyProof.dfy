include "CopySpec.dfy"

module CopyProof {
  import BenchIO
  import CopySpec

  twostate lemma CopyResultImpliesSpec(
    io: BenchIO.IO, readErr: int, writeErr: int, exit: int)
    requires CopySpec.CopyResult(io, readErr, writeErr)
    requires exit == (if readErr == 0 && writeErr == 0 then 0 else 1)
    ensures CopySpec.Spec(io, exit)
  {
  }
}
