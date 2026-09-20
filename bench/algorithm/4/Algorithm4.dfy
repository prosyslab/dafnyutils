include "Core.dfy"
include "Proof.dfy"

module Algorithm4 {
  import Spec = Algorithm4Spec
  import Core = Algorithm4Core
  import Proof = Algorithm4Proof

  method RunCore(x: int, hh: int, mm: int) returns (y: int)
    ensures Spec.Spec(x, hh, mm, y)
    decreases *
  {
    y := Core.RunCore(x, hh, mm);
    Proof.CoreSummaryImpliesSpec(x, hh, mm, y);
  }
}
