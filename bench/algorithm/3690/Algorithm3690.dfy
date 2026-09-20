include "Core.dfy"
include "Proof.dfy"

module Algorithm3690 {
  import Spec = Algorithm3690Spec
  import Core = Algorithm3690Core
  import Proof = Algorithm3690Proof

  method RunCore(h: int, m: int, s: int, t1: int, t2: int) returns (result: string)
    requires Spec.ValidInput(h, m, s, t1, t2)
    ensures Spec.Spec(h, m, s, t1, t2, result)
  {
    Proof.ValidInputSpecToCore(h, m, s, t1, t2);
    result := Core.RunCore(h, m, s, t1, t2);
    Proof.CoreSummaryImpliesSpec(h, m, s, t1, t2, result);
  }
}
