include "Core.dfy"
include "Proof.dfy"

module Algorithm1 {
  import Spec = Algorithm1Spec
  import Core = Algorithm1Core
  import Proof = Algorithm1Proof

  method RunCore(x: int) returns (result: int)
    requires x >= 1
    ensures Spec.Spec(x, result)
  {
    result := Core.RunCore(x);
    Proof.CoreSummaryImpliesSpec(x, result);
  }
}
