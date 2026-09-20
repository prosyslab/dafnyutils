include "Core.dfy"
include "Proof.dfy"

module Algorithm20 {
  import Spec = Algorithm20Spec
  import Core = Algorithm20Core
  import Proof = Algorithm20Proof

  method RunCore(time: string) returns (result: int)
    requires |time| == 5
    ensures Spec.Spec(time, result)
    decreases *
  {
    result := Core.RunCore(time);
    Proof.CoreSummaryImpliesSpec(time, result);
  }
}
