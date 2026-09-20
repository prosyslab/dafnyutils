include "Core.dfy"
include "Proof.dfy"

module Algorithm4004 {
  import Spec = Algorithm4004Spec
  import Core = Algorithm4004Core
  import Proof = Algorithm4004Proof

  method RunCore(n: int, a: seq<int>) returns (out: int)
    ensures Spec.Spec(n, a, out)
  {
    out := Core.RunCore(n, a);
    Proof.CoreSummaryImpliesSpec(n, a, out);
  }
}
