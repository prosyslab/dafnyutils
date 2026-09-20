include "Core.dfy"
include "Proof.dfy"

module Algorithm63 {
  import Spec = Algorithm63Spec
  import Core = Algorithm63Core
  import Proof = Algorithm63Proof

  method RunCore(n: int, k: int, a: seq<int>) returns (result: int)
    requires 0 <= n
    requires |a| == n
    ensures Spec.Spec(n, k, a, result)
  {
    result := Core.RunCore(n, k, a);
    Proof.CoreSummaryImpliesSpec(n, k, a, result);
  }
}
