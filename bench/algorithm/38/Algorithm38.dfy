include "Core.dfy"
include "Proof.dfy"

module Algorithm38 {
  import Spec = Algorithm38Spec
  import Core = Algorithm38Core
  import Proof = Algorithm38Proof

  method RunCore(n: int, L: int, kefa: seq<int>, sasha: seq<int>) returns (result: string)
    requires Spec.ValidInput(n, L, kefa, sasha)
    ensures Spec.Spec(n, L, kefa, sasha, result)
  {
    Proof.ValidInputSpecToCore(n, L, kefa, sasha);
    result := Core.RunCore(n, L, kefa, sasha);
    Proof.CoreSummaryImpliesSpec(n, L, kefa, sasha, result);
  }
}
