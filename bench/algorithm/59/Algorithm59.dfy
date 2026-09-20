include "Core.dfy"
include "Proof.dfy"

module Algorithm59 {
  import Spec = Algorithm59Spec
  import Core = Algorithm59Core
  import Proof = Algorithm59Proof

  method RunCore(n: int, a: seq<int>, s: string) returns (output: string)
    requires Spec.ValidInput(n, a, s)
    ensures Spec.Spec(n, a, s, output)
  {
    Proof.ValidInputSpecToCore(n, a, s);
    output := Core.RunCore(n, a, s);
    Proof.CoreSummaryImpliesSpec(n, a, s, output);
  }
}
