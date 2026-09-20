include "Core.dfy"
include "Proof.dfy"

module Algorithm100 {
  import Spec = Algorithm100Spec
  import Core = Algorithm100Core
  import Proof = Algorithm100Proof

  method RunCore(n: int, m: int, screen: seq<string>) returns (output_lines: seq<string>)
    requires Spec.ValidScreen(n, m, screen)
    requires exists r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w'
    ensures Spec.Spec(n, m, screen, output_lines)
  {
    Proof.ValidScreenSpecToCore(n, m, screen);
    output_lines := Core.RunCore(n, m, screen);
    Proof.CoreSummaryImpliesSpec(n, m, screen, output_lines);
  }
}
