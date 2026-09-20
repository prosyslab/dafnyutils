include "Core.dfy"
include "Proof.dfy"

module Algorithm75 {
  import Spec = Algorithm75Spec
  import Core = Algorithm75Core
  import Proof = Algorithm75Proof

  method RunCore(n: int, m: int, grid: seq<string>) returns (out_status: string, out_x: int, out_y: int)
    requires Spec.ValidGrid(n, m, grid)
    ensures Spec.Spec(n, m, grid, out_status, out_x, out_y)
  {
    Proof.ValidGridSpecToCore(n, m, grid);
    out_status, out_x, out_y := Core.RunCore(n, m, grid);
    Proof.CoreSummaryImpliesSpec(n, m, grid, out_status, out_x, out_y);
  }
}
