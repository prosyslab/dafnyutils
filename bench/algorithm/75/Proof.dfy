include "Spec.dfy"
include "Core.dfy"

module Algorithm75Proof {
  import SpecMod = Algorithm75Spec
  import Core = Algorithm75Core

  lemma ValidGridSpecToCore(n: int, m: int, grid: seq<string>)
    requires SpecMod.ValidGrid(n, m, grid)
    ensures Core.ValidGrid(n, m, grid)
  {
  }

  lemma CoreSummaryImpliesSpec(n: int, m: int, grid: seq<string>, out_status: string, out_x: int, out_y: int)
    ensures Core.CoreSummary(n, m, grid, out_status, out_x, out_y) ==>
              SpecMod.Spec(n, m, grid, out_status, out_x, out_y)
  {
    if Core.CoreSummary(n, m, grid, out_status, out_x, out_y) {
      assert Core.ValidGrid(n, m, grid) ==> SpecMod.ValidGrid(n, m, grid);

      if Core.ValidGrid(n, m, grid) {
        assert SpecMod.ValidGrid(n, m, grid);
        if out_status == SpecMod.PositiveResult() {
          assert Core.Covers(n, m, grid, out_x - 1, out_y - 1);
          assert 0 <= out_x - 1 < n;
          assert 0 <= out_y - 1 < m;
          assert 1 <= out_x <= n;
          assert 1 <= out_y <= m;
          assert forall r, c | 0 <= r < n && 0 <= c < m && grid[r][c] == '*' ::
              r + 1 == out_x || c + 1 == out_y;
          assert SpecMod.BombCoversAllWalls(n, m, grid, out_x, out_y);
        } else if out_status == SpecMod.NegativeResult() {
          assert out_x == 0;
          assert out_y == 0;
          assert !(exists x, y | 0 <= x < n && 0 <= y < m :: Core.Covers(n, m, grid, x, y));
          if exists x, y | 1 <= x <= n && 1 <= y <= m :: SpecMod.BombCoversAllWalls(n, m, grid, x, y) {
            var x, y :| 1 <= x <= n && 1 <= y <= m && SpecMod.BombCoversAllWalls(n, m, grid, x, y);
            assert 0 <= x - 1 < n;
            assert 0 <= y - 1 < m;
            assert forall r, c | 0 <= r < n && 0 <= c < m && grid[r][c] == '*' ::
                r == x - 1 || c == y - 1;
            assert Core.Covers(n, m, grid, x - 1, y - 1);
            assert false;
          }
        }
        assert SpecMod.Spec(n, m, grid, out_status, out_x, out_y);
      }
    }
  }
}
