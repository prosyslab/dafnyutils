module Algorithm75Spec
{
  function PositiveResult(): string
  {
    "YES"
  }

  function NegativeResult(): string
  {
    "NO"
  }

  predicate ValidGrid(n: int, m: int, grid: seq<string>)
  {
    1 <= n <= 1000 &&
    1 <= m <= 1000 &&
    |grid| == n &&
    forall r | 0 <= r < n ::
      |grid[r]| == m &&
      forall c | 0 <= c < m :: grid[r][c] == '.' || grid[r][c] == '*'
  }

  predicate BombCoversAllWalls(n: int, m: int, grid: seq<string>, x: int, y: int)
  {
    ValidGrid(n, m, grid) &&
    1 <= x <= n &&
    1 <= y <= m &&
    forall r, c | 0 <= r < n && 0 <= c < m && grid[r][c] == '*' ::
      r + 1 == x || c + 1 == y
  }

  predicate Spec(n: int, m: int, grid: seq<string>, out_status: string, out_x: int, out_y: int)
  {
    ValidGrid(n, m, grid) &&
    (
      (out_status == PositiveResult() && BombCoversAllWalls(n, m, grid, out_x, out_y)) ||
      (
        out_status == NegativeResult() &&
        out_x == 0 &&
        out_y == 0 &&
        !(exists x, y | 1 <= x <= n && 1 <= y <= m :: BombCoversAllWalls(n, m, grid, x, y))
      )
    )
  }
}
