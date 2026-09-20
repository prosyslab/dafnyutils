include "Spec.dfy"

module Algorithm75Core {
  import Spec = Algorithm75Spec

  ghost predicate ValidGrid(n: int, m: int, grid: seq<string>)
  {
    1 <= n <= 1000 &&
    1 <= m <= 1000 &&
    |grid| == n &&
    forall r | 0 <= r < n ::
      |grid[r]| == m &&
      forall c | 0 <= c < m :: grid[r][c] == '.' || grid[r][c] == '*'
  }

  ghost predicate StarAt(grid: seq<string>, r: int, c: int)
  {
    0 <= r < |grid| &&
    0 <= c < |grid[r]| &&
    grid[r][c] == '*'
  }

  ghost predicate Covers(n: int, m: int, grid: seq<string>, x: int, y: int)
  {
    ValidGrid(n, m, grid) &&
    0 <= x < n &&
    0 <= y < m &&
    forall r, c | 0 <= r < n && 0 <= c < m && grid[r][c] == '*' ::
      r == x || c == y
  }

  ghost predicate CoreSummary(n: int, m: int, grid: seq<string>, out_status: string, out_x: int, out_y: int)
  {
    ValidGrid(n, m, grid) &&
    (
      (out_status == Spec.PositiveResult() && Covers(n, m, grid, out_x - 1, out_y - 1)) ||
      (
        out_status == Spec.NegativeResult() &&
        out_x == 0 &&
        out_y == 0 &&
        !(exists x, y | 0 <= x < n && 0 <= y < m :: Covers(n, m, grid, x, y))
      )
    )
  }

  method HasShape(n: int, m: int, grid: seq<string>) returns (ok: bool)
    ensures ok ==> 1 <= n && 1 <= m && |grid| == n && forall r :: 0 <= r < n ==> |grid[r]| == m
    ensures ValidGrid(n, m, grid) ==> ok
  {
    if n < 1 || m < 1 || |grid| != n {
      ok := false;
      return;
    }

    ok := true;
    var r := 0;
    while r < n
      invariant 0 <= r <= n
      invariant 1 <= n && 1 <= m && |grid| == n
      invariant ok ==> forall rr :: 0 <= rr < r ==> |grid[rr]| == m
      invariant !ok ==> exists rr :: 0 <= rr < r && |grid[rr]| != m
    {
      if |grid[r]| != m {
        ok := false;
      }
      r := r + 1;
    }

    if ok {
      assert forall rr :: 0 <= rr < n ==> |grid[rr]| == m;
    }
  }

  method FirstStar(n: int, m: int, grid: seq<string>) returns (found: bool, row: int, col: int)
    requires 1 <= n && 1 <= m && |grid| == n
    requires forall r :: 0 <= r < n ==> |grid[r]| == m
    ensures found ==> 0 <= row < n && 0 <= col < m && grid[row][col] == '*'
    ensures !found ==> forall r, c :: 0 <= r < n && 0 <= c < m ==> grid[r][c] != '*'
  {
    found := false;
    row := 0;
    col := 0;

    var r := 0;
    while r < n && !found
      invariant 0 <= r <= n
      invariant !found ==> forall rr, cc :: 0 <= rr < r && 0 <= cc < m ==> grid[rr][cc] != '*'
      invariant found ==> 0 <= row < n && 0 <= col < m && grid[row][col] == '*'
    {
      var c := 0;
      while c < m && !found
        invariant 0 <= c <= m
        invariant !found ==> forall rr, cc ::
                      ((0 <= rr < r && 0 <= cc < m) || (rr == r && 0 <= cc < c)) ==> grid[rr][cc] != '*'
        invariant found ==> 0 <= row < n && 0 <= col < m && grid[row][col] == '*'
      {
        if grid[r][c] == '*' {
          found := true;
          row := r;
          col := c;
        }
        c := c + 1;
      }
      if !found {
        assert c == m;
        assert forall rr, cc :: 0 <= rr < r + 1 && 0 <= cc < m ==> grid[rr][cc] != '*';
      }
      r := r + 1;
    }

    if !found {
      assert r == n;
      assert forall rr, cc :: 0 <= rr < n && 0 <= cc < m ==> grid[rr][cc] != '*';
    }
  }

  method FirstUncoveredStar(n: int, m: int, grid: seq<string>, firstRow: int, firstCol: int)
    returns (found: bool, row: int, col: int)
    requires 1 <= n && 1 <= m && |grid| == n
    requires forall r :: 0 <= r < n ==> |grid[r]| == m
    requires 0 <= firstRow < n && 0 <= firstCol < m
    ensures found ==> 0 <= row < n && 0 <= col < m && grid[row][col] == '*' && row != firstRow && col != firstCol
    ensures !found ==> forall r, c :: 0 <= r < n && 0 <= c < m && grid[r][c] == '*' ==> r == firstRow || c == firstCol
  {
    found := false;
    row := 0;
    col := 0;

    var r := 0;
    while r < n && !found
      invariant 0 <= r <= n
      invariant !found ==> forall rr, cc ::
                    (0 <= rr < r && 0 <= cc < m && grid[rr][cc] == '*') ==> rr == firstRow || cc == firstCol
      invariant found ==> 0 <= row < n && 0 <= col < m && grid[row][col] == '*' && row != firstRow && col != firstCol
    {
      var c := 0;
      while c < m && !found
        invariant 0 <= c <= m
        invariant !found ==> forall rr, cc ::
                      (((0 <= rr < r && 0 <= cc < m) || (rr == r && 0 <= cc < c)) &&
                       grid[rr][cc] == '*') ==> rr == firstRow || cc == firstCol
        invariant found ==> 0 <= row < n && 0 <= col < m && grid[row][col] == '*' && row != firstRow && col != firstCol
      {
        if grid[r][c] == '*' && r != firstRow && c != firstCol {
          found := true;
          row := r;
          col := c;
        }
        c := c + 1;
      }
      if !found {
        assert c == m;
        assert forall rr, cc ::
            0 <= rr < r + 1 && 0 <= cc < m && grid[rr][cc] == '*' ==> rr == firstRow || cc == firstCol;
      }
      r := r + 1;
    }

    if !found {
      assert r == n;
      assert forall rr, cc ::
          0 <= rr < n && 0 <= cc < m && grid[rr][cc] == '*' ==> rr == firstRow || cc == firstCol;
    }
  }

  method CandidateCovers(n: int, m: int, grid: seq<string>, x: int, y: int) returns (ok: bool)
    requires 1 <= n && 1 <= m && |grid| == n
    requires forall r :: 0 <= r < n ==> |grid[r]| == m
    requires 0 <= x < n && 0 <= y < m
    ensures ValidGrid(n, m, grid) && ok ==> Covers(n, m, grid, x, y)
    ensures ValidGrid(n, m, grid) && !ok ==> !Covers(n, m, grid, x, y)
  {
    ok := true;
    ghost var badR := 0;
    ghost var badC := 0;
    var r := 0;
    while r < n && ok
      invariant 0 <= r <= n
      invariant ok ==> forall rr, cc ::
                    0 <= rr < r && 0 <= cc < m && grid[rr][cc] == '*' ==> rr == x || cc == y
      invariant !ok ==> 0 <= badR < n && 0 <= badC < m && grid[badR][badC] == '*' && badR != x && badC != y
    {
      var c := 0;
      while c < m && ok
        invariant 0 <= c <= m
        invariant ok ==> forall rr, cc ::
                      (((0 <= rr < r && 0 <= cc < m) || (rr == r && 0 <= cc < c)) &&
                       grid[rr][cc] == '*') ==> rr == x || cc == y
        invariant !ok ==> 0 <= badR < n && 0 <= badC < m && grid[badR][badC] == '*' && badR != x && badC != y
      {
        if grid[r][c] == '*' && r != x && c != y {
          ok := false;
          badR := r;
          badC := c;
        }
        c := c + 1;
      }
      if ok {
        assert c == m;
        assert forall rr, cc ::
            0 <= rr < r + 1 && 0 <= cc < m && grid[rr][cc] == '*' ==> rr == x || cc == y;
      }
      r := r + 1;
    }

    if ok {
      assert r == n;
      assert forall rr, cc :: 0 <= rr < n && 0 <= cc < m && grid[rr][cc] == '*' ==> rr == x || cc == y;
      if ValidGrid(n, m, grid) {
        assert Covers(n, m, grid, x, y);
      }
    } else if ValidGrid(n, m, grid) {
      assert 0 <= badR < n && 0 <= badC < m && grid[badR][badC] == '*' && badR != x && badC != y;
      assert !Covers(n, m, grid, x, y);
    }
  }

  lemma TwoWitnessesLimitCandidates(n: int, m: int, grid: seq<string>, firstRow: int, firstCol: int, secondRow: int, secondCol: int, x: int, y: int)
    requires ValidGrid(n, m, grid)
    requires 0 <= firstRow < n && 0 <= firstCol < m && grid[firstRow][firstCol] == '*'
    requires 0 <= secondRow < n && 0 <= secondCol < m && grid[secondRow][secondCol] == '*'
    requires secondRow != firstRow && secondCol != firstCol
    requires Covers(n, m, grid, x, y)
    ensures (x == secondRow && y == firstCol) || (x == firstRow && y == secondCol)
  {
    assert firstRow == x || firstCol == y;
    assert secondRow == x || secondCol == y;
  }

  method RunCore(n: int, m: int, grid: seq<string>) returns (out_status: string, out_x: int, out_y: int)
    requires ValidGrid(n, m, grid)
    ensures CoreSummary(n, m, grid, out_status, out_x, out_y)
  {
    out_status := Spec.NegativeResult();
    out_x := 0;
    out_y := 0;

    var shapeOk := HasShape(n, m, grid);
    assert shapeOk;
    if !shapeOk {
      return;
    }
    assert 1 <= n && 1 <= m && |grid| == n;
    assert forall r :: 0 <= r < n ==> |grid[r]| == m;

    var firstFound, firstRow, firstCol := FirstStar(n, m, grid);
    if !firstFound {
      out_status := Spec.PositiveResult();
      out_x := 1;
      out_y := 1;
      if ValidGrid(n, m, grid) {
        assert n >= 1 && m >= 1;
        assert forall r, c :: 0 <= r < n && 0 <= c < m ==> grid[r][c] != '*';
        assert Covers(n, m, grid, 0, 0);
      }
      return;
    }

    var secondFound, secondRow, secondCol := FirstUncoveredStar(n, m, grid, firstRow, firstCol);
    if !secondFound {
      var firstRowCandidateCovers := CandidateCovers(n, m, grid, 0, firstCol);
      out_status := Spec.PositiveResult();
      if firstRowCandidateCovers {
        out_x := 1;
        out_y := firstCol + 1;
      } else {
        out_x := firstRow + 1;
        out_y := firstCol + 1;
      }
      if ValidGrid(n, m, grid) {
        if firstRowCandidateCovers {
          assert Covers(n, m, grid, 0, firstCol);
        } else {
          assert Covers(n, m, grid, firstRow, firstCol);
        }
      }
      return;
    }

    var coversSecondFirst := CandidateCovers(n, m, grid, secondRow, firstCol);
    if coversSecondFirst {
      out_status := Spec.PositiveResult();
      out_x := secondRow + 1;
      out_y := firstCol + 1;
      return;
    }

    var coversFirstSecond := CandidateCovers(n, m, grid, firstRow, secondCol);
    if coversFirstSecond {
      out_status := Spec.PositiveResult();
      out_x := firstRow + 1;
      out_y := secondCol + 1;
      return;
    }

    out_status := Spec.NegativeResult();
    out_x := 0;
    out_y := 0;
    if ValidGrid(n, m, grid) {
      assert !Covers(n, m, grid, secondRow, firstCol);
      assert !Covers(n, m, grid, firstRow, secondCol);
      forall x, y | 0 <= x < n && 0 <= y < m
        ensures !Covers(n, m, grid, x, y)
      {
        if Covers(n, m, grid, x, y) {
          TwoWitnessesLimitCandidates(n, m, grid, firstRow, firstCol, secondRow, secondCol, x, y);
          if x == secondRow && y == firstCol {
            assert false;
          } else {
            assert x == firstRow && y == secondCol;
            assert false;
          }
        }
      }
    }
  }
}
