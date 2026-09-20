include "Spec.dfy"

module Algorithm100Core {
  import Spec = Algorithm100Spec

  function Min(a: int, b: int): int
  {
    if a <= b then a else b
  }

  predicate ValidScreen(n: int, m: int, screen: seq<string>)
  {
    |screen| == n &&
    forall r | 0 <= r < n ::
      |screen[r]| == m &&
      forall c | 0 <= c < m :: screen[r][c] == '.' || screen[r][c] == 'w'
  }

  predicate ValidOutputGrid(n: int, m: int, output_lines: seq<string>)
  {
    |output_lines| == n &&
    forall r | 0 <= r < n ::
      |output_lines[r]| == m &&
      forall c | 0 <= c < m ::
        output_lines[r][c] == '.' || output_lines[r][c] == 'w' || output_lines[r][c] == '+'
  }

  predicate IsFrameWithinBounds(n: int, m: int, r1: int, c1: int, d: int)
  {
    1 <= d <= Min(n, m) &&
    0 <= r1 <= n - d &&
    0 <= c1 <= m - d
  }

  function FramePixels(r1: int, c1: int, d: int): set<(int, int)>
  {
    (set c {:trigger (r1, c)} | c1 <= c < c1 + d :: (r1, c)) +
    (set c {:trigger (r1 + d - 1, c)} | c1 <= c < c1 + d :: (r1 + d - 1, c)) +
    (set r {:trigger (r, c1)} | r1 + 1 <= r < r1 + d - 1 :: (r, c1)) +
    (set r {:trigger (r, c1 + d - 1)} | r1 + 1 <= r < r1 + d - 1 :: (r, c1 + d - 1))
  }

  predicate AllWhitesOnFrame(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
  {
    ValidScreen(n, m, screen) &&
    IsFrameWithinBounds(n, m, r1, c1, d) &&
    forall r, c :: 0 <= r < n && 0 <= c < m ==>
                     (screen[r][c] == 'w' ==> OnFrame(r, c, r1, c1, d))
  }

  predicate IsValidFrame(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
  {
    ValidScreen(n, m, screen) &&
    IsFrameWithinBounds(n, m, r1, c1, d) &&
    AllWhitesOnFrame(n, m, screen, r1, c1, d) &&
    (forall r :: 0 <= r < n ==>
                   forall c :: 0 <= c < m ==>
                                 (OnFrame(r, c, r1, c1, d) ==> (screen[r][c] == 'w' || screen[r][c] == '.')))
  }

  predicate IsMinimalFrame(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
  {
    IsValidFrame(n, m, screen, r1, c1, d) &&
    forall d', r1', c1' {:trigger IsValidFrame(n, m, screen, r1', c1', d')} ::
      1 <= d' < d &&
      0 <= r1' <= n - d' &&
      0 <= c1' <= m - d' ==>
        !IsValidFrame(n, m, screen, r1', c1', d')
  }

  predicate FrameOutputLines(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int, output_lines: seq<string>)
  {
    ValidScreen(n, m, screen) &&
    |output_lines| == n &&
    forall r :: 0 <= r < n ==>
                  |output_lines[r]| == m &&
                  forall c :: 0 <= c < m ==>
                                if OnFrame(r, c, r1, c1, d) then
                                  if screen[r][c] == 'w' then output_lines[r][c] == 'w'
                                  else output_lines[r][c] == '+'
                                else
                                  output_lines[r][c] == screen[r][c]
  }

  predicate RuntimeCoreSummary(n: int, m: int, screen: seq<string>, output_lines: seq<string>)
  {
    ValidScreen(n, m, screen) &&
    (
      (output_lines == Spec.FailureResult() &&
       forall r1, c1, d ::
         0 <= r1 <= n - d && 0 <= c1 <= m - d && 1 <= d <= Min(n, m) ==>
           !IsValidFrame(n, m, screen, r1, c1, d))
      ||
      (
        ValidOutputGrid(n, m, output_lines) &&
        exists r1, c1, d ::
          0 <= r1 <= n - d &&
          0 <= c1 <= m - d &&
          1 <= d <= Min(n, m) &&
          IsValidFrame(n, m, screen, r1, c1, d) &&
          IsMinimalFrame(n, m, screen, r1, c1, d) &&
          FrameOutputLines(n, m, screen, r1, c1, d, output_lines)
      )
    )
  }

  ghost predicate CoreSummary(n: int, m: int, screen: seq<string>, output_lines: seq<string>)
  {
    RuntimeCoreSummary(n, m, screen, output_lines)
  }

  predicate OnFrame(r: int, c: int, r1: int, c1: int, d: int)
  {
    r1 <= r < r1 + d &&
    c1 <= c < c1 + d &&
    (r == r1 || r == r1 + d - 1 || c == c1 || c == c1 + d - 1)
  }

  function FrameOutputLine(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int, r: int): string
    requires ValidScreen(n, m, screen)
    requires IsFrameWithinBounds(n, m, r1, c1, d)
  {
    if 0 <= r < n then
      seq(m, c =>
        if 0 <= c < m then
          if OnFrame(r, c, r1, c1, d) then
            if screen[r][c] == 'w' then 'w' else '+'
          else
            screen[r][c]
        else '.')
    else ""
  }

  function BuildFrameOutput(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int): seq<string>
    requires ValidScreen(n, m, screen)
    requires IsFrameWithinBounds(n, m, r1, c1, d)
  {
    seq(n, r => FrameOutputLine(n, m, screen, r1, c1, d, r))
  }

  lemma BuildFrameOutputProperties(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
    requires ValidScreen(n, m, screen)
    requires IsFrameWithinBounds(n, m, r1, c1, d)
    ensures ValidOutputGrid(n, m, BuildFrameOutput(n, m, screen, r1, c1, d))
    ensures FrameOutputLines(n, m, screen, r1, c1, d, BuildFrameOutput(n, m, screen, r1, c1, d))
  {
  }

  predicate Processed(r: int, c: int, rr: int, cc: int)
  {
    rr < r || (rr == r && cc < c)
  }

  predicate BoundingBox(n: int, m: int, screen: seq<string>, minR: int, maxR: int, minC: int, maxC: int)
  {
    ValidScreen(n, m, screen) &&
    0 <= minR <= maxR < n &&
    0 <= minC <= maxC < m &&
    (exists c :: 0 <= c < m && screen[minR][c] == 'w') &&
    (exists c :: 0 <= c < m && screen[maxR][c] == 'w') &&
    (exists r :: 0 <= r < n && screen[r][minC] == 'w') &&
    (exists r :: 0 <= r < n && screen[r][maxC] == 'w') &&
    forall r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w' ==>
                     minR <= r <= maxR && minC <= c <= maxC
  }

  function BoundingSize(minR: int, maxR: int, minC: int, maxC: int): int
  {
    if maxR - minR >= maxC - minC then maxR - minR + 1 else maxC - minC + 1
  }

  lemma BoundingValidIsMinimal(
    n: int, m: int, screen: seq<string>, minR: int, maxR: int, minC: int, maxC: int,
    r1: int, c1: int, d: int)
    requires BoundingBox(n, m, screen, minR, maxR, minC, maxC)
    requires d == if maxR - minR >= maxC - minC then maxR - minR + 1 else maxC - minC + 1
    requires IsValidFrame(n, m, screen, r1, c1, d)
    ensures IsMinimalFrame(n, m, screen, r1, c1, d)
  {
  }

  lemma WhitesOnFrameValid(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
    requires ValidScreen(n, m, screen)
    requires IsFrameWithinBounds(n, m, r1, c1, d)
    requires forall r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w' ==>
                              OnFrame(r, c, r1, c1, d)
    ensures IsValidFrame(n, m, screen, r1, c1, d)
  {
  }

  lemma BoundingCandidateCompleteness(
    n: int, m: int, screen: seq<string>, minR: int, maxR: int, minC: int, maxC: int,
    pivotFound: bool, pivotR: int, pivotC: int)
    requires BoundingBox(n, m, screen, minR, maxR, minC, maxC)
    requires pivotFound ==>
               0 <= pivotR < n && 0 <= pivotC < m && screen[pivotR][pivotC] == 'w'
    requires maxR - minR >= maxC - minC ==>
               (pivotFound ==> minR < pivotR < maxR) &&
               (!pivotFound ==> forall r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w' ==>
                                                 r == minR || r == maxR)
    requires maxR - minR < maxC - minC ==>
               (pivotFound ==> minC < pivotC < maxC) &&
               (!pivotFound ==> forall r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w' ==>
                                                 c == minC || c == maxC)
    ensures (exists r1, c1, d {:trigger IsValidFrame(n, m, screen, r1, c1, d)} ::
               IsValidFrame(n, m, screen, r1, c1, d)) ==>
              exists r1, c1 {:trigger IsValidFrame(
                  n, m, screen, r1, c1,
                  BoundingSize(minR, maxR, minC, maxC))} ::
                IsValidFrame(
                  n, m, screen, r1, c1,
                  BoundingSize(minR, maxR, minC, maxC)) &&
                (if maxR - minR >= maxC - minC then
                   r1 == minR &&
                   (if pivotFound then c1 == pivotC || c1 == pivotC - (maxR - minR)
                    else c1 == (if maxC - (maxR - minR) < 0 then 0 else maxC - (maxR - minR)))
                 else
                   c1 == minC &&
                   (if pivotFound then r1 == pivotR || r1 == pivotR - (maxC - minC)
                    else r1 == (if maxR - (maxC - minC) < 0 then 0 else maxR - (maxC - minC))))
  {
    if exists r1, c1, d :: IsValidFrame(n, m, screen, r1, c1, d) {
      var validR, validC, validD :| IsValidFrame(n, m, screen, validR, validC, validD);
      var minRowC :| 0 <= minRowC < m && screen[minR][minRowC] == 'w';
      var maxRowC :| 0 <= maxRowC < m && screen[maxR][maxRowC] == 'w';
      var minColR :| 0 <= minColR < n && screen[minColR][minC] == 'w';
      var maxColR :| 0 <= maxColR < n && screen[maxColR][maxC] == 'w';
      assert OnFrame(minR, minRowC, validR, validC, validD);
      assert OnFrame(maxR, maxRowC, validR, validC, validD);
      assert OnFrame(minColR, minC, validR, validC, validD);
      assert OnFrame(maxColR, maxC, validR, validC, validD);
      assert maxR - minR + 1 <= validD;
      assert maxC - minC + 1 <= validD;
      var size := if maxR - minR >= maxC - minC then maxR - minR + 1 else maxC - minC + 1;
      assert size == BoundingSize(minR, maxR, minC, maxC);
      assert 1 <= size <= Min(n, m);
      assert forall r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w' ==>
                              OnFrame(r, c, validR, validC, validD);
      if maxR - minR >= maxC - minC {
        if pivotFound {
          assert OnFrame(pivotR, pivotC, validR, validC, validD);
          if pivotC == validC {
            assert 0 <= pivotC <= m - size;
            assert forall r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w' ==>
                                    OnFrame(r, c, minR, pivotC, size) by {
              forall r, c | 0 <= r < n && 0 <= c < m && screen[r][c] == 'w'
                ensures OnFrame(r, c, minR, pivotC, size)
              {
                if minR < r < maxR {
                  assert validR <= minR < r < maxR < validR + validD;
                  assert c == validC || c == validC + validD - 1;
                  if c != validC {
                    assert minC <= pivotC < c <= maxC;
                    assert validD <= maxC - minC + 1 <= size;
                    assert size == validD;
                  }
                }
              }
            }
            WhitesOnFrameValid(n, m, screen, minR, pivotC, size);
          } else {
            assert pivotC == validC + validD - 1;
            assert 0 <= pivotC - size + 1 <= m - size;
            assert forall r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w' ==>
                                    OnFrame(r, c, minR, pivotC - size + 1, size) by {
              forall r, c | 0 <= r < n && 0 <= c < m && screen[r][c] == 'w'
                ensures OnFrame(r, c, minR, pivotC - size + 1, size)
              {
                if minR < r < maxR {
                  assert validR <= minR < r < maxR < validR + validD;
                  assert c == validC || c == validC + validD - 1;
                  if c != validC + validD - 1 {
                    assert minC <= c < pivotC <= maxC;
                    assert validD <= maxC - minC + 1 <= size;
                    assert size == validD;
                  }
                }
              }
            }
            WhitesOnFrameValid(n, m, screen, minR, pivotC - size + 1, size);
          }
        } else {
          var left := if maxC - (maxR - minR) < 0 then 0 else maxC - (maxR - minR);
          assert 0 <= left <= m - size;
          assert forall r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w' ==>
                                  OnFrame(r, c, minR, left, size);
          WhitesOnFrameValid(n, m, screen, minR, left, size);
        }
      } else {
        if pivotFound {
          assert OnFrame(pivotR, pivotC, validR, validC, validD);
          if pivotR == validR {
            assert 0 <= pivotR <= n - size;
            assert forall r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w' ==>
                                    OnFrame(r, c, pivotR, minC, size) by {
              forall r, c | 0 <= r < n && 0 <= c < m && screen[r][c] == 'w'
                ensures OnFrame(r, c, pivotR, minC, size)
              {
                if minC < c < maxC {
                  assert validC <= minC < c < maxC < validC + validD;
                  assert r == validR || r == validR + validD - 1;
                  if r != validR {
                    assert minR <= pivotR < r <= maxR;
                    assert validD <= maxR - minR + 1 <= size;
                    assert size == validD;
                  }
                }
              }
            }
            WhitesOnFrameValid(n, m, screen, pivotR, minC, size);
          } else {
            assert pivotR == validR + validD - 1;
            assert 0 <= pivotR - size + 1 <= n - size;
            assert forall r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w' ==>
                                    OnFrame(r, c, pivotR - size + 1, minC, size) by {
              forall r, c | 0 <= r < n && 0 <= c < m && screen[r][c] == 'w'
                ensures OnFrame(r, c, pivotR - size + 1, minC, size)
              {
                if minC < c < maxC {
                  assert validC <= minC < c < maxC < validC + validD;
                  assert r == validR || r == validR + validD - 1;
                  if r != validR + validD - 1 {
                    assert minR <= r < pivotR <= maxR;
                    assert validD <= maxR - minR + 1 <= size;
                    assert size == validD;
                  }
                }
              }
            }
            WhitesOnFrameValid(n, m, screen, pivotR - size + 1, minC, size);
          }
        } else {
          var top := if maxR - (maxC - minC) < 0 then 0 else maxR - (maxC - minC);
          assert 0 <= top <= n - size;
          assert forall r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w' ==>
                                  OnFrame(r, c, top, minC, size);
          WhitesOnFrameValid(n, m, screen, top, minC, size);
        }
      }
    }
  }

  method RunCore(n: int, m: int, screen: seq<string>) returns (output_lines: seq<string>)
    requires ValidScreen(n, m, screen)
    requires exists r, c :: 0 <= r < n && 0 <= c < m && screen[r][c] == 'w'
    ensures CoreSummary(n, m, screen, output_lines)
  {
    var found := false;
    var minR, maxR, minC, maxC := 0, 0, 0, 0;
    var r := 0;
    while r < n
      invariant 0 <= r <= n
      invariant found ==> 0 <= minR <= maxR < n && 0 <= minC <= maxC < m
      invariant found ==> exists c :: 0 <= c < m && screen[minR][c] == 'w'
      invariant found ==> exists c :: 0 <= c < m && screen[maxR][c] == 'w'
      invariant found ==> exists rr :: 0 <= rr < n && screen[rr][minC] == 'w'
      invariant found ==> exists rr :: 0 <= rr < n && screen[rr][maxC] == 'w'
      invariant forall rr, cc ::
                  (0 <= rr < n && 0 <= cc < m && Processed(r, 0, rr, cc) && screen[rr][cc] == 'w') ==>
                    found && minR <= rr <= maxR && minC <= cc <= maxC
      invariant !found ==> (forall rr, cc ::
                              0 <= rr < n && 0 <= cc < m && Processed(r, 0, rr, cc) ==> screen[rr][cc] != 'w')
      decreases n - r
    {
      var c := 0;
      while c < m
        invariant 0 <= c <= m
        invariant found ==> 0 <= minR <= maxR < n && 0 <= minC <= maxC < m
        invariant found ==> exists cc :: 0 <= cc < m && screen[minR][cc] == 'w'
        invariant found ==> exists cc :: 0 <= cc < m && screen[maxR][cc] == 'w'
        invariant found ==> exists rr :: 0 <= rr < n && screen[rr][minC] == 'w'
        invariant found ==> exists rr :: 0 <= rr < n && screen[rr][maxC] == 'w'
        invariant forall rr, cc ::
                    (0 <= rr < n && 0 <= cc < m && Processed(r, c, rr, cc) && screen[rr][cc] == 'w') ==>
                      found && minR <= rr <= maxR && minC <= cc <= maxC
        invariant !found ==> (forall rr, cc ::
                                0 <= rr < n && 0 <= cc < m && Processed(r, c, rr, cc) ==> screen[rr][cc] != 'w')
        decreases m - c
      {
        if screen[r][c] == 'w' {
          if !found {
            found := true;
            minR, maxR, minC, maxC := r, r, c, c;
          } else {
            if r < minR { minR := r; }
            if r > maxR { maxR := r; }
            if c < minC { minC := c; }
            if c > maxC { maxC := c; }
          }
        }
        c := c + 1;
      }
      r := r + 1;
    }
    assert found;
    assert BoundingBox(n, m, screen, minR, maxR, minC, maxC);

    var height := maxR - minR + 1;
    var width := maxC - minC + 1;
    var d := if height >= width then height else width;
    var pivotFound := false;
    var pivotR, pivotC := 0, 0;
    r := 0;
    while r < n
      invariant 0 <= r <= n
      invariant pivotFound ==> 0 <= pivotR < n && 0 <= pivotC < m && screen[pivotR][pivotC] == 'w'
      invariant height >= width && pivotFound ==> minR < pivotR < maxR
      invariant height < width && pivotFound ==> minC < pivotC < maxC
      invariant !pivotFound ==> (forall rr, cc ::
                                   (0 <= rr < n && 0 <= cc < m && Processed(r, 0, rr, cc) && screen[rr][cc] == 'w') ==>
                                     (height >= width ==> !(minR < rr < maxR)) &&
                                     (height < width ==> !(minC < cc < maxC)))
      decreases n - r
    {
      var c := 0;
      while c < m
        invariant 0 <= c <= m
        invariant pivotFound ==> 0 <= pivotR < n && 0 <= pivotC < m && screen[pivotR][pivotC] == 'w'
        invariant height >= width && pivotFound ==> minR < pivotR < maxR
        invariant height < width && pivotFound ==> minC < pivotC < maxC
        invariant !pivotFound ==> (forall rr, cc ::
                                     (0 <= rr < n && 0 <= cc < m && Processed(r, c, rr, cc) && screen[rr][cc] == 'w') ==>
                                       (height >= width ==> !(minR < rr < maxR)) &&
                                       (height < width ==> !(minC < cc < maxC)))
        decreases m - c
      {
        if !pivotFound && screen[r][c] == 'w' &&
           ((height >= width && minR < r < maxR) || (height < width && minC < c < maxC)) {
          pivotFound, pivotR, pivotC := true, r, c;
        }
        c := c + 1;
      }
      r := r + 1;
    }
    BoundingCandidateCompleteness(n, m, screen, minR, maxR, minC, maxC, pivotFound, pivotR, pivotC);

    var r1, c1 := minR, minC;
    var r2, c2 := minR, minC;
    if height >= width {
      if pivotFound {
        c1, c2 := pivotC, pivotC - d + 1;
      } else {
        c1 := maxC - d + 1;
        if c1 < 0 { c1 := 0; }
        c2 := c1;
      }
    } else {
      if pivotFound {
        r1, r2 := pivotR, pivotR - d + 1;
      } else {
        r1 := maxR - d + 1;
        if r1 < 0 { r1 := 0; }
        r2 := r1;
      }
    }

    output_lines := Spec.FailureResult();
    if IsFrameWithinBounds(n, m, r1, c1, d) && IsValidFrame(n, m, screen, r1, c1, d) {
      BoundingValidIsMinimal(n, m, screen, minR, maxR, minC, maxC, r1, c1, d);
      BuildFrameOutputProperties(n, m, screen, r1, c1, d);
      output_lines := BuildFrameOutput(n, m, screen, r1, c1, d);
    } else if IsFrameWithinBounds(n, m, r2, c2, d) && IsValidFrame(n, m, screen, r2, c2, d) {
      BoundingValidIsMinimal(n, m, screen, minR, maxR, minC, maxC, r2, c2, d);
      BuildFrameOutputProperties(n, m, screen, r2, c2, d);
      output_lines := BuildFrameOutput(n, m, screen, r2, c2, d);
    }
    assert CoreSummary(n, m, screen, output_lines);
  }
}
