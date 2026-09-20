include "Spec.dfy"
include "Core.dfy"

module Algorithm63Proof {
  import SpecMod = Algorithm63Spec
  import Core = Algorithm63Core

  ghost function ValidYs(
    n: int, k: int, a: seq<int>, x: int, lo: int): set<int>
    requires 0 <= lo <= n
  {
    set y: int |
      lo <= y < n &&
      0 <= x && x + y < n &&
      Core.IsValidSubdeck(a, x, y, k)
      :: y
  }

  ghost function ValidPairs(
    n: int, k: int, a: seq<int>, lo: int): set<(int, int)>
    requires 0 <= lo <= n
  {
    set x: int, y: int |
      lo <= x < n && 0 <= y < n && x + y < n &&
      Core.IsValidSubdeck(a, x, y, k)
      :: (x, y)
  }

  ghost function PairRow(x: int, ys: set<int>): set<(int, int)>
  {
    set y | y in ys :: (x, y)
  }

  lemma ProductMatches(s: seq<int>)
    ensures Core.Product(s) == SpecMod.Product(s)
    decreases |s|
  {
    if |s| > 0 {
      ProductMatches(s[1..]);
    }
  }

  lemma ValidSubdeckMatches(a: seq<int>, x: int, y: int, k: int)
    ensures Core.IsValidSubdeck(a, x, y, k) == SpecMod.IsValidSubdeck(a, x, y, k)
  {
    if 0 <= x && 0 <= y && x + y < |a| {
      ProductMatches(a[x .. |a| - y]);
    }
  }

  lemma PairRowCardinality(x: int, ys: set<int>)
    ensures |PairRow(x, ys)| == |ys|
    decreases |ys|
  {
    if ys != {} {
      var y :| y in ys;
      PairRowCardinality(x, ys - {y});
      assert PairRow(x, ys) == {(x, y)} + PairRow(x, ys - {y}) by {
        assert forall p ::
            p in PairRow(x, ys) <==>
                 p in {(x, y)} + PairRow(x, ys - {y});
      }
      assert (x, y) !in PairRow(x, ys - {y});
    }
  }

  lemma InnerFoldCardinality(
    n: int, k: int, a: seq<int>, x: int, lo: int, startIndex: int, acc: int)
    requires 0 <= lo <= n
    ensures Core.FoldIFrom(
              startIndex,
              Core.Range(lo, n),
              acc,
              (yi: int, accy: int, y: int) =>
                accy +
                (if 0 <= x && 0 <= y && x + y < n &&
                    Core.IsValidSubdeck(a, x, y, k) then 1 else 0)) ==
            acc + |ValidYs(n, k, a, x, lo)|
    decreases n - lo
  {
    if lo < n {
      var rest := ValidYs(n, k, a, x, lo + 1);
      var isValid :=
        0 <= x && x + lo < n && Core.IsValidSubdeck(a, x, lo, k);
      if isValid {
        assert ValidYs(n, k, a, x, lo) == {lo} + rest by {
          assert forall y ::
              y in ValidYs(n, k, a, x, lo) <==> y in {lo} + rest;
        }
        assert lo !in rest;
      } else {
        assert ValidYs(n, k, a, x, lo) == rest by {
          assert forall y ::
              y in ValidYs(n, k, a, x, lo) <==> y in rest;
        }
      }
      InnerFoldCardinality(
        n, k, a, x, lo + 1, startIndex + 1, acc + (if isValid then 1 else 0));
    }
  }

  lemma InnerCountCardinality(n: int, k: int, a: seq<int>, x: int)
    requires 0 <= n
    ensures Core.InnerCount(n, k, a, x) == |ValidYs(n, k, a, x, 0)|
  {
    InnerFoldCardinality(n, k, a, x, 0, 0, 0);
  }

  lemma OuterFoldCardinality(
    n: int, k: int, a: seq<int>, lo: int, startIndex: int, acc: int)
    requires 0 <= lo <= n
    ensures Core.FoldIFrom(
              startIndex,
              Core.Range(lo, n),
              acc,
              (xi: int, accx: int, x: int) =>
                Core.OuterCountStep(n, k, a, xi, accx, x)) ==
            acc + |ValidPairs(n, k, a, lo)|
    decreases n - lo
  {
    if lo < n {
      InnerCountCardinality(n, k, a, lo);
      var ys := ValidYs(n, k, a, lo, 0);
      var row := PairRow(lo, ys);
      var rest := ValidPairs(n, k, a, lo + 1);
      PairRowCardinality(lo, ys);
      assert ValidPairs(n, k, a, lo) == row + rest by {
        assert forall p ::
            p in ValidPairs(n, k, a, lo) <==> p in row + rest;
      }
      assert row * rest == {};
      OuterFoldCardinality(
        n, k, a, lo + 1, startIndex + 1, acc + Core.InnerCount(n, k, a, lo));
      var step := (xi: int, accx: int, x: int) =>
        Core.OuterCountStep(n, k, a, xi, accx, x);
      calc {
        Core.FoldIFrom(startIndex, Core.Range(lo, n), acc, step);
        == Core.FoldIFrom(startIndex + 1, Core.Range(lo + 1, n),
             acc + Core.InnerCount(n, k, a, lo), step);
        == acc + Core.InnerCount(n, k, a, lo) + |rest|;
        == acc + |ValidPairs(n, k, a, lo)|;
      }
    }
  }

  lemma CountCardinality(n: int, k: int, a: seq<int>)
    requires 0 <= n
    ensures Core.Count(n, k, a) == |ValidPairs(n, k, a, 0)|
  {
    OuterFoldCardinality(n, k, a, 0, 0, 0);
  }

  lemma ValidPairsMatchSpec(n: int, k: int, a: seq<int>)
    requires 0 <= n
    requires |a| == n
    ensures ValidPairs(n, k, a, 0) == SpecMod.ValidSubdecks(a, k)
  {
    assert forall p ::
        p in ValidPairs(n, k, a, 0) <==> p in SpecMod.ValidSubdecks(a, k) by {
      forall p
        ensures p in ValidPairs(n, k, a, 0) <==>
                p in SpecMod.ValidSubdecks(a, k)
      {
        ValidSubdeckMatches(a, p.0, p.1, k);
      }
    }
  }

  lemma CoreSummaryImpliesSpec(n: int, k: int, a: seq<int>, result: int)
    ensures Core.CoreSummary(n, k, a, result) ==>
              SpecMod.Spec(n, k, a, result)
  {
    if Core.CoreSummary(n, k, a, result) {
      CountCardinality(n, k, a);
      ValidPairsMatchSpec(n, k, a);
    }
  }
}
