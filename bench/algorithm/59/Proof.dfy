include "Spec.dfy"
include "Core.dfy"

module Algorithm59Proof {
  import SpecMod = Algorithm59Spec
  import Core = Algorithm59Core

  lemma RangeMatches(lo: int, hi: int)
    ensures Core.Range(lo, hi) == SpecMod.Range(lo, hi)
    decreases hi - lo
  {
    if lo < hi {
      RangeMatches(lo + 1, hi);
    }
  }

  lemma ValidInputSpecToCore(n: int, a: seq<int>, s: string)
    requires SpecMod.ValidInput(n, a, s)
    ensures Core.ValidInput(n, a, s)
  {
    RangeMatches(1, n + 1);
  }

  lemma AllowedSwapMatches(s: string, i: int)
    ensures Core.IsAllowedSwap(s, i) == SpecMod.IsAllowedSwap(s, i)
  {
  }

  lemma MaxRProperties(s: string, n: int, start: int)
    requires 1 <= start <= n
    requires |s| == n - 1
    ensures Core.MaxR(s, n, start) == n ||
            !Core.IsAllowedSwap(s, Core.MaxR(s, n, start) - 1)
    ensures forall i ::
              start - 1 <= i < Core.MaxR(s, n, start) - 1 ==>
                Core.IsAllowedSwap(s, i)
    decreases n - start
  {
    if start < n && Core.IsAllowedSwap(s, start - 1) {
      MaxRProperties(s, n, start + 1);
    }
  }

  lemma MaxRStopsAtBoundary(s: string, n: int, start: int, hi: int)
    requires 1 <= start <= hi <= n
    requires |s| == n - 1
    requires forall i :: start - 1 <= i < hi - 1 ==> Core.IsAllowedSwap(s, i)
    requires hi == n || !Core.IsAllowedSwap(s, hi - 1)
    ensures Core.MaxR(s, n, start) == hi
    decreases hi - start
  {
    if start < hi {
      assert Core.IsAllowedSwap(s, start - 1);
      MaxRStopsAtBoundary(s, n, start + 1, hi);
    }
  }

  lemma SegmentsFromContainsSwapSegment(
    s: string, n: int, start: int, lo: int, hi: int)
    requires 1 <= start <= lo
    requires 1 <= n
    requires |s| == n - 1
    requires SpecMod.IsSwapSegment(s, n, lo, hi)
    ensures (lo, hi) in Core.SegmentsFrom(s, n, start)
    decreases n - start + 1
  {
    if start <= n {
      MaxRProperties(s, n, start);
      var r := Core.MaxR(s, n, start);
      if start == lo {
        assert forall i :: lo - 1 <= i < hi - 1 ==> Core.IsAllowedSwap(s, i) by {
          forall i | lo - 1 <= i < hi - 1
            ensures Core.IsAllowedSwap(s, i)
          {
            AllowedSwapMatches(s, i);
          }
        }
        MaxRStopsAtBoundary(s, n, lo, hi);
        assert r == hi;
      } else {
        assert start < lo;
        if r >= lo {
          assert start - 1 <= lo - 2 < r - 1;
          assert Core.IsAllowedSwap(s, lo - 2);
          assert !SpecMod.IsAllowedSwap(s, lo - 2);
          assert false;
        }
        assert r + 1 <= lo;
        SegmentsFromContainsSwapSegment(s, n, r + 1, lo, hi);
      }
    }
  }

  lemma SegmentsFromMembersAreSwapSegments(s: string, n: int, start: int)
    requires 1 <= start <= n + 1
    requires |s| == n - 1
    requires start == 1 || !Core.IsAllowedSwap(s, start - 2)
    ensures forall seg ::
              seg in Core.SegmentsFrom(s, n, start) ==>
                SpecMod.IsSwapSegment(s, n, seg.0, seg.1)
    decreases n - start + 1
  {
    if start <= n {
      MaxRProperties(s, n, start);
      var r := Core.MaxR(s, n, start);
      assert forall i :: start - 1 <= i < r - 1 ==> SpecMod.IsAllowedSwap(s, i) by {
        forall i | start - 1 <= i < r - 1
          ensures SpecMod.IsAllowedSwap(s, i)
        {
          AllowedSwapMatches(s, i);
        }
      }
      AllowedSwapMatches(s, start - 2);
      AllowedSwapMatches(s, r - 1);
      assert SpecMod.IsSwapSegment(s, n, start, r);
      SegmentsFromMembersAreSwapSegments(s, n, r + 1);
      forall seg | seg in Core.SegmentsFrom(s, n, start)
        ensures SpecMod.IsSwapSegment(s, n, seg.0, seg.1)
      {
        if seg != (start, r) {
          assert seg in Core.SegmentsFrom(s, n, r + 1);
        }
      }
    }
  }

  lemma AllSegmentsGoodImpliesSortable(n: int, a: seq<int>, s: string)
    requires Core.ValidInput(n, a, s)
    requires Core.AllSegmentsGood(n, a, s)
    ensures SpecMod.Sortable(n, a, s)
  {
    forall lo, hi | SpecMod.IsSwapSegment(s, n, lo, hi)
      ensures SpecMod.IsPermutation(a[lo - 1 .. hi], SpecMod.Range(lo, hi + 1))
    {
      SegmentsFromContainsSwapSegment(s, n, 1, lo, hi);
      assert (lo, hi) in Core.Segments(s, n);
      assert Core.SegmentGood(a, (lo, hi));
      RangeMatches(lo, hi + 1);
    }
  }

  lemma SortableImpliesAllSegmentsGood(n: int, a: seq<int>, s: string)
    requires Core.ValidInput(n, a, s)
    requires SpecMod.Sortable(n, a, s)
    ensures Core.AllSegmentsGood(n, a, s)
  {
    SegmentsFromMembersAreSwapSegments(s, n, 1);
    forall seg | seg in Core.Segments(s, n)
      ensures Core.SegmentGood(a, seg)
    {
      assert SpecMod.IsSwapSegment(s, n, seg.0, seg.1);
      assert SpecMod.IsPermutation(
          a[seg.0 - 1 .. seg.1],
          SpecMod.Range(seg.0, seg.1 + 1));
      RangeMatches(seg.0, seg.1 + 1);
    }
  }

  lemma CoreSummaryImpliesSpec(n: int, a: seq<int>, s: string, output: string)
    ensures Core.CoreSummary(n, a, s, output) ==>
              SpecMod.Spec(n, a, s, output)
  {
    if Core.CoreSummary(n, a, s, output) {
      RangeMatches(1, n + 1);
      assert SpecMod.IsPermutation(a, SpecMod.Range(1, n + 1));
      if Core.AllSegmentsGood(n, a, s) {
        AllSegmentsGoodImpliesSortable(n, a, s);
      } else if SpecMod.Sortable(n, a, s) {
        SortableImpliesAllSegmentsGood(n, a, s);
        assert false;
      }
    }
  }
}
