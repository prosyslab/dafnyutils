include "Spec.dfy"
include "Core.dfy"

module Algorithm3690Proof {
  import SpecMod = Algorithm3690Spec
  import Core = Algorithm3690Core

  lemma ValidInputSpecToCore(h: int, m: int, s: int, t1: int, t2: int)
    requires SpecMod.ValidInput(h, m, s, t1, t2)
    ensures Core.ValidInput(h, m, s, t1, t2)
  {
  }

  lemma IsStrictlyBetweenCoreToSpec(p: real, start: real, end: real)
    ensures Core.IsStrictlyBetweenOnCircle(p, start, end) == SpecMod.IsStrictlyBetweenOnCircle(p, start, end)
  {
  }

  lemma ArcIsClearCoreToSpec(start: real, end: real, blockedPositions: set<real>)
    ensures Core.ArcIsClear(start, end, blockedPositions) == SpecMod.ArcIsClear(start, end, blockedPositions)
  {
    if start != end {
      forall p | p in blockedPositions
        ensures !Core.IsStrictlyBetweenOnCircle(p, start, end) ==>
                  !SpecMod.IsStrictlyBetweenOnCircle(p, start, end)
      {
        IsStrictlyBetweenCoreToSpec(p, start, end);
      }
      forall p | p in blockedPositions
        ensures !SpecMod.IsStrictlyBetweenOnCircle(p, start, end) ==>
                  !Core.IsStrictlyBetweenOnCircle(p, start, end)
      {
        IsStrictlyBetweenCoreToSpec(p, start, end);
      }
    }
  }

  lemma CoreSummaryImpliesSpec(h: int, m: int, s: int, t1: int, t2: int, result: string)
    ensures Core.CoreSummary(h, m, s, t1, t2, result) ==>
              SpecMod.Spec(h, m, s, t1, t2, result)
  {
    if Core.CoreSummary(h, m, s, t1, t2, result) {
      var hp := if h == 12 then 0.0 else h as real;
      var hourPos := hp + (m as real) / 60.0 + (s as real) / 3600.0;
      var mp := (m as real) / 5.0 + (s as real) / (5.0 * 60.0);
      var sp := (s as real) / 5.0;
      var t1p := if t1 == 12 then 0.0 else t1 as real;
      var t2p := if t2 == 12 then 0.0 else t2 as real;
      var handPositions := {hourPos, mp, sp};
      ArcIsClearCoreToSpec(t1p, t2p, handPositions);
      ArcIsClearCoreToSpec(t2p, t1p, handPositions);
      assert SpecMod.Spec(h, m, s, t1, t2, result);
    }
  }
}
