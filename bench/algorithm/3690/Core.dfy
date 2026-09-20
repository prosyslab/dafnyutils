include "Spec.dfy"

module Algorithm3690Core {
  import Spec = Algorithm3690Spec

  predicate ValidInput(h: int, m: int, s: int, t1: int, t2: int)
  {
    1 <= h <= 12 &&
    0 <= m < 60 &&
    0 <= s < 60 &&
    1 <= t1 <= 12 &&
    1 <= t2 <= 12
  }

  function ClockTick(x: int): int
  {
    if x == 12 then 0 else x * 3600
  }

  predicate BetweenTicks(p: int, start: int, end: int)
  {
    if end > start then
      start < p < end
    else
      (start < p < 43200) || (0 <= p < end)
  }

  predicate ClearTicks(start: int, end: int, hourTick: int, minuteTick: int, secondTick: int)
  {
    !BetweenTicks(hourTick, start, end) &&
    !BetweenTicks(minuteTick, start, end) &&
    !BetweenTicks(secondTick, start, end)
  }

  predicate RuntimeCoreSummary(h: int, m: int, s: int, t1: int, t2: int, result: string)
  {
    var hp := if h == 12 then 0.0 else h as real;
    var hourPos := hp + (m as real) / 60.0 + (s as real) / 3600.0;
    var mp := (m as real) / 5.0 + (s as real) / (5.0 * 60.0);
    var sp := (s as real) / 5.0;
    var t1p := if t1 == 12 then 0.0 else t1 as real;
    var t2p := if t2 == 12 then 0.0 else t2 as real;
    var handPositions := {hourPos, mp, sp};
    var existsPath :=
      ArcIsClear(t1p, t2p, handPositions) || ArcIsClear(t2p, t1p, handPositions);

    (existsPath ==> result == Spec.PositiveResult()) &&
    (!existsPath ==> result == Spec.NegativeResult())
  }

  ghost predicate CoreSummary(h: int, m: int, s: int, t1: int, t2: int, result: string)
  {
    RuntimeCoreSummary(h, m, s, t1, t2, result)
  }

  predicate ArcIsClear(start: real, end: real, blockedPositions: set<real>)
  {
    if start == end then
      true
    else
      forall p :: p in blockedPositions ==> !IsStrictlyBetweenOnCircle(p, start, end)
  }

  predicate IsStrictlyBetweenOnCircle(p: real, start: real, end: real)
  {
    if end > start then
      start < p && p < end
    else
      (start < p && p < 12.0) || (0.0 <= p && p < end)
  }

  lemma BetweenTicksScaled(p: real, start: real, end: real, pt: int, startTick: int, endTick: int)
    requires p * 3600.0 == pt as real
    requires start * 3600.0 == startTick as real
    requires end * 3600.0 == endTick as real
    ensures IsStrictlyBetweenOnCircle(p, start, end) == BetweenTicks(pt, startTick, endTick)
  {
  }

  method RunCore(h: int, m: int, s: int, t1: int, t2: int) returns (result: string)
    requires ValidInput(h, m, s, t1, t2)
    ensures CoreSummary(h, m, s, t1, t2, result)
  {
    var hourTick := ClockTick(h) + m * 60 + s;
    var minuteTick := (m * 60 + s) * 12;
    var secondTick := s * 720;
    var start1 := ClockTick(t1);
    var start2 := ClockTick(t2);

    if start1 == start2 ||
       ClearTicks(start1, start2, hourTick, minuteTick, secondTick) ||
       ClearTicks(start2, start1, hourTick, minuteTick, secondTick) {
      result := Spec.PositiveResult();
    } else {
      result := Spec.NegativeResult();
    }

    ghost var hp := if h == 12 then 0.0 else h as real;
    ghost var hourPos := hp + (m as real) / 60.0 + (s as real) / 3600.0;
    ghost var minutePos := (m as real) / 5.0 + (s as real) / (5.0 * 60.0);
    ghost var secondPos := (s as real) / 5.0;
    ghost var t1Pos := if t1 == 12 then 0.0 else t1 as real;
    ghost var t2Pos := if t2 == 12 then 0.0 else t2 as real;
    assert hourPos * 3600.0 == hourTick as real;
    assert minutePos * 3600.0 == minuteTick as real;
    assert secondPos * 3600.0 == secondTick as real;
    assert t1Pos * 3600.0 == start1 as real;
    assert t2Pos * 3600.0 == start2 as real;
    BetweenTicksScaled(hourPos, t1Pos, t2Pos, hourTick, start1, start2);
    BetweenTicksScaled(minutePos, t1Pos, t2Pos, minuteTick, start1, start2);
    BetweenTicksScaled(secondPos, t1Pos, t2Pos, secondTick, start1, start2);
    BetweenTicksScaled(hourPos, t2Pos, t1Pos, hourTick, start2, start1);
    BetweenTicksScaled(minutePos, t2Pos, t1Pos, minuteTick, start2, start1);
    BetweenTicksScaled(secondPos, t2Pos, t1Pos, secondTick, start2, start1);
    assert (t1Pos == t2Pos) == (start1 == start2);
    if t1Pos != t2Pos {
      assert ArcIsClear(t1Pos, t2Pos, {hourPos, minutePos, secondPos}) ==
             ClearTicks(start1, start2, hourTick, minuteTick, secondTick) by {
        assert forall p :: p in {hourPos, minutePos, secondPos} ==>
                             (!IsStrictlyBetweenOnCircle(p, t1Pos, t2Pos) ==
                              ((p == hourPos && !BetweenTicks(hourTick, start1, start2)) ||
                               (p == minutePos && !BetweenTicks(minuteTick, start1, start2)) ||
                               (p == secondPos && !BetweenTicks(secondTick, start1, start2))));
      }
      assert ArcIsClear(t2Pos, t1Pos, {hourPos, minutePos, secondPos}) ==
             ClearTicks(start2, start1, hourTick, minuteTick, secondTick) by {
        assert forall p :: p in {hourPos, minutePos, secondPos} ==>
                             (!IsStrictlyBetweenOnCircle(p, t2Pos, t1Pos) ==
                              ((p == hourPos && !BetweenTicks(hourTick, start2, start1)) ||
                               (p == minutePos && !BetweenTicks(minuteTick, start2, start1)) ||
                               (p == secondPos && !BetweenTicks(secondTick, start2, start1))));
      }
    }
    assert CoreSummary(h, m, s, t1, t2, result);
  }
}
