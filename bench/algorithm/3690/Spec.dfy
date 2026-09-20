module Algorithm3690Spec
{
  function PositiveResult(): string
  {
    "YES"
  }

  function NegativeResult(): string
  {
    "NO"
  }

  predicate ValidInput(h: int, m: int, s: int, t1: int, t2: int)
  {
    1 <= h <= 12 &&
    0 <= m < 60 &&
    0 <= s < 60 &&
    1 <= t1 <= 12 &&
    1 <= t2 <= 12
  }

  predicate Spec(h: int, m: int, s: int, t1: int, t2: int, result: string)
  {
    var hp := if h == 12 then 0.0 else h as real;
    var hourPos := hp + (m as real)/60.0 + (s as real)/3600.0;
    var mp := (m as real)/5.0 + (s as real)/(5.0*60.0);
    var sp := (s as real)/5.0;
    var t1p := if t1 == 12 then 0.0 else t1 as real;
    var t2p := if t2 == 12 then 0.0 else t2 as real;

    var handPositions := {hourPos, mp, sp};

    var existsPath :=
      ArcIsClear(t1p, t2p, handPositions) || ArcIsClear(t2p, t1p, handPositions);

    (existsPath ==> result == PositiveResult()) &&
    (!existsPath ==> result == NegativeResult())
  }

  predicate ArcIsClear(start: real, end: real, blockedPositions: set<real>)
  {
    if start == end then
      true
    else
      forall p :: p in blockedPositions ==> !IsStrictlyBetweenOnCircle(p, start, end)
  }

  /**
    * Returns true iff the position p lies strictly between start and end moving clockwise
    * on the clock circle modulo 12.
    * That is, starting from start and moving clockwise around the circle [0,12),
    * p is strictly greater than start and strictly less than end within this traversal.
    * Handles wrap-around where end < start.
    *
    * @param p - the position on the clock circle
    * @param start - start position on clock circle (exclusive)
    * @param end - end position on clock circle (exclusive)
    */
  predicate IsStrictlyBetweenOnCircle(p: real, start: real, end: real)
  {
    if end > start then
      start < p && p < end
    else
      (start < p && p < 12.0) || (0.0 <= p && p < end)
  }
}
