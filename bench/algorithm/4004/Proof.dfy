include "Spec.dfy"
include "Core.dfy"

module Algorithm4004Proof {
  import SpecMod = Algorithm4004Spec
  import Core = Algorithm4004Core

  lemma SingletonFeasible(a: seq<int>)
    requires |a| <= 1
    ensures SpecMod.IsFeasible(a, 0)
  {
    reveal SpecMod.IsFeasible();
    reveal SpecMod.AllCanAdjustTo();
    reveal SpecMod.CanAdjustTo();
    if |a| == 0 {
      assert forall i :: 0 <= i < |a| ==> SpecMod.CanAdjustTo(a[i], 0, 0);
      assert forall i | 0 <= i < |a| :: SpecMod.CanAdjustTo(a[i], 0, 0);
      assert SpecMod.AllCanAdjustTo(a, 0, 0);
      assert SpecMod.IsFeasible(a, 0);
    } else {
      assert forall i :: 0 <= i < |a| ==> SpecMod.CanAdjustTo(a[i], 0, a[0]);
      assert forall i | 0 <= i < |a| :: SpecMod.CanAdjustTo(a[i], 0, a[0]);
      assert SpecMod.AllCanAdjustTo(a, 0, a[0]);
      assert SpecMod.IsFeasible(a, 0);
    }
  }

  lemma TwoValueFeasible(a: seq<int>, lo: int, hi: int, out: int)
    requires Core.AllInTwo(a, lo, hi)
    requires lo <= hi
    requires out >= 0
    requires hi - lo == out || hi - lo == 2 * out
    ensures SpecMod.IsFeasible(a, out)
  {
    reveal SpecMod.IsFeasible();
    reveal SpecMod.AllCanAdjustTo();
    reveal SpecMod.CanAdjustTo();
    var target := if hi - lo == 2 * out then lo + out else lo;
    forall i | 0 <= i < |a|
      ensures SpecMod.CanAdjustTo(a[i], out, target)
    {
      assert a[i] == lo || a[i] == hi;
      if hi - lo == 2 * out {
        if a[i] == lo {
          assert target == a[i] + out;
        } else {
          assert target == a[i] - out;
        }
      } else {
        if a[i] == lo {
          assert target == a[i];
        } else {
          assert hi - out == lo;
          assert target == a[i] - out;
        }
      }
    }
    assert SpecMod.AllCanAdjustTo(a, out, target);
    assert SpecMod.IsFeasible(a, out);
  }

  lemma ThreeValueFeasible(a: seq<int>, lo: int, hi: int, out: int)
    requires Core.AllInThree(a, lo, lo + out, hi)
    requires hi - lo == 2 * out
    requires out >= 0
    ensures SpecMod.IsFeasible(a, out)
  {
    reveal SpecMod.IsFeasible();
    reveal SpecMod.AllCanAdjustTo();
    reveal SpecMod.CanAdjustTo();
    var target := lo + out;
    forall i | 0 <= i < |a|
      ensures SpecMod.CanAdjustTo(a[i], out, target)
    {
      assert a[i] == lo || a[i] == target || a[i] == hi;
      if a[i] == lo {
        assert target == a[i] + out;
      } else if a[i] == target {
        assert target == a[i];
      } else {
        assert target == a[i] - out;
      }
    }
    assert SpecMod.AllCanAdjustTo(a, out, target);
    assert SpecMod.IsFeasible(a, out);
  }

  lemma FeasibleShape(a: seq<int>, lo: int, hi: int, D: int)
    requires Core.IsMin(a, lo)
    requires Core.IsMax(a, hi)
    requires lo < hi
    requires D >= 0
    requires SpecMod.IsFeasible(a, D)
    ensures (hi - lo == D && Core.AllInTwo(a, lo, hi)) ||
            (hi - lo == 2 * D && Core.AllInThree(a, lo, lo + D, hi))
  {
    reveal SpecMod.IsFeasible();
    reveal SpecMod.AllCanAdjustTo();
    reveal SpecMod.CanAdjustTo();
    var T :| SpecMod.AllCanAdjustTo(a, D, T);
    assert forall i :: 0 <= i < |a| ==> SpecMod.CanAdjustTo(a[i], D, T);
    var loIndex :| 0 <= loIndex < |a| && a[loIndex] == lo;
    var hiIndex :| 0 <= hiIndex < |a| && a[hiIndex] == hi;
    assert SpecMod.CanAdjustTo(lo, D, T);
    assert SpecMod.CanAdjustTo(hi, D, T);

    if T == lo {
      assert hi - D == T;
      assert hi - lo == D;
      forall i | 0 <= i < |a|
        ensures a[i] == lo || a[i] == hi
      {
        assert lo <= a[i] <= hi;
        assert SpecMod.CanAdjustTo(a[i], D, T);
        if T == a[i] - D {
          assert a[i] == hi;
        } else if T == a[i] {
          assert a[i] == lo;
        } else {
          assert T == a[i] + D;
          assert a[i] <= lo;
          assert a[i] == lo;
        }
      }
      assert Core.AllInTwo(a, lo, hi);
    } else {
      assert T == lo + D;
      if T == hi {
        assert hi - lo == D;
        forall i | 0 <= i < |a|
          ensures a[i] == lo || a[i] == hi
        {
          assert lo <= a[i] <= hi;
          assert SpecMod.CanAdjustTo(a[i], D, T);
          if T == a[i] - D {
            assert a[i] >= hi;
            assert a[i] == hi;
          } else if T == a[i] {
            assert a[i] == hi;
          } else {
            assert T == a[i] + D;
            assert a[i] == lo;
          }
        }
        assert Core.AllInTwo(a, lo, hi);
      } else {
        assert T == hi - D;
        assert hi - lo == 2 * D;
        assert lo + D == T;
        forall i | 0 <= i < |a|
          ensures a[i] == lo || a[i] == lo + D || a[i] == hi
        {
          assert lo <= a[i] <= hi;
          assert SpecMod.CanAdjustTo(a[i], D, T);
          if T == a[i] - D {
            assert a[i] == hi;
          } else if T == a[i] {
            assert a[i] == lo + D;
          } else {
            assert T == a[i] + D;
            assert a[i] == lo;
          }
        }
        assert Core.AllInThree(a, lo, lo + D, hi);
      }
    }
  }

  lemma FeasibleGapLowerBound(a: seq<int>, lo: int, hi: int, D: int)
    requires Core.IsMin(a, lo)
    requires Core.IsMax(a, hi)
    requires lo < hi
    requires D >= 0
    requires SpecMod.IsFeasible(a, D)
    ensures hi - lo <= 2 * D
  {
    FeasibleShape(a, lo, hi, D);
  }

  lemma CoreSummaryImpliesSpec(n: int, a: seq<int>, out: int)
    ensures Core.CoreSummary(n, a, out) ==> SpecMod.Spec(n, a, out)
  {
    if Core.CoreSummary(n, a, out) {
      if |a| <= 1 {
        assert out == 0;
        SingletonFeasible(a);
        assert forall D: int :: 0 <= D < out ==> !SpecMod.IsFeasible(a, D);
        assert SpecMod.Spec(n, a, out);
        return;
      }

      var lo, hi :| Core.IsMin(a, lo) &&
                    Core.IsMax(a, hi) &&
                    lo <= hi &&
                    var diff := hi - lo;
                    var mid := lo + diff / 2;
                    (
                      (Core.AllInTwo(a, lo, hi) &&
                       ((diff % 2 == 0 && out == diff / 2) ||
                        (diff % 2 != 0 && out == diff))) ||
                      (!Core.AllInTwo(a, lo, hi) &&
                       diff % 2 == 0 &&
                       Core.AllInThree(a, lo, mid, hi) &&
                       out == diff / 2) ||
                      (!Core.AllInTwo(a, lo, hi) &&
                       !(diff % 2 == 0 && Core.AllInThree(a, lo, mid, hi)) &&
                       out == -1)
                    );
      var diff := hi - lo;
      var mid := lo + diff / 2;

      if out == -1 {
        assert !Core.AllInTwo(a, lo, hi);
        assert !(diff % 2 == 0 && Core.AllInThree(a, lo, mid, hi));
        assert lo < hi;
        forall D: int | D >= 0
          ensures !SpecMod.IsFeasible(a, D)
        {
          if SpecMod.IsFeasible(a, D) {
            FeasibleShape(a, lo, hi, D);
            if hi - lo == D && Core.AllInTwo(a, lo, hi) {
              assert false;
            } else {
              assert hi - lo == 2 * D;
              assert diff == 2 * D;
              assert diff % 2 == 0;
              assert mid == lo + D;
              assert Core.AllInThree(a, lo, mid, hi);
              assert false;
            }
          }
        }
        assert SpecMod.Spec(n, a, out);
      } else {
        assert out >= 0;
        if Core.AllInTwo(a, lo, hi) {
          if diff % 2 == 0 {
            assert out == diff / 2;
            assert diff == 2 * out;
            TwoValueFeasible(a, lo, hi, out);
            if out > 0 {
              assert lo < hi;
              forall D: int | 0 <= D < out
                ensures !SpecMod.IsFeasible(a, D)
              {
                if SpecMod.IsFeasible(a, D) {
                  FeasibleGapLowerBound(a, lo, hi, D);
                  assert 2 * D < 2 * out;
                  assert false;
                }
              }
            }
          } else {
            assert out == diff;
            TwoValueFeasible(a, lo, hi, out);
            assert lo < hi;
            forall D: int | 0 <= D < out
              ensures !SpecMod.IsFeasible(a, D)
            {
              if SpecMod.IsFeasible(a, D) {
                FeasibleShape(a, lo, hi, D);
                if diff == D {
                  assert false;
                } else {
                  assert diff == 2 * D;
                  assert diff % 2 == 0;
                  assert false;
                }
              }
            }
          }
        } else {
          assert diff % 2 == 0;
          assert Core.AllInThree(a, lo, mid, hi);
          assert out == diff / 2;
          assert diff == 2 * out;
          ThreeValueFeasible(a, lo, hi, out);
          assert lo < hi;
          forall D: int | 0 <= D < out
            ensures !SpecMod.IsFeasible(a, D)
          {
            if SpecMod.IsFeasible(a, D) {
              FeasibleGapLowerBound(a, lo, hi, D);
              assert 2 * D < 2 * out;
              assert false;
            }
          }
        }
        assert SpecMod.Spec(n, a, out);
      }
    }
  }
}
