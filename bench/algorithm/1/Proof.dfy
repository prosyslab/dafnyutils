include "Spec.dfy"
include "Core.dfy"

module Algorithm1Proof {
  import SpecMod = Algorithm1Spec
  import Core = Algorithm1Core

  lemma SumOfDigitsEquivalent(n: int)
    ensures Core.SumOfDigits(n) == SpecMod.SumOfDigits(n)
    decreases if n <= 0 then 0 else n
  {
    if n > 0 {
      SumOfDigitsEquivalent(n / 10);
    }
  }

  lemma CoreSummaryImpliesSpec(x: int, result: int)
    ensures Core.CoreSummary(x, result) ==> SpecMod.Spec(x, result)
  {
    if Core.CoreSummary(x, result) {
      assert x >= 1;
      assert result == Core.Best(x);
      Core.BestIsOptimal(x);
      SumOfDigitsEquivalent(result);

      forall t | 1 <= t <= x
        ensures SpecMod.SumOfDigits(result) >= SpecMod.SumOfDigits(t)
      {
        SumOfDigitsEquivalent(t);
        assert Core.SumOfDigits(result) >= Core.SumOfDigits(t);
      }

      forall t | 1 <= t <= x && SpecMod.SumOfDigits(t) == SpecMod.SumOfDigits(result)
        ensures t <= result
      {
        SumOfDigitsEquivalent(t);
        assert Core.SumOfDigits(t) == Core.SumOfDigits(result);
        assert t <= result;
      }

      assert SpecMod.Spec(x, result);
    }
  }
}
