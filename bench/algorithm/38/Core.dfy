include "Spec.dfy"

module Algorithm38Core {
  import Spec = Algorithm38Spec

  predicate IsSorted(s: seq<int>)
  {
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  }

  predicate ValidInput(n: int, L: int, kefa: seq<int>, sasha: seq<int>)
  {
    n >= 1 && n <= 50 &&
    L >= n && L <= 100 &&
    |kefa| == n && |sasha| == n &&
    IsSorted(kefa) && IsSorted(sasha) &&
    (forall x :: x in kefa ==> 0 <= x < L) &&
    (forall x :: x in sasha ==> 0 <= x < L)
  }

  function DistSeq(p: seq<int>, L: int): seq<int>
  {
    if |p| == 0 then
      []
    else
      seq(|p|, i =>
        if 0 <= i && i + 1 < |p| then
          p[i + 1] - p[i]
        else
          L - p[|p| - 1] + p[0]
          )
  }

  predicate IsRotation(s1: seq<int>, s2: seq<int>, offset: int)
  {
    |s1| == |s2| &&
    0 <= offset < |s1| &&
    forall i :: 0 <= i < |s1| ==> s2[i] == s1[(i + offset) % |s1|]
  }

  predicate HasRotation(n: int, L: int, kefa: seq<int>, sasha: seq<int>)
  {
    exists offset ::
      0 <= offset < n &&
      IsRotation(DistSeq(kefa, L), DistSeq(sasha, L), offset)
  }

  predicate CoreSummary(n: int, L: int, kefa: seq<int>, sasha: seq<int>, result: string)
  {
    ValidInput(n, L, kefa, sasha) &&
    (
      (HasRotation(n, L, kefa, sasha) && result == Spec.PositiveResult()) ||
      (!HasRotation(n, L, kefa, sasha) && result == Spec.NegativeResult())
    )
  }

  method RunCore(n: int, L: int, kefa: seq<int>, sasha: seq<int>) returns (result: string)
    requires ValidInput(n, L, kefa, sasha)
    ensures CoreSummary(n, L, kefa, sasha, result)
  {
    if HasRotation(n, L, kefa, sasha) {
      result := Spec.PositiveResult();
    } else {
      result := Spec.NegativeResult();
    }
  }
}
