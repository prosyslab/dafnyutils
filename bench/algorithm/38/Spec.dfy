module Algorithm38Spec
{
  function PositiveResult(): string
  {
    "YES"
  }

  function NegativeResult(): string
  {
    "NO"
  }

  predicate {:fuel 100} IsSorted(s: seq<int>)
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

  predicate Spec(n: int, L: int, kefa: seq<int>, sasha: seq<int>, result: string) {
    // Preconditions on inputs: sizes and domain
    ValidInput(n, L, kefa, sasha) &&
    (
      (HasRotation(n, L, kefa, sasha) && result == PositiveResult()) ||
      (!HasRotation(n, L, kefa, sasha) && result == NegativeResult())
    )
  }

  predicate HasRotation(n: int, L: int, kefa: seq<int>, sasha: seq<int>)
  {
    exists offset ::
      0 <= offset < n &&
      IsRotation(DistSeq(kefa, L), DistSeq(sasha, L), offset)
  }

  function DistSeq(p: seq<int>, L: int): seq<int>
  {
    if |p| == 0 then
      []
    else
      // Differences between consecutive barriers
      seq(|p|, i =>
        if 0 <= i && i + 1 < |p| then
          p[i + 1] - p[i]
        else // wrap-around distance from last to first barrier modulo L
          L - p[|p| - 1] + p[0]
          )
  }

  predicate IsRotation(s1: seq<int>, s2: seq<int>, offset: int)
  {
    |s1| == |s2| &&
    0 <= offset < |s1| &&
    forall i :: 0 <= i < |s1| ==> s2[i] == s1[(i + offset) % |s1|]
  }
}
