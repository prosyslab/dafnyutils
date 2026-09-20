module Algorithm59Spec
{
  function PositiveResult(): string
  {
    "YES"
  }

  function NegativeResult(): string
  {
    "NO"
  }

  predicate {:fuel 100} IsPermutation<T(==)>(a: seq<T>, b: seq<T>)
  {
    multiset(a) == multiset(b)
  }

  function {:fuel 100} Range(lo: int, hi: int): seq<int>
    decreases hi - lo
  {
    if lo >= hi then [] else [lo] + Range(lo + 1, hi)
  }

  predicate ValidInput(n: int, a: seq<int>, s: string)
  {
    1 <= n && n <= 200000 &&
    |a| == n &&
    |s| == n - 1 &&
    IsPermutation(a, Range(1, n + 1))
  }

  ghost predicate Spec(n: int, a: seq<int>, s: string, output: string)
  {
    ValidInput(n, a, s) &&
    (
      (Sortable(n, a, s) && output == PositiveResult()) ||
      (!Sortable(n, a, s) && output == NegativeResult())
    )
  }

  ghost predicate Sortable(n: int, a: seq<int>, s: string)
    requires |a| == n
  {
    forall lo, hi ::
      IsSwapSegment(s, n, lo, hi) ==>
        IsPermutation(a[lo - 1 .. hi], Range(lo, hi + 1))
  }

  predicate IsSwapSegment(s: string, n: int, lo: int, hi: int)
  {
    1 <= lo <= hi <= n &&
    (lo == 1 || !IsAllowedSwap(s, lo - 2)) &&
    (hi == n || !IsAllowedSwap(s, hi - 1)) &&
    forall i :: lo - 1 <= i < hi - 1 ==> IsAllowedSwap(s, i)
  }

  /**
    * Returns true iff the character at index i in the swap string s is '1',
    * indicating that a swap between positions i+1 and i+2 is allowed.
    * @param s The swap indicator string of length n-1.
    * @param i The zero-based index in s to check (0 ≤ i < |s|).
    */
  predicate IsAllowedSwap(s: string, i: int)
  {
    0 <= i < |s| && s[i] == '1'
  }
}
