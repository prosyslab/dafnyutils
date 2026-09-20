module Algorithm63Core {
  function {:fuel 100} Product(s: seq<int>): int
  {
    if |s| == 0 then 1 else s[0] * Product(s[1..])
  }

  function {:fuel 100} Range(lo: int, hi: int): seq<int>
    decreases hi - lo
  {
    if lo >= hi then [] else [lo] + Range(lo + 1, hi)
  }

  function {:fuel 100} FoldIFrom<T, A>(start_idx: int, s: seq<T>, acc: A, f: (int, A, T) -> A): A
    decreases |s|
  {
    if |s| == 0 then acc
    else FoldIFrom(start_idx + 1, s[1..], f(start_idx, acc, s[0]), f)
  }

  function {:fuel 100} FoldI<T, A>(s: seq<T>, init: A, f: (int, A, T) -> A): A
  {
    FoldIFrom(0, s, init, f)
  }

  predicate IsValidSubdeck(a: seq<int>, x: int, y: int, k: int)
  {
    0 <= x && 0 <= y && x + y < |a| &&
    SubdeckProductDivisible(a, x, y, k)
  }

  predicate SubdeckProductDivisible(a: seq<int>, x: int, y: int, k: int)
  {
    0 <= x && 0 <= y && x + y < |a| &&
    k != 0 && Product(a[x .. |a| - y]) % k == 0
  }

  function InnerCount(n: int, k: int, a: seq<int>, x: int): int
  {
    FoldI(Range(0, n), 0, (yi: int, accy: int, y: int) =>
            accy + (if 0 <= x && 0 <= y && x + y < n && IsValidSubdeck(a, x, y, k) then 1 else 0)
    )
  }

  function OuterCountStep(n: int, k: int, a: seq<int>, xi: int, accx: int, x: int): int
  {
    accx + InnerCount(n, k, a, x)
  }

  function Count(n: int, k: int, a: seq<int>): int
  {
    FoldI(Range(0, n), 0, (xi: int, accx: int, x: int) =>
            OuterCountStep(n, k, a, xi, accx, x)
    )
  }

  method RunCore(n: int, k: int, a: seq<int>) returns (result: int)
    requires 0 <= n
    requires |a| == n
    ensures CoreSummary(n, k, a, result)
  {
    result := Count(n, k, a);
  }

  ghost predicate CoreSummary(n: int, k: int, a: seq<int>, result: int)
  {
    0 <= n &&
    |a| == n &&
    result == Count(n, k, a)
  }
}
