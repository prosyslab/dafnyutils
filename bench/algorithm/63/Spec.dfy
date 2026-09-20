module Algorithm63Spec
{
  function {:fuel 100} Product(s: seq<int>): int
  {
    if |s| == 0 then 1 else s[0] * Product(s[1..])
  }

  ghost function ValidSubdecks(a: seq<int>, k: int): set<(int, int)>
  {
    set x: int, y: int |
      0 <= x < |a| && 0 <= y < |a| && x + y < |a| &&
      IsValidSubdeck(a, x, y, k)
      :: (x, y)
  }

  ghost predicate Spec(n: int, k: int, a: seq<int>, result: int) {
    0 <= n &&
    |a| == n &&
    result == |ValidSubdecks(a, k)|
  }

  predicate IsValidSubdeck(a: seq<int>, x: int, y: int, k: int)
  {
    // The subdeck must be non-empty: x + y < |a|
    0 <= x && 0 <= y && x + y < |a| &&
    // The product of the subdeck elements is divisible by k
    SubdeckProductDivisible(a, x, y, k)
  }

  predicate SubdeckProductDivisible(a: seq<int>, x: int, y: int, k: int)
  {
    0 <= x && 0 <= y && x + y < |a| &&
    // Define the subdeck by slicing the sequence
    var subdeck := a[x .. |a| - y];

    // Divisibility condition: k divides the product of subdeck's elements
    k != 0 && Product(subdeck) % k == 0
  }
}
