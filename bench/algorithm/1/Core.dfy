module Algorithm1Core {
  function SumOfDigits(n: int): int
    decreases if n <= 0 then 0 else n
  {
    if n <= 0 then 0 else (n % 10) + SumOfDigits(n / 10)
  }

  function BetterOrEqual(a: int, b: int): bool
  {
    SumOfDigits(a) > SumOfDigits(b) ||
    (SumOfDigits(a) == SumOfDigits(b) && a >= b)
  }

  function Best(x: int): int
    requires x >= 1
    decreases x
  {
    if x < 10 then x else
    var prefix := x / 10;
    var fallback := if prefix == 1 then 9 else 10 * Best(prefix - 1) + 9;
    if BetterOrEqual(x, fallback) then x else fallback
  }

  lemma SumOfDigitsNonnegative(n: int)
    ensures SumOfDigits(n) >= 0
    decreases if n <= 0 then 0 else n
  {
    if n > 0 {
      SumOfDigitsNonnegative(n / 10);
    }
  }

  lemma SumAppendDigit(n: int, d: int)
    requires n >= 0
    requires 0 <= d < 10
    ensures SumOfDigits(10 * n + d) == SumOfDigits(n) + d
  {
    assert (10 * n + d) % 10 == d;
    assert (10 * n + d) / 10 == n;
  }

  lemma BestIsOptimal(x: int)
    requires x >= 1
    ensures 1 <= Best(x) <= x
    ensures forall t :: 1 <= t <= x ==> SumOfDigits(Best(x)) >= SumOfDigits(t)
    ensures forall t :: 1 <= t <= x && SumOfDigits(t) == SumOfDigits(Best(x)) ==> t <= Best(x)
    decreases x
  {
    if x < 10 {
      assert Best(x) == x;
      forall t | 1 <= t <= x
        ensures SumOfDigits(Best(x)) >= SumOfDigits(t)
        ensures SumOfDigits(t) == SumOfDigits(Best(x)) ==> t <= Best(x)
      {
        assert t < 10;
        assert SumOfDigits(t) == t;
      }
      return;
    }

    var prefix := x / 10;
    var digit := x % 10;
    assert prefix >= 1;
    assert 0 <= digit < 10;
    assert x == 10 * prefix + digit;
    SumAppendDigit(prefix, digit);

    var fallback := if prefix == 1 then 9 else 10 * Best(prefix - 1) + 9;
    if prefix > 1 {
      BestIsOptimal(prefix - 1);
      SumAppendDigit(Best(prefix - 1), 9);
      assert 1 <= Best(prefix - 1) <= prefix - 1;
      assert fallback <= 10 * (prefix - 1) + 9;
      assert fallback < x;
    } else {
      assert fallback == 9;
      assert fallback < x;
    }

    assert 1 <= fallback <= x;
    assert 1 <= Best(x) <= x;

    forall t | 1 <= t <= x
      ensures SumOfDigits(fallback) >= SumOfDigits(t) || SumOfDigits(x) >= SumOfDigits(t)
      ensures SumOfDigits(t) == SumOfDigits(fallback) && SumOfDigits(fallback) > SumOfDigits(x) ==> t <= fallback
      ensures SumOfDigits(t) == SumOfDigits(x) && SumOfDigits(x) >= SumOfDigits(fallback) ==> t <= x
    {
      var q := t / 10;
      var d := t % 10;
      assert 0 <= d < 10;
      assert t == 10 * q + d;
      SumAppendDigit(q, d);

      if q == prefix {
        assert d <= digit;
        assert SumOfDigits(t) <= SumOfDigits(x);
        assert t <= x;
      } else {
        assert q < prefix;
        if prefix == 1 {
          assert q == 0;
          assert t < 10;
          assert SumOfDigits(t) == t;
          assert t <= fallback;
          assert SumOfDigits(t) <= SumOfDigits(fallback);
        } else {
          if q == 0 {
            assert SumOfDigits(q) == 0;
            SumOfDigitsNonnegative(Best(prefix - 1));
            assert SumOfDigits(q) <= SumOfDigits(Best(prefix - 1));
            assert SumOfDigits(t) <= SumOfDigits(fallback);
          } else {
            assert 1 <= q <= prefix - 1;
            assert SumOfDigits(Best(prefix - 1)) >= SumOfDigits(q);
            assert SumOfDigits(t) <= SumOfDigits(fallback);
            if SumOfDigits(t) == SumOfDigits(fallback) {
              assert d == 9;
              assert SumOfDigits(q) == SumOfDigits(Best(prefix - 1));
              assert q <= Best(prefix - 1);
              assert t <= fallback;
            }
          }
        }
      }
    }

    if BetterOrEqual(x, fallback) {
      assert Best(x) == x;
      forall t | 1 <= t <= x
        ensures SumOfDigits(Best(x)) >= SumOfDigits(t)
        ensures SumOfDigits(t) == SumOfDigits(Best(x)) ==> t <= Best(x)
      {
        assert SumOfDigits(fallback) >= SumOfDigits(t) || SumOfDigits(x) >= SumOfDigits(t);
        assert SumOfDigits(x) >= SumOfDigits(fallback);
        assert SumOfDigits(Best(x)) >= SumOfDigits(t);
        assert t <= x;
      }
    } else {
      assert Best(x) == fallback;
      assert SumOfDigits(fallback) > SumOfDigits(x) ||
             (SumOfDigits(fallback) == SumOfDigits(x) && fallback > x);
      assert SumOfDigits(fallback) > SumOfDigits(x);
      forall t | 1 <= t <= x
        ensures SumOfDigits(Best(x)) >= SumOfDigits(t)
        ensures SumOfDigits(t) == SumOfDigits(Best(x)) ==> t <= Best(x)
      {
        assert SumOfDigits(fallback) >= SumOfDigits(t) || SumOfDigits(x) >= SumOfDigits(t);
        if SumOfDigits(x) >= SumOfDigits(t) {
          assert SumOfDigits(fallback) >= SumOfDigits(t);
        }
        if SumOfDigits(t) == SumOfDigits(Best(x)) {
          assert t <= fallback;
        }
      }
    }
  }

  method RunCore(x: int) returns (result: int)
    requires x >= 1
    ensures CoreSummary(x, result)
  {
    result := Best(x);
  }

  ghost predicate CoreSummary(x: int, result: int)
  {
    x >= 1 && result == Best(x)
  }
}
