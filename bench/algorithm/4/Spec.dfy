module Algorithm4Spec
{
  predicate Spec(x: int, hh: int, mm: int, y: int)
  {
    var total := hh * 60 + mm;
    0 <= y &&
    IsLuckyTime(((total - x * y) % 1440 + 1440) % 1440 / 60, ((total - x * y) % 1440 + 1440) % 1440 % 60) &&
    forall z :: 0 <= z < y ==>
                  !IsLuckyTime(((total - x * z) % 1440 + 1440) % 1440 / 60, ((total - x * z) % 1440 + 1440) % 1440 % 60)
  }

  predicate IsLuckyTime(h: int, m: int)
  {
    ContainsDigit7(h) || ContainsDigit7(m)
  }

  predicate ContainsDigit7(x: int)
  {
    x >= 0 &&
    (
      (x % 10 == 7) ||
      (x >= 10 && ContainsDigit7(x / 10))
    )
  }
}
