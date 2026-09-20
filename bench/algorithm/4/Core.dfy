module Algorithm4Core {
  function ContainsDigit7(x: int): bool
    decreases if x < 10 then 0 else x
  {
    x >= 0 &&
    (x % 10 == 7 || (x >= 10 && ContainsDigit7(x / 10)))
  }

  function IsLuckyTime(h: int, m: int): bool
  {
    ContainsDigit7(h) || ContainsDigit7(m)
  }

  function TimeAt(x: int, hh: int, mm: int, y: int): int
  {
    var total := hh * 60 + mm;
    ((total - x * y) % 1440 + 1440) % 1440
  }

  function LuckyAt(x: int, hh: int, mm: int, y: int): bool
  {
    IsLuckyTime(TimeAt(x, hh, mm, y) / 60, TimeAt(x, hh, mm, y) % 60)
  }

  method RunCore(x: int, hh: int, mm: int) returns (y: int)
    ensures CoreSummary(x, hh, mm, y)
    decreases *
  {
    y := 0;
    while !LuckyAt(x, hh, mm, y)
      invariant 0 <= y
      invariant forall z :: 0 <= z < y ==> !LuckyAt(x, hh, mm, z)
      decreases *
    {
      y := y + 1;
    }
  }

  ghost predicate CoreSummary(x: int, hh: int, mm: int, y: int)
  {
    0 <= y &&
    LuckyAt(x, hh, mm, y) &&
    forall z :: 0 <= z < y ==> !LuckyAt(x, hh, mm, z)
  }
}
