include "Spec.dfy"

module Algorithm20Core {
  import Spec = Algorithm20Spec

  function CharToNat(c: char): int
  {
    (c as int) - ('0' as int)
  }

  function NatToChar(n: int): char
  {
    if 0 <= n <= 9 then (n + ('0' as int)) as char else '0'
  }

  function TimeToMinutes(time: string): int
    requires |time| == 5
  {
    var h0 := CharToNat(time[0]);
    var h1 := CharToNat(time[1]);
    var m0 := CharToNat(time[3]);
    var m1 := CharToNat(time[4]);
    (h0 * 10 + h1) * 60 + (m0 * 10 + m1)
  }

  function TwoDigitStr(n: int): string
  {
    var t := NatToChar(n / 10);
    var u := NatToChar(n % 10);
    [t] + [u]
  }

  function MinutesToTime(m: int): string
  {
    var hours := m / 60;
    var minutes := m % 60;
    TwoDigitStr(hours) + [Spec.TimeSeparator()] + TwoDigitStr(minutes)
  }

  function IsPalindromeTime(t: string): bool
  {
    |t| == 5 &&
    t[2] == Spec.TimeSeparator() &&
    t[0] == t[4] &&
    t[1] == t[3]
  }

  function PalindromeAfter(time: string, result: int): bool
    requires |time| == 5
  {
    var totalMinutes := TimeToMinutes(time);
    IsPalindromeTime(MinutesToTime((totalMinutes + result) % 1440))
  }

  method RunCore(time: string) returns (result: int)
    requires |time| == 5
    ensures CoreSummary(time, result)
    decreases *
  {
    result := 0;
    while !PalindromeAfter(time, result)
      invariant 0 <= result
      invariant forall k: int :: 0 <= k < result ==> !PalindromeAfter(time, k)
      decreases *
    {
      result := result + 1;
    }
  }

  ghost predicate CoreSummary(time: string, result: int)
  {
    |time| == 5 &&
    0 <= result &&
    PalindromeAfter(time, result) &&
    forall k: int :: 0 <= k < result ==> !PalindromeAfter(time, k)
  }
}
