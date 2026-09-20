module Algorithm20Spec
{
  function TimeSeparator(): char
  {
    ':'
  }

  function {:fuel 100} CharToNat(c: char): int
  {
    (c as int) - ('0' as int)
  }

  function {:fuel 100} NatToChar(n: int): char
  {
    if 0 <= n <= 9 then (n + ('0' as int)) as char else '0'
  }

  /**
    * Predicate Spec(time, result) means:
    * Given a time string "hh:mm" in 24-hour format,
    * result is the minimal non-negative integer number of minutes to add (mod 1440)
    * so that advancing time by result minutes yields a palindrome time string.
    *
    * In other words:
    * - Parse `time` to integer minutes totalMinutes (0 <= totalMinutes < 1440)
    * - There exists result >= 0 such that:
    *   - the time string MinutesToTime((totalMinutes + result) mod 1440) is palindrome
    *   - for all k with 0 <= k < result, MinutesToTime((totalMinutes + k) mod 1440) is NOT palindrome
    */
  predicate PalindromeAfter(time: string, result: int)
    requires |time| == 5
  {
    IsPalindromeTime(MinutesToTime((TimeToMinutes(time) + result) % 1440))
  }

  predicate Spec(time: string, result: int)
  {
    |time| == 5 &&
    0 <= result &&
    PalindromeAfter(time, result) &&
    forall k ::
      0 <= k < result ==> !PalindromeAfter(time, k)
  }

  function TimeToMinutes(time: string): int
    requires |time| == 5
  {
    // Extract hour digits
    var h0 := CharToNat(time[0]);
    var h1 := CharToNat(time[1]);
    // Extract minute digits
    var m0 := CharToNat(time[3]);
    var m1 := CharToNat(time[4]);
    // Compose integer values
    (h0 * 10 + h1) * 60 + (m0 * 10 + m1)
  }

  /**
    * Converts an integer number of minutes m (0 <= m < 1440) to a string time of format "hh:mm"
    * with zero-padded hour and minute.
    * Returns the canonical 5-character string representation of the time.
    */
  function MinutesToTime(m: int): string
  {
    var hours := m / 60;
    var minutes := m % 60;
    TwoDigitStr(hours) + [TimeSeparator()] + TwoDigitStr(minutes)
  }

  /**
    * Predicate true iff t is a palindrome string of length 5 with format "hh:mm".
    * That is, t equals its reverse string.
    */
  predicate IsPalindromeTime(t: string)
  {
    |t| == 5 &&
    t[2] == TimeSeparator() &&
    t[0] == t[4] &&
    t[1] == t[3]
  }

  /**
    * Returns the two-character string representation of an integer n (0 <= n < 60),
    * zero-padded on the left if n < 10.
    * For example, TwoDigitStr(3) returns "03", and TwoDigitStr(23) returns "23".
    */
  function TwoDigitStr(n: int): string
  {
    var t := NatToChar(n / 10);
    var u := NatToChar(n % 10);
    [t] + [u]
  }
}
