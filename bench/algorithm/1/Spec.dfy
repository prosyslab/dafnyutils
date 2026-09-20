module Algorithm1Spec
{
  predicate Spec(x: int, result: int)
  {
    1 <= result <= x
    &&
    (forall t :: 1 <= t <= x ==> SumOfDigits(result) >= SumOfDigits(t))
    &&
    (forall t :: 1 <= t <= x && SumOfDigits(t) == SumOfDigits(result) ==> t <= result)
  }

  /**
    * Returns the sum of decimal digits of the positive integer n.
    * For example, SumOfDigits(521) == 5 + 2 + 1 == 8.
    * It holds that SumOfDigits(n) >= 0 for all n >= 0.
    * Precondition: n >= 0.
    * Note: Leading zeros do not affect the sum.
    * @param n the integer whose decimal digits are summed
    * @return the sum of digits of n
    */
  function SumOfDigits(n: int): int
    decreases n
  {
    if n <= 0 then 0 else (n % 10) + SumOfDigits(n / 10)
  }
}
