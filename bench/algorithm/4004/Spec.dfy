module Algorithm4004Spec
{
  ghost predicate Spec(n: int, a: seq<int>, out: int)
  {
    if out == -1 then
      forall D: int :: D >= 0 ==> !IsFeasible(a, D)
    else
      out >= 0 &&
      IsFeasible(a, out) &&
      forall D: int :: 0 <= D < out ==> !IsFeasible(a, D)
  }

  /**
    * Determines whether for the given sequence a and non-negative integer D,
    * there exists a common target integer T and an assignment of operations (add D, subtract D, or do nothing)
    * applied to each element a[i], resulting in all elements equal to T.
    * Formally, there exists T such that for all i in [0..|a|),
    * a[i] + op_i = T where op_i ∈ { -D, 0, D }.
    * Returns false if no such assignment exists.
    *
    * @param a sequence of integers
    * @param D non-negative integer to add or subtract
    */
  ghost predicate IsFeasible(a: seq<int>, D: int)
  {
    exists T {:trigger AllCanAdjustTo(a, D, T)} :: AllCanAdjustTo(a, D, T)
  }

  ghost predicate AllCanAdjustTo(a: seq<int>, D: int, T: int)
  {
    forall i :: 0 <= i < |a| ==> CanAdjustTo(a[i], D, T)
  }

  /**
    * Returns true iff the element 'a_i' can be adjusted by adding -D, 0, or D to obtain 'T'.
    * Formally, there exists an op in {-D, 0, D} such that a_i + op = T.
    * @param a_i an integer element from the sequence
    * @param D a non-negative integer adjustment magnitude
    * @param T the target integer value to check adjustment feasibility
    */
  predicate CanAdjustTo(a_i: int, D: int, T: int)
  {
    T == a_i - D || T == a_i || T == a_i + D
  }
}
