include "../../core/World.dfy"
include "FactorSchema.dfy"
include "FactorCore.dfy"
include "FactorSpec.dfy"

module FactorProof {
  import BenchIO
  import BW = BenchWorld
  import Schema = FactorSchema
  import Core = FactorCore
  import Spec = FactorSpec

  lemma IsWhitespaceEq(ch: char)
    ensures Core.IsWhitespace(ch) == Spec.IsWhitespace(ch)
  {
  }

  lemma IsDigitEq(ch: char)
    ensures Core.IsDigit(ch) == Spec.IsDigit(ch)
  {
  }

  lemma HelpSelectedEq(raw: Schema.FactorCmdRaw)
    ensures Core.HelpSelected(raw) == Spec.HelpSelected(raw)
  {
  }

  lemma VersionSelectedEq(raw: Schema.FactorCmdRaw)
    ensures Core.VersionSelected(raw) == Spec.VersionSelected(raw)
  {
  }

  lemma TrimLeftWhitespaceRelation(text: string)
    ensures exists leading: string ::
              text == leading + Core.TrimLeftWhitespace(text) &&
              Spec.WhitespaceOnly(leading) &&
              (|Core.TrimLeftWhitespace(text)| == 0 ||
               !Spec.IsWhitespace(Core.TrimLeftWhitespace(text)[0]))
    decreases |text|
  {
    if |text| == 0 {
      assert Spec.WhitespaceOnly("");
    } else {
      IsWhitespaceEq(text[0]);
      if Core.IsWhitespace(text[0]) {
        TrimLeftWhitespaceRelation(text[1..]);
        var leading: string :|
          text[1..] == leading + Core.TrimLeftWhitespace(text[1..]) &&
          Spec.WhitespaceOnly(leading) &&
          (|Core.TrimLeftWhitespace(text[1..])| == 0 ||
           !Spec.IsWhitespace(Core.TrimLeftWhitespace(text[1..])[0]));
        assert Spec.WhitespaceOnly([text[0]] + leading) by {
          reveal Spec.WhitespaceOnly();
        }
      } else {
        assert Spec.WhitespaceOnly("");
      }
    }
  }

  lemma TrimRightWhitespaceRelation(text: string)
    ensures exists trailing: string ::
              text == Core.TrimRightWhitespace(text) + trailing &&
              Spec.WhitespaceOnly(trailing) &&
              (|Core.TrimRightWhitespace(text)| == 0 ||
               !Spec.IsWhitespace(
                 Core.TrimRightWhitespace(text)[|Core.TrimRightWhitespace(text)| - 1]
               ))
    decreases |text|
  {
    if |text| == 0 {
      assert Spec.WhitespaceOnly("");
    } else {
      IsWhitespaceEq(text[|text| - 1]);
      if Core.IsWhitespace(text[|text| - 1]) {
        TrimRightWhitespaceRelation(text[..|text| - 1]);
        var trailing: string :|
          text[..|text| - 1] ==
          Core.TrimRightWhitespace(text[..|text| - 1]) + trailing &&
          Spec.WhitespaceOnly(trailing) &&
          (|Core.TrimRightWhitespace(text[..|text| - 1])| == 0 ||
           !Spec.IsWhitespace(
             Core.TrimRightWhitespace(text[..|text| - 1])[
             |Core.TrimRightWhitespace(text[..|text| - 1])| - 1
             ]
           ));
        assert Spec.WhitespaceOnly(trailing + [text[|text| - 1]]) by {
          reveal Spec.WhitespaceOnly();
        }
      } else {
        assert Spec.WhitespaceOnly("");
      }
    }
  }

  lemma TrimWhitespaceSatisfiesRelation(text: string)
    ensures Spec.TrimmedTokenRelation(text, Core.TrimWhitespace(text))
  {
    TrimRightWhitespaceRelation(text);
    var trailing: string :|
      text == Core.TrimRightWhitespace(text) + trailing &&
      Spec.WhitespaceOnly(trailing) &&
      (|Core.TrimRightWhitespace(text)| == 0 ||
       !Spec.IsWhitespace(
         Core.TrimRightWhitespace(text)[|Core.TrimRightWhitespace(text)| - 1]
       ));
    TrimLeftWhitespaceRelation(Core.TrimRightWhitespace(text));
    var leading: string :|
      Core.TrimRightWhitespace(text) ==
      leading + Core.TrimWhitespace(text) &&
      Spec.WhitespaceOnly(leading) &&
      (|Core.TrimWhitespace(text)| == 0 ||
       !Spec.IsWhitespace(Core.TrimWhitespace(text)[0]));
    reveal Spec.TrimmedTokenRelation();
    assert text == leading + Core.TrimWhitespace(text) + trailing;
    if |Core.TrimWhitespace(text)| > 0 {
      assert Core.TrimRightWhitespace(text) ==
             leading + Core.TrimWhitespace(text);
      assert Core.TrimWhitespace(text)[|Core.TrimWhitespace(text)| - 1] ==
             Core.TrimRightWhitespace(text)[|Core.TrimRightWhitespace(text)| - 1];
    }
  }

  lemma CountPrefixBounds(factors: seq<int>, p: int, i: nat)
    requires i <= |factors|
    ensures Core.CountPrefix(factors, p, i) <= |factors| - i
    ensures i < |factors| && factors[i] == p ==> 1 <= Core.CountPrefix(factors, p, i)
    decreases |factors| - i
  {
    if i < |factors| && factors[i] == p {
      CountPrefixBounds(factors, p, i + 1);
    }
  }

  lemma CountPrefixCharacterization(factors: seq<int>, p: int, i: nat)
    requires i <= |factors|
    ensures Core.CountPrefix(factors, p, i) <= |factors| - i
    ensures forall j :: i <= j < i + Core.CountPrefix(factors, p, i) ==>
                          factors[j] == p
    ensures i + Core.CountPrefix(factors, p, i) < |factors| ==>
              factors[i + Core.CountPrefix(factors, p, i)] != p
    decreases |factors| - i
  {
    CountPrefixBounds(factors, p, i);
    if i < |factors| && factors[i] == p {
      CountPrefixCharacterization(factors, p, i + 1);
      forall j | i <= j < i + Core.CountPrefix(factors, p, i)
        ensures factors[j] == p
      {
        assert j < |factors|;
        if j > i {
          assert i + Core.CountPrefix(factors, p, i) ==
                 i + 1 + Core.CountPrefix(factors, p, i + 1);
        }
      }
    }
  }

  lemma AllDigitsGivesDigitsFrom(text: string, start: nat)
    requires start < |text|
    requires Core.AllDigits(text, start)
    ensures Spec.DigitsFrom(text, start)
    decreases |text| - start
  {
    assert Core.IsDigit(text[start]);
    IsDigitEq(text[start]);
    if start + 1 < |text| {
      AllDigitsGivesDigitsFrom(text, start + 1);
    }
  }

  lemma ParseDigitsTrace(
    text: string,
    start: nat,
    i: nat,
    acc: int,
    prefixes: seq<int>
  )
    requires start < |text|
    requires start <= i <= |text|
    requires Core.AllDigits(text, start)
    requires Core.AllDigits(text, i)
    requires Spec.DigitsFrom(text, start)
    requires |prefixes| == i - start + 1
    requires prefixes[0] == 0
    requires prefixes[|prefixes| - 1] == acc
    requires forall j {:trigger prefixes[j + 1]} :: 0 <= j < i - start ==>
                                                      prefixes[j + 1] ==
                                                      prefixes[j] * 10 + (text[start + j] as int - '0' as int)
    ensures exists completed: seq<int> ::
              Spec.DecimalTrace(text, start, Core.ParseDigits(text, i, acc), completed)
    decreases |text| - i
  {
    if i == |text| {
      assert Core.ParseDigits(text, i, acc) == acc;
      assert Spec.DecimalTrace(text, start, acc, prefixes) by {
        reveal Spec.DigitsFrom();
      }
      assert exists completed: seq<int> ::
          Spec.DecimalTrace(
            text, start, Core.ParseDigits(text, i, acc), completed
          );
    } else {
      assert Core.AllDigits(text, i);
      assert Core.IsDigit(text[i]);
      assert Core.AllDigits(text, i + 1);
      IsDigitEq(text[i]);
      var nextAcc := acc * 10 + (text[i] as int - '0' as int);
      var nextPrefixes := prefixes + [nextAcc];
      assert forall j {:trigger nextPrefixes[j + 1]} ::
          0 <= j < i + 1 - start ==>
            nextPrefixes[j + 1] ==
            nextPrefixes[j] * 10 +
            (text[start + j] as int - '0' as int) by {
        forall j {:trigger nextPrefixes[j + 1]} | 0 <= j < i + 1 - start
          ensures nextPrefixes[j + 1] ==
                  nextPrefixes[j] * 10 +
                  (text[start + j] as int - '0' as int)
        {
          if j < i - start {
            assert prefixes[j + 1] ==
                   prefixes[j] * 10 +
                   (text[start + j] as int - '0' as int);
            assert nextPrefixes[j] == prefixes[j];
            assert nextPrefixes[j + 1] == prefixes[j + 1];
          } else {
            assert j == i - start;
            assert start + j == i;
            assert nextPrefixes[j] == acc;
            assert nextPrefixes[j + 1] == nextAcc;
          }
        }
      }
      ParseDigitsTrace(text, start, i + 1, nextAcc, nextPrefixes);
      assert Core.ParseDigits(text, i, acc) ==
             Core.ParseDigits(text, i + 1, nextAcc);
      var completed :| Spec.DecimalTrace(
          text, start, Core.ParseDigits(text, i + 1, nextAcc), completed
        );
      assert Spec.DecimalTrace(
          text, start, Core.ParseDigits(text, i, acc), completed
        );
    }
  }

  lemma ParseDigitsSatisfiesRelation(text: string, start: nat)
    requires start < |text|
    requires Core.AllDigits(text, start)
    ensures Spec.DecimalRelation(
              text, start, Core.ParseDigits(text, start, 0)
            )
  {
    AllDigitsGivesDigitsFrom(text, start);
    ParseDigitsTrace(text, start, start, 0, [0]);
  }

  lemma DigitsSatisfyCanonical(n: int)
    requires 0 <= n
    ensures Spec.CanonicalDecimalRelation(n, Core.Digits(n))
    decreases n
  {
    if n < 10 {
      var prefixes := [0, n];
      assert Core.DigitChar(n) as int - '0' as int == n;
      assert Spec.IsDigit(Core.DigitChar(n));
      assert Spec.DecimalTrace(Core.Digits(n), 0, n, prefixes);
    } else {
      var quotient := n / 10;
      var remainder := n % 10;
      DigitsSatisfyCanonical(quotient);
      var prefixText := Core.Digits(quotient);
      var prefixes :| Spec.DecimalTrace(prefixText, 0, quotient, prefixes);
      var digits := Core.Digits(n);
      var completed := prefixes + [n];
      assert n == quotient * 10 + remainder;
      assert 0 <= remainder < 10;
      assert Spec.IsDigit(Core.DigitChar(remainder));
      assert forall i {:trigger completed[i + 1]} :: 0 <= i < |digits| ==>
                                                       Spec.IsDigit(digits[i]) &&
                                                       completed[i + 1] ==
                                                       completed[i] * 10 + (digits[i] as int - '0' as int) by {
        forall i {:trigger completed[i + 1]} | 0 <= i < |digits|
          ensures Spec.IsDigit(digits[i]) &&
                  completed[i + 1] ==
                  completed[i] * 10 + (digits[i] as int - '0' as int)
        {
          if i < |prefixText| {
            assert digits[i] == prefixText[i];
            assert completed[i] == prefixes[i];
            assert completed[i + 1] == prefixes[i + 1];
          } else {
            assert i == |prefixText|;
            assert digits[i] == Core.DigitChar(remainder);
            assert completed[i] == quotient;
            assert completed[i + 1] == n;
            assert Core.DigitChar(remainder) as int - '0' as int == remainder;
          }
        }
      }
      assert Spec.DecimalTrace(digits, 0, n, completed);
      reveal Spec.CanonicalDecimalRelation();
      assert quotient > 0;
      assert prefixText[0] != '0' by {
        if prefixText[0] == '0' {
          if |prefixText| > 1 {
          } else {
            assert |prefixText| == 1;
            forall j | 1 <= j <= |prefixText|
              ensures prefixes[j] == prefixes[j - 1] * 10 +
                (prefixText[j - 1] as int - '0' as int)
            {
            }
            assert prefixes[1] ==
                   prefixes[0] * 10 +
                   (prefixText[0] as int - '0' as int);
            assert quotient == 0;
          }
        }
      }
      assert digits[0] == prefixText[0];
    }
  }

  ghost predicate NoDivisorBelow(value: int, bound: int)
  {
    forall divisor :: 2 <= divisor < bound ==> !Spec.Divides(divisor, value)
  }

  lemma RemainderZeroGivesDivides(value: int, divisor: int)
    requires 0 <= value
    requires 0 < divisor
    requires value % divisor == 0
    ensures Spec.Divides(divisor, value)
  {
    var quotient := value / divisor;
    assert 0 <= quotient;
    assert value == divisor * quotient + value % divisor;
    assert value == divisor * quotient;
    assert exists q: nat :: value == divisor * q;
  }

  lemma RemainderNonzeroRejectsDivides(value: int, divisor: int)
    requires 0 < divisor
    requires value % divisor != 0
    ensures !Spec.Divides(divisor, value)
  {
    if Spec.Divides(divisor, value) {
      var quotient :| value == divisor * quotient;
      MultipleHasZeroRemainder(divisor, quotient);
      assert value % divisor == (divisor * quotient) % divisor;
    }
  }

  lemma FundamentalDivision(value: int, divisor: int)
    requires divisor != 0
    ensures value ==
            divisor * (value / divisor) + value % divisor
  {
  }

  lemma RemainderRange(value: int, divisor: int)
    requires divisor > 0
    ensures 0 <= value % divisor < divisor
  {
  }

  lemma AddDenominatorRemainder(divisor: int, value: int)
    requires divisor > 0
    ensures (value + divisor) % divisor == value % divisor
  {
    FundamentalDivision(value, divisor);
    FundamentalDivision(value + divisor, divisor);
    RemainderRange(value, divisor);
    RemainderRange(value + divisor, divisor);
    var quotientDifference :=
      (value + divisor) / divisor - value / divisor - 1;
    assert 0 == divisor * quotientDifference +
                (value + divisor) % divisor - value % divisor;
    if quotientDifference > 0 {
      assert divisor <= divisor * quotientDifference;
    }
    if quotientDifference < 0 {
      assert divisor * quotientDifference <= -divisor;
    }
  }

  lemma MultipleHasZeroRemainder(
    divisor: int, quotient: nat
  )
    requires 0 < divisor
    ensures (divisor * quotient) % divisor == 0
    decreases quotient
  {
    if quotient > 0 {
      MultipleHasZeroRemainder(divisor, quotient - 1);
      assert divisor * quotient ==
             divisor * (quotient - 1) + divisor;
      AddDenominatorRemainder(
        divisor, divisor * (quotient - 1)
      );
    } else {
      RemainderRange(0, divisor);
    }
  }

  lemma DividesTransitive(value: int, middle: int, divisor: int)
    requires Spec.Divides(divisor, middle)
    requires Spec.Divides(middle, value)
    ensures Spec.Divides(divisor, value)
  {
    var first :| middle == divisor * first;
    var second :| value == middle * second;
    assert value == divisor * (first * second);
  }

  lemma QuotientKeepsNoSmallDivisor(value: int, divisor: int)
    requires 2 <= divisor
    requires value % divisor == 0
    requires NoDivisorBelow(value, divisor)
    ensures NoDivisorBelow(value / divisor, divisor)
  {
    forall candidate | 2 <= candidate < divisor
      ensures !Spec.Divides(candidate, value / divisor)
    {
      if Spec.Divides(candidate, value / divisor) {
        var quotient :| value / divisor == candidate * quotient;
        assert value == divisor * (value / divisor);
        assert value == candidate * (divisor * quotient);
        assert Spec.Divides(candidate, value);
        assert false;
      }
    }
  }

  lemma AdvanceNoDivisor(value: int, divisor: int)
    requires divisor == 2 || (3 <= divisor && divisor % 2 == 1)
    requires NoDivisorBelow(value, divisor)
    requires value % divisor != 0
    ensures NoDivisorBelow(
              value, if divisor == 2 then 3 else divisor + 2
            )
  {
    RemainderNonzeroRejectsDivides(value, divisor);
    var next := if divisor == 2 then 3 else divisor + 2;
    forall candidate | 2 <= candidate < next
      ensures !Spec.Divides(candidate, value)
    {
      if candidate < divisor {
      } else if candidate == divisor {
      } else {
        assert divisor != 2;
        assert candidate == divisor + 1;
        assert candidate % 2 == 0;
        if Spec.Divides(candidate, value) {
          var quotient :| value == candidate * quotient;
          assert candidate == 2 * (candidate / 2);
          assert value == 2 * ((candidate / 2) * quotient);
          assert Spec.Divides(2, value);
          assert false;
        }
      }
    }
  }

  lemma PrimeAtFoundDivisor(value: int, divisor: int)
    requires 0 <= value
    requires 2 <= divisor
    requires value % divisor == 0
    requires NoDivisorBelow(value, divisor)
    ensures Spec.Prime(divisor)
  {
    RemainderZeroGivesDivides(value, divisor);
    forall candidate | 2 <= candidate && candidate * candidate <= divisor
      ensures !Spec.Divides(candidate, divisor)
    {
      if Spec.Divides(candidate, divisor) {
        assert candidate < divisor by {
          if candidate >= divisor {
            assert 0 <= (candidate - divisor) * (candidate + divisor);
            assert candidate * candidate - divisor * divisor ==
                   (candidate - divisor) * (candidate + divisor);
            assert candidate * candidate >= divisor * divisor;
            assert divisor * divisor > divisor;
          }
        }
        DividesTransitive(value, divisor, candidate);
        assert false;
      }
    }
  }

  lemma PrimePastSquare(value: int, divisor: int)
    requires 2 <= value
    requires 2 <= divisor
    requires divisor * divisor > value
    requires NoDivisorBelow(value, divisor)
    ensures Spec.Prime(value)
  {
    forall candidate | 2 <= candidate && candidate * candidate <= value
      ensures !Spec.Divides(candidate, value)
    {
      assert candidate < divisor by {
        if candidate >= divisor {
          SquareMonotone(divisor, candidate);
        }
      }
    }
  }

  lemma SquareMonotone(lower: int, upper: int)
    requires 0 <= lower <= upper
    ensures lower * lower <= upper * upper
  {
    assert 0 <= (upper - lower) * (upper + lower);
    assert upper * upper - lower * lower ==
           (upper - lower) * (upper + lower);
  }

  lemma CancelPositiveFactor(factor: int, left: int, right: int)
    requires 0 < factor
    requires factor * left <= factor * right
    ensures left <= right
  {
    if left > right {
      assert 0 < factor * (left - right);
      assert factor * left - factor * right == factor * (left - right);
    }
  }

  lemma ProductSplit(values: seq<int>, i: nat)
    requires i <= |values|
    ensures Spec.Product(values) ==
            Spec.Product(values[..i]) * Spec.Product(values[i..])
    decreases i
  {
    if i > 0 {
      ProductSplit(values[1..], i - 1);
      assert values[..i] == [values[0]] + values[1..i];
      assert values[i..] == values[1..][i - 1..];
      assert values[1..][..i - 1] == values[1..i];
      calc {
          Spec.Product(values);
      ==  values[0] * Spec.Product(values[1..]);
      ==  values[0] *
          (Spec.Product(values[1..i]) * Spec.Product(values[i..]));
      ==  (values[0] * Spec.Product(values[1..i])) *
          Spec.Product(values[i..]);
      ==  Spec.Product(values[..i]) * Spec.Product(values[i..]);
      }
    }
  }

  lemma ProductPositive(values: seq<int>)
    requires forall i :: 0 <= i < |values| ==> 1 <= values[i]
    ensures 1 <= Spec.Product(values)
    decreases |values|
  {
    if |values| > 0 {
      ProductPositive(values[1..]);
    }
  }

  lemma NondecreasingBetween(values: seq<int>, i: nat, j: nat)
    requires Spec.Nondecreasing(values)
    requires i <= j < |values|
    ensures values[i] <= values[j]
    decreases j - i
  {
    if i < j {
      NondecreasingBetween(values, i + 1, j);
      assert values[i] <= values[i + 1];
    }
  }

  lemma NondecreasingGivesSuffixMinimums(values: seq<int>)
    requires Spec.Nondecreasing(values)
    ensures Spec.SuffixMinimums(values)
  {
    forall i, j | 0 <= i <= j < |values|
      ensures values[i] <= values[j]
    {
      NondecreasingBetween(values, i, j);
    }
  }

  lemma FactorizationFactorsAtLeast(
    value: int, factors: seq<int>, bound: int
  )
    requires Spec.PrimeFactorizationRelation(value, factors)
    requires NoDivisorBelow(value, bound)
    ensures forall i :: 0 <= i < |factors| ==> bound <= factors[i]
  {
    forall i | 0 <= i < |factors|
      ensures bound <= factors[i]
    {
      if factors[i] < bound {
        ProductSplit(factors, i);
        assert forall j :: 0 <= j < |factors| ==> 1 <= factors[j] by {
          forall j | 0 <= j < |factors|
            ensures 1 <= factors[j]
          {
            assert Spec.Prime(factors[j]);
          }
        }
        ProductPositive(factors[..i]);
        ProductPositive(factors[i + 1..]);
        assert Spec.Product(factors[i..]) ==
               factors[i] * Spec.Product(factors[i + 1..]);
        assert value == Spec.Product(factors[..i]) *
                        (factors[i] * Spec.Product(factors[i + 1..]));
        assert value == factors[i] *
                        (Spec.Product(factors[..i]) * Spec.Product(factors[i + 1..]));
        assert 0 <= Spec.Product(factors[..i]) *
                    Spec.Product(factors[i + 1..]);
        assert exists quotient: nat ::
            value == factors[i] * quotient;
        assert Spec.Divides(factors[i], value);
        assert Spec.Prime(factors[i]);
        assert 2 <= factors[i];
        assert false;
      }
    }
  }

  lemma PrependPrimeFactorization(
    value: int,
    divisor: int,
    quotient: int,
    factors: seq<int>
  )
    requires value == divisor * quotient
    requires Spec.Prime(divisor)
    requires Spec.PrimeFactorizationRelation(quotient, factors)
    requires forall i :: 0 <= i < |factors| ==> divisor <= factors[i]
    ensures Spec.PrimeFactorizationRelation(value, [divisor] + factors)
  {
    assert Spec.Product([divisor] + factors) ==
           divisor * Spec.Product(factors);
    assert forall i :: 0 <= i < |[divisor] + factors| ==>
                         Spec.Prime(([divisor] + factors)[i]) by {
      forall i | 0 <= i < |[divisor] + factors|
        ensures Spec.Prime(([divisor] + factors)[i])
      {
        if i > 0 {
          assert ([divisor] + factors)[i] == factors[i - 1];
        }
      }
    }
    assert Spec.Nondecreasing([divisor] + factors) by {
      forall i | 0 <= i && i + 1 < |[divisor] + factors|
        ensures ([divisor] + factors)[i] <=
                ([divisor] + factors)[i + 1]
      {
        if i == 0 {
        } else {
          assert ([divisor] + factors)[i] == factors[i - 1];
          assert ([divisor] + factors)[i + 1] == factors[i];
        }
      }
    }
    NondecreasingGivesSuffixMinimums([divisor] + factors);
  }

  lemma FactorizeFromSatisfiesRelation(value: int, divisor: int)
    requires value > 1
    requires divisor == 2 || (3 <= divisor && divisor % 2 == 1)
    requires NoDivisorBelow(value, divisor)
    ensures Spec.PrimeFactorizationRelation(
              value, Core.FactorizeFrom(value, divisor)
            )
    decreases value, value - divisor
  {
    if divisor * divisor > value {
      PrimePastSquare(value, divisor);
      assert Spec.Product([value]) == value;
      assert Spec.Nondecreasing([value]);
      assert Spec.SuffixMinimums([value]);
    } else if value % divisor == 0 {
      Core.FactorizeQuotientSmaller(value, divisor);
      var quotient := value / divisor;
      assert value == divisor * quotient;
      CancelPositiveFactor(divisor, divisor, quotient);
      assert quotient >= divisor;
      FactorizeFromSatisfiesRelation(quotient, 2);
      assert Core.FactorizeFrom(quotient, 2) == Core.Factorize(quotient);
      var factors := Core.Factorize(quotient);
      PrimeAtFoundDivisor(value, divisor);
      QuotientKeepsNoSmallDivisor(value, divisor);
      FactorizationFactorsAtLeast(quotient, factors, divisor);
      PrependPrimeFactorization(value, divisor, quotient, factors);
    } else if divisor == 2 {
      AdvanceNoDivisor(value, divisor);
      FactorizeFromSatisfiesRelation(value, 3);
    } else {
      AdvanceNoDivisor(value, divisor);
      FactorizeFromSatisfiesRelation(value, divisor + 2);
    }
  }

  lemma FactorizeSatisfiesRelation(value: int)
    requires value > 1
    ensures Spec.PrimeFactorizationRelation(value, Core.Factorize(value))
  {
    FactorizeFromSatisfiesRelation(value, 2);
  }

  ghost function ShiftCuts(cuts: seq<nat>, amount: nat): seq<nat>
  {
    seq(|cuts|, i requires 0 <= i < |cuts| => cuts[i] + amount)
  }

  lemma ShiftCutsIndex(cuts: seq<nat>, amount: nat, index: nat)
    requires index < |cuts|
    ensures ShiftCuts(cuts, amount)[index] == cuts[index] + amount
  {
  }

  lemma PrependSlice<T>(
    head: seq<T>, tail: seq<T>, start: nat, end: nat
  )
    requires start <= end <= |tail|
    ensures (head + tail)[|head| + start..|head| + end] ==
            tail[start..end]
  {
  }

  lemma {:isolate_assertions} PrependFragment(
    head: BW.Bytes,
    tailFragments: seq<BW.Bytes>,
    tail: BW.Bytes,
    tailCuts: seq<nat>
  )
    requires Spec.FragmentsConcatenate(tailFragments, tail, tailCuts)
    ensures Spec.FragmentsConcatenate(
              [head] + tailFragments,
              head + tail,
              [0] + ShiftCuts(tailCuts, |head|)
            )
  {
    reveal Spec.FragmentsConcatenate();
    forall i: nat {:trigger ([0] + ShiftCuts(tailCuts, |head|))[i]} |
      i < |[head] + tailFragments|
      ensures ([0] + ShiftCuts(tailCuts, |head|))[i] <=
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] <= |head + tail| &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] ==
              ([0] + ShiftCuts(tailCuts, |head|))[i] +
              |([head] + tailFragments)[i]| &&
              (head + tail)[
              ([0] + ShiftCuts(tailCuts, |head|))[i]..
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1]
              ] == ([head] + tailFragments)[i]
    {
      ShiftCutsIndex(tailCuts, |head|, i);
      if i == 0 {
        assert ([0] + ShiftCuts(tailCuts, |head|))[1] == |head|;
      } else {
        ShiftCutsIndex(tailCuts, |head|, i - 1);
        var k := i - 1;
        PrependSlice(head, tail, tailCuts[k], tailCuts[k + 1]);
      }
    }
  }

  lemma LiftFactorPiece(
    factors: seq<int>,
    offset: nat,
    lo: nat,
    hi: nat,
    exponents: bool,
    piece: BW.Bytes
  )
    requires offset <= |factors|
    requires Spec.FactorPieceRelation(
               factors[offset..], lo, hi, exponents, piece
             )
    requires exponents && lo == 0 && offset > 0 ==>
               factors[offset - 1] != factors[offset]
    ensures Spec.FactorPieceRelation(
              factors, offset + lo, offset + hi, exponents, piece
            )
  {
    reveal Spec.FactorPieceRelation();
    assert offset + hi <= |factors|;
    if exponents {
      assert forall i :: offset + lo <= i < offset + hi ==>
                           factors[i] == factors[offset + lo] by {
        forall i | offset + lo <= i < offset + hi
          ensures factors[i] == factors[offset + lo]
        {
          var tailIndex := i - offset;
          assert factors[i] == factors[offset..][tailIndex];
          assert factors[offset + lo] == factors[offset..][lo];
        }
      }
      if offset + lo > 0 {
        if lo > 0 {
          assert factors[offset + lo - 1] ==
                 factors[offset..][lo - 1];
          assert factors[offset + lo] == factors[offset..][lo];
        } else {
          assert offset + lo == offset;
        }
      }
      if offset + hi < |factors| {
        assert hi < |factors[offset..]|;
        assert factors[offset + hi] == factors[offset..][hi];
        assert factors[offset + lo] == factors[offset..][lo];
      }
    }
  }

  lemma {:isolate_assertions} LiftFactorPieces(
    factors: seq<int>,
    offset: nat,
    tailCuts: seq<nat>,
    pieces: seq<BW.Bytes>,
    exponents: bool
  )
    requires offset <= |factors|
    requires |tailCuts| == |pieces| + 1
    requires forall i :: 0 <= i < |pieces| ==>
                           Spec.FactorPieceRelation(
                             factors[offset..], tailCuts[i], tailCuts[i + 1],
                             exponents, pieces[i]
                           )
    requires exponents && offset > 0 ==> offset < |factors|
    requires exponents && offset > 0 ==>
               factors[offset - 1] != factors[offset]
    ensures forall i :: 0 <= i < |pieces| ==>
                          Spec.FactorPieceRelation(
                            factors,
                            ShiftCuts(tailCuts, offset)[i],
                            ShiftCuts(tailCuts, offset)[i + 1],
                            exponents,
                            pieces[i]
                          )
  {
    forall i | 0 <= i < |pieces|
      ensures Spec.FactorPieceRelation(
                factors,
                ShiftCuts(tailCuts, offset)[i],
                ShiftCuts(tailCuts, offset)[i + 1],
                exponents,
                pieces[i]
              )
    {
      ShiftCutsIndex(tailCuts, offset, i);
      ShiftCutsIndex(tailCuts, offset, i + 1);
      LiftFactorPiece(
        factors, offset, tailCuts[i], tailCuts[i + 1],
        exponents, pieces[i]
      );
    }
  }

  lemma PartitionGivesFactorOutputRelation(
    factors: seq<int>,
    exponents: bool,
    output: BW.Bytes,
    factorCuts: seq<nat>,
    pieces: seq<BW.Bytes>,
    outputCuts: seq<nat>,
    fragments: seq<BW.Bytes>
  )
    requires Spec.FactorOutputPartition(
               factors, exponents, output,
               factorCuts, pieces, outputCuts, fragments
             )
    ensures Spec.FactorOutputRelation(factors, exponents, output)
  {
    reveal Spec.FactorOutputRelation();
  }

  lemma {:isolate_assertions} RenderFactorsSatisfiesRelation(
    factors: seq<int>, exponents: bool
  )
    requires |factors| > 0
    requires forall i :: 0 <= i < |factors| ==> 0 <= factors[i]
    ensures Spec.FactorOutputRelation(
              factors, exponents, Core.RenderFactors(factors, exponents)
            )
    decreases |factors|
  {
    if !exponents {
      var headText := Core.Digits(factors[0]);
      DigitsSatisfyCanonical(factors[0]);
      if |factors| == 1 {
        var factorCuts: seq<nat> := [0, 1];
        var pieces := [headText];
        var outputCuts: seq<nat> := [0, |headText|];
        var fragments := [headText];
        assert Spec.FragmentsConcatenate(
            fragments, headText, outputCuts
          );
        assert Spec.FactorOutputPartition(
            factors, false, headText,
            factorCuts, pieces, outputCuts, fragments
          );
        PartitionGivesFactorOutputRelation(
          factors, false, headText,
          factorCuts, pieces, outputCuts, fragments
        );
      } else {
        var tailFactors := factors[1..];
        RenderFactorsSatisfiesRelation(tailFactors, false);
        var tailOutput := Core.RenderFactors(tailFactors, false);
        var tailFactorCuts: seq<nat>,
            tailPieces: seq<BW.Bytes>,
            tailOutputCuts: seq<nat>,
            tailFragments: seq<BW.Bytes> :|
          Spec.FactorOutputPartition(
            tailFactors, false, tailOutput,
            tailFactorCuts, tailPieces, tailOutputCuts, tailFragments
          );
        reveal Spec.FactorOutputPartition();
        var headFragment := headText + [' '];
        var factorCuts := [0] + ShiftCuts(tailFactorCuts, 1);
        var pieces := [headText] + tailPieces;
        var fragments := [headFragment] + tailFragments;
        var outputCuts := [0] +
        ShiftCuts(tailOutputCuts, |headFragment|);
        PrependFragment(
          headFragment, tailFragments, tailOutput, tailOutputCuts
        );
        LiftFactorPieces(
          factors, 1, tailFactorCuts, tailPieces, false
        );
        assert forall i :: 0 <= i < |pieces| ==>
                             Spec.FactorPieceRelation(
                               factors, factorCuts[i], factorCuts[i + 1], false, pieces[i]
                             ) by {
          forall i | 0 <= i < |pieces|
            ensures Spec.FactorPieceRelation(
                      factors, factorCuts[i], factorCuts[i + 1], false, pieces[i]
                    )
          {
            if i == 0 {
              ShiftCutsIndex(tailFactorCuts, 1, 0);
            } else {
              assert factorCuts[i] ==
                     ShiftCuts(tailFactorCuts, 1)[i - 1];
              assert factorCuts[i + 1] ==
                     ShiftCuts(tailFactorCuts, 1)[i];
            }
          }
        }
        assert forall i :: 0 <= i < |pieces| ==>
                             fragments[i] == pieces[i] +
                             (if i + 1 < |pieces| then [' '] else []) by {
          forall i | 0 <= i < |pieces|
            ensures fragments[i] == pieces[i] +
                                    (if i + 1 < |pieces| then [' '] else [])
          {
            if i > 0 {
              assert fragments[i] == tailFragments[i - 1];
              assert pieces[i] == tailPieces[i - 1];
            }
          }
        }
        assert Spec.FactorOutputPartition(
            factors, false, headFragment + tailOutput,
            factorCuts, pieces, outputCuts, fragments
          );
        PartitionGivesFactorOutputRelation(
          factors, false, headFragment + tailOutput,
          factorCuts, pieces, outputCuts, fragments
        );
      }
    } else {
      var prime := factors[0];
      var count := Core.CountPrefix(factors, prime, 0);
      CountPrefixBounds(factors, prime, 0);
      CountPrefixCharacterization(factors, prime, 0);
      assert 1 <= count <= |factors|;
      var primeText := Core.Digits(prime);
      DigitsSatisfyCanonical(prime);
      var current: BW.Bytes;
      if count == 1 {
        current := primeText;
      } else {
        var countText := Core.Digits(count);
        DigitsSatisfyCanonical(count);
        current := primeText + ['^'] + countText;
      }
      assert Spec.FactorPieceRelation(
          factors, 0, count, true, current
        ) by {
        reveal Spec.FactorPieceRelation();
      }
      if count == |factors| {
        var factorCuts := [0, count];
        var pieces := [current];
        var outputCuts := [0, |current|];
        var fragments := [current];
        assert Spec.FragmentsConcatenate(
            fragments, current, outputCuts
          );
        assert Spec.FactorOutputPartition(
            factors, true, current,
            factorCuts, pieces, outputCuts, fragments
          );
        PartitionGivesFactorOutputRelation(
          factors, true, current,
          factorCuts, pieces, outputCuts, fragments
        );
      } else {
        var tailFactors := factors[count..];
        RenderFactorsSatisfiesRelation(tailFactors, true);
        var tailOutput := Core.RenderFactors(tailFactors, true);
        var tailFactorCuts: seq<nat>,
            tailPieces: seq<BW.Bytes>,
            tailOutputCuts: seq<nat>,
            tailFragments: seq<BW.Bytes> :|
          Spec.FactorOutputPartition(
            tailFactors, true, tailOutput,
            tailFactorCuts, tailPieces, tailOutputCuts, tailFragments
          );
        reveal Spec.FactorOutputPartition();
        var headFragment := current + [' '];
        var factorCuts := [0] + ShiftCuts(tailFactorCuts, count);
        var pieces := [current] + tailPieces;
        var fragments := [headFragment] + tailFragments;
        var outputCuts := [0] +
        ShiftCuts(tailOutputCuts, |headFragment|);
        PrependFragment(
          headFragment, tailFragments, tailOutput, tailOutputCuts
        );
        assert factors[count - 1] != factors[count];
        LiftFactorPieces(
          factors, count, tailFactorCuts, tailPieces, true
        );
        assert forall i :: 0 <= i < |pieces| ==>
                             Spec.FactorPieceRelation(
                               factors, factorCuts[i], factorCuts[i + 1], true, pieces[i]
                             ) by {
          forall i | 0 <= i < |pieces|
            ensures Spec.FactorPieceRelation(
                      factors, factorCuts[i], factorCuts[i + 1], true, pieces[i]
                    )
          {
            if i == 0 {
              ShiftCutsIndex(tailFactorCuts, count, 0);
            } else {
              assert factorCuts[i] ==
                     ShiftCuts(tailFactorCuts, count)[i - 1];
              assert factorCuts[i + 1] ==
                     ShiftCuts(tailFactorCuts, count)[i];
            }
          }
        }
        assert forall i :: 0 <= i < |pieces| ==>
                             fragments[i] == pieces[i] +
                             (if i + 1 < |pieces| then [' '] else []) by {
          forall i | 0 <= i < |pieces|
            ensures fragments[i] == pieces[i] +
                                    (if i + 1 < |pieces| then [' '] else [])
          {
            if i > 0 {
              assert fragments[i] == tailFragments[i - 1];
              assert pieces[i] == tailPieces[i - 1];
            }
          }
        }
        assert |factorCuts| == |pieces| + 1;
        assert factorCuts[0] == 0;
        assert factorCuts[|factorCuts| - 1] == |factors| by {
          ShiftCutsIndex(
            tailFactorCuts, count, |tailFactorCuts| - 1
          );
        }
        assert forall i :: 0 <= i < |pieces| ==>
                             factorCuts[i] < factorCuts[i + 1] by {
          forall i | 0 <= i < |pieces|
            ensures factorCuts[i] < factorCuts[i + 1]
          {
            if i == 0 {
              ShiftCutsIndex(tailFactorCuts, count, 0);
              assert tailFactorCuts[0] == 0;
            } else {
              ShiftCutsIndex(tailFactorCuts, count, i - 1);
              ShiftCutsIndex(tailFactorCuts, count, i);
              assert tailFactorCuts[i - 1] < tailFactorCuts[i];
            }
          }
        }
        assert Spec.FactorOutputPartition(
            factors, true, headFragment + tailOutput,
            factorCuts, pieces, outputCuts, fragments
          );
        PartitionGivesFactorOutputRelation(
          factors, true, headFragment + tailOutput,
          factorCuts, pieces, outputCuts, fragments
        );
      }
    }
  }

  lemma RenderValidValueSatisfiesRelation(value: int, exponents: bool)
    requires 0 <= value
    ensures Spec.ValueOutputRelation(
              value, exponents, Core.RenderValidValue(value, exponents)
            )
  {
    var valueText := Core.Digits(value);
    DigitsSatisfyCanonical(value);
    if value <= 1 {
    } else {
      var factors := Core.Factorize(value);
      FactorizeSatisfiesRelation(value);
      assert forall i :: 0 <= i < |factors| ==> 0 <= factors[i] by {
        forall i | 0 <= i < |factors|
          ensures 0 <= factors[i]
        {
          assert Spec.Prime(factors[i]);
        }
      }
      RenderFactorsSatisfiesRelation(factors, exponents);
    }
  }

  lemma DigitsFromGivesAllDigits(text: string, start: nat)
    requires Spec.DigitsFrom(text, start)
    ensures Core.AllDigits(text, start)
    decreases |text| - start
  {
    reveal Spec.DigitsFrom();
    IsDigitEq(text[start]);
    if start + 1 < |text| {
      assert Spec.DigitsFrom(text, start + 1);
      DigitsFromGivesAllDigits(text, start + 1);
    }
  }

  lemma AllDigitsIffDigitsFrom(text: string, start: nat)
    requires start < |text|
    ensures Core.AllDigits(text, start) == Spec.DigitsFrom(text, start)
  {
    if Core.AllDigits(text, start) {
      AllDigitsGivesDigitsFrom(text, start);
    } else if Spec.DigitsFrom(text, start) {
      DigitsFromGivesAllDigits(text, start);
    }
  }

  lemma ProcessTokenSatisfiesRelation(token: string, exponents: bool)
    ensures Core.ProcessToken(token, exponents).TokenOk? ==>
              Spec.TokenRelation(
                token, exponents,
                Core.ProcessToken(token, exponents).out, [], false
              )
    ensures Core.ProcessToken(token, exponents).TokenErr? ==>
              Spec.TokenRelation(
                token, exponents,
                [], Core.ProcessToken(token, exponents).err, true
              )
  {
    TrimWhitespaceSatisfiesRelation(token);
    var trimmed := Core.TrimWhitespace(token);
    if |trimmed| == 0 {
    } else if trimmed[0] == '-' {
    } else {
      var start: nat := if trimmed[0] == '+' then 1 else 0;
      if trimmed[0] == '+' && |trimmed| == 1 {
        assert !Spec.DigitsFrom(trimmed, start);
      } else {
        assert start < |trimmed|;
        AllDigitsIffDigitsFrom(trimmed, start);
        if Core.AllDigits(trimmed, start) {
          ParseDigitsSatisfiesRelation(trimmed, start);
          var value := Core.ParseDigits(trimmed, start, 0);
          assert 0 <= value;
          RenderValidValueSatisfiesRelation(value, exponents);
        }
      }
    }
  }

  lemma RunTokensSatisfiesRelation(
    tokens: seq<string>, exponents: bool
  )
    ensures Spec.RunRelation(
              tokens,
              exponents,
              Core.RunTokens(tokens, exponents).stdout,
              Core.RunTokens(tokens, exponents).stderr,
              Core.RunTokens(tokens, exponents).hadError
            )
    decreases |tokens|
  {
    if |tokens| == 0 {
      reveal Spec.RunRelation();
    } else {
      ProcessTokenSatisfiesRelation(tokens[0], exponents);
      RunTokensSatisfiesRelation(tokens[1..], exponents);
      var head := Core.ProcessToken(tokens[0], exponents);
      var tail := Core.RunTokens(tokens[1..], exponents);
      var headOutput: BW.Bytes;
      var headError: BW.Bytes;
      var headHadError: bool;
      if head.TokenOk? {
        headOutput := head.out;
        headError := [];
        headHadError := false;
      } else {
        headOutput := [];
        headError := head.err;
        headHadError := true;
      }
      reveal Spec.RunRelation();
    }
  }

  lemma WordEndSatisfiesRelation(text: BW.Bytes, i: nat)
    requires i <= |text|
    ensures i <= Core.WordEnd(text, i) <= |text|
    ensures (i < |text| &&
             !Spec.IsWhitespace(text[i]) && text[i] != '\0') ==>
              i < Core.WordEnd(text, i)
    ensures forall j :: i <= j < Core.WordEnd(text, i) ==>
                          !Spec.IsWhitespace(text[j]) && text[j] != '\0'
    ensures Core.WordEnd(text, i) == |text| ||
            Spec.IsWhitespace(text[Core.WordEnd(text, i)]) ||
            text[Core.WordEnd(text, i)] == '\0'
    decreases |text| - i
  {
    if i < |text| {
      IsWhitespaceEq(text[i]);
      if !Core.IsWhitespace(text[i]) && text[i] != '\0' {
        WordEndSatisfiesRelation(text, i + 1);
        assert forall j :: i <= j < Core.WordEnd(text, i) ==>
                             !Spec.IsWhitespace(text[j]) && text[j] != '\0' by {
          forall j | i <= j < Core.WordEnd(text, i)
            ensures !Spec.IsWhitespace(text[j]) && text[j] != '\0'
          {
            if j == i {
              assert !Spec.IsWhitespace(text[j]);
            }
          }
        }
      }
    }
  }

  lemma SkipAfterNulSatisfiesRelation(text: BW.Bytes, i: nat)
    requires i < |text|
    ensures Spec.NulTailRelation(text, i, Core.SkipAfterNul(text, i))
    decreases |text| - i
  {
    IsWhitespaceEq(text[i]);
    if Core.IsWhitespace(text[i]) {
      reveal Spec.NulTailRelation();
    } else if i + 1 == |text| {
      reveal Spec.NulTailRelation();
    } else {
      SkipAfterNulSatisfiesRelation(text, i + 1);
      reveal Spec.NulTailRelation();
      var next := Core.SkipAfterNul(text, i + 1);
      assert forall j :: i <= j < next - 1 ==>
                           !Spec.IsWhitespace(text[j]) by {
        forall j | i <= j < next - 1
          ensures !Spec.IsWhitespace(text[j])
        {
          if j == i {
            assert !Spec.IsWhitespace(text[j]);
          }
        }
      }
      if next == |text| &&
         !Spec.IsWhitespace(text[next - 1]) {
        assert forall j :: i <= j < next ==>
                             !Spec.IsWhitespace(text[j]) by {
          forall j | i <= j < next
            ensures !Spec.IsWhitespace(text[j])
          {
            if j == i {
              assert !Spec.IsWhitespace(text[j]);
            }
          }
        }
      }
    }
  }

  lemma LiftInputPartitionOverWhitespace(
    text: BW.Bytes,
    i: nat,
    tokens: seq<string>,
    cursors: seq<nat>,
    starts: seq<nat>,
    ends: seq<nat>
  )
    requires i < |text|
    requires Spec.IsWhitespace(text[i])
    requires Spec.InputTokenPartitionFrom(
               text, i + 1, tokens, cursors, starts, ends
             )
    ensures Spec.InputTokensFromRelation(text, i, tokens)
  {
    reveal Spec.InputTokenPartitionFrom();
    reveal Spec.InputTokensFromRelation();
    if |tokens| == 0 {
      assert forall j :: i <= j < |text| ==>
                           Spec.IsWhitespace(text[j]) by {
        forall j | i <= j < |text|
          ensures Spec.IsWhitespace(text[j])
        {
          if j == i {
          }
        }
      }
      assert Spec.InputTokenPartitionFrom(
          text, i, tokens, [i], starts, ends
        );
    } else {
      var liftedCursors := [i] + cursors[1..];
      assert forall k :: 0 <= k < |tokens| ==>
                           Spec.InputTokenItemRelation(
                             text, tokens[k],
                             liftedCursors[k], starts[k], ends[k],
                             liftedCursors[k + 1]
                           ) by {
        forall k | 0 <= k < |tokens|
          ensures Spec.InputTokenItemRelation(
                    text, tokens[k],
                    liftedCursors[k], starts[k], ends[k],
                    liftedCursors[k + 1]
                  )
        {
          assert Spec.InputTokenItemRelation(
              text, tokens[k],
              cursors[k], starts[k], ends[k], cursors[k + 1]
            );
          if k == 0 {
            reveal Spec.InputTokenItemRelation();
            assert forall j :: i <= j < starts[0] ==>
                                 Spec.IsWhitespace(text[j]) by {
              forall j | i <= j < starts[0]
                ensures Spec.IsWhitespace(text[j])
              {
                if j == i {
                }
              }
            }
          } else {
            assert liftedCursors[k] == cursors[k];
          }
          assert liftedCursors[k + 1] == cursors[k + 1];
        }
      }
      assert Spec.InputTokenPartitionFrom(
          text, i, tokens, liftedCursors, starts, ends
        );
    }
  }

  lemma PrependInputTokenPartition(
    text: BW.Bytes,
    i: nat,
    end: nat,
    next: nat,
    token: string,
    tailTokens: seq<string>,
    cursors: seq<nat>,
    starts: seq<nat>,
    ends: seq<nat>
  )
    requires i < |text|
    requires !Spec.IsWhitespace(text[i])
    requires Spec.InputTokenPartitionFrom(
               text, next, tailTokens, cursors, starts, ends
             )
    requires if text[i] == '\0' then
               end == i && token == "" &&
               Spec.NulTailRelation(text, i, next)
             else
               i < end <= |text| &&
               token == text[i..end] &&
               (forall j :: i <= j < end ==>
                              !Spec.IsWhitespace(text[j]) && text[j] != '\0') &&
               (end == |text| ||
                Spec.IsWhitespace(text[end]) ||
                text[end] == '\0') &&
               (if end < |text| && text[end] == '\0'
                then Spec.NulTailRelation(text, end, next)
                else next == end)
    ensures Spec.InputTokensFromRelation(
              text, i, [token] + tailTokens
            )
  {
    reveal Spec.InputTokenPartitionFrom();
    reveal Spec.InputTokensFromRelation();
    var newCursors := [i] + cursors;
    var newStarts := [i] + starts;
    var newEnds := [end] + ends;
    assert forall k :: 0 <= k < |[token] + tailTokens| ==>
                         Spec.InputTokenItemRelation(
                           text, ([token] + tailTokens)[k],
                           newCursors[k], newStarts[k], newEnds[k],
                           newCursors[k + 1]
                         ) by {
      forall k | 0 <= k < |[token] + tailTokens|
        ensures Spec.InputTokenItemRelation(
                  text, ([token] + tailTokens)[k],
                  newCursors[k], newStarts[k], newEnds[k],
                  newCursors[k + 1]
                )
      {
        if k > 0 {
          assert newCursors[k] == cursors[k - 1];
          assert newCursors[k + 1] == cursors[k];
          assert newStarts[k] == starts[k - 1];
          assert newEnds[k] == ends[k - 1];
          assert ([token] + tailTokens)[k] == tailTokens[k - 1];
          assert Spec.InputTokenItemRelation(
              text, tailTokens[k - 1],
              cursors[k - 1], starts[k - 1], ends[k - 1], cursors[k]
            );
        } else {
          reveal Spec.InputTokenItemRelation();
        }
      }
    }
    assert Spec.InputTokenPartitionFrom(
        text, i, [token] + tailTokens,
        newCursors, newStarts, newEnds
      );
  }

  lemma SplitWordsFromSatisfiesRelation(text: BW.Bytes, i: nat)
    requires i <= |text|
    ensures Spec.InputTokensFromRelation(
              text, i, Core.SplitWordsFrom(text, i)
            )
    decreases |text| - i
  {
    if i == |text| {
      reveal Spec.InputTokensFromRelation();
      assert Spec.InputTokenPartitionFrom(
          text, i, [], [i], [], []
        );
    } else {
      IsWhitespaceEq(text[i]);
      if Core.IsWhitespace(text[i]) {
        SplitWordsFromSatisfiesRelation(text, i + 1);
        var cursors: seq<nat>, starts: seq<nat>, ends: seq<nat> :|
          Spec.InputTokenPartitionFrom(
            text, i + 1, Core.SplitWordsFrom(text, i + 1),
            cursors, starts, ends
          );
        LiftInputPartitionOverWhitespace(
          text, i, Core.SplitWordsFrom(text, i + 1),
          cursors, starts, ends
        );
      } else if text[i] == '\0' {
        SkipAfterNulSatisfiesRelation(text, i);
        var next := Core.SkipAfterNul(text, i);
        SplitWordsFromSatisfiesRelation(text, next);
        var cursors: seq<nat>, starts: seq<nat>, ends: seq<nat> :|
          Spec.InputTokenPartitionFrom(
            text, next, Core.SplitWordsFrom(text, next),
            cursors, starts, ends
          );
        PrependInputTokenPartition(
          text, i, i, next, "",
          Core.SplitWordsFrom(text, next), cursors, starts, ends
        );
      } else {
        WordEndSatisfiesRelation(text, i);
        var end := Core.WordEnd(text, i);
        var next :=
          if end < |text| && text[end] == '\0'
          then Core.SkipAfterNul(text, end)
          else end;
        if end < |text| && text[end] == '\0' {
          SkipAfterNulSatisfiesRelation(text, end);
        }
        SplitWordsFromSatisfiesRelation(text, next);
        var cursors: seq<nat>, starts: seq<nat>, ends: seq<nat> :|
          Spec.InputTokenPartitionFrom(
            text, next, Core.SplitWordsFrom(text, next),
            cursors, starts, ends
          );
        PrependInputTokenPartition(
          text, i, end, next, text[i..end],
          Core.SplitWordsFrom(text, next), cursors, starts, ends
        );
      }
    }
  }

  lemma SplitWordsSatisfiesRelation(text: BW.Bytes)
    ensures Spec.InputTokensRelation(text, Core.SplitWords(text))
  {
    SplitWordsFromSatisfiesRelation(text, 0);
    reveal Spec.InputTokensRelation();
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.FactorCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    HelpSelectedEq(raw);
    VersionSelectedEq(raw);
    if Core.HelpSelected(raw) {
    } else if Core.VersionSelected(raw) {
    } else {
      var tokens := if |raw.operands| > 0 then raw.operands else Core.SplitWords(old(io.stdin()));
      if |raw.operands| == 0 {
        SplitWordsSatisfiesRelation(old(io.stdin()));
      }
      RunTokensSatisfiesRelation(tokens, raw.seenExponents);
      var run := Core.RunTokens(tokens, raw.seenExponents);
      assert Spec.RunRelation(
          tokens,
          raw.seenExponents,
          run.stdout,
          run.stderr,
          run.hadError
        );
      assert exists output: BW.Bytes,
          errorOutput: BW.Bytes,
          hadError: bool ::
          Spec.RunRelation(
            tokens, raw.seenExponents,
            output, errorOutput, hadError
          ) &&
          io.stdout() == old(io.stdout()) + output &&
          io.stderr() == old(io.stderr()) + errorOutput &&
          exit == (if hadError then 1 else 0);
    }
  }
}
