include "../../core/World.dfy"
include "../../core/IO.dfy"
include "ExprSchema.dfy"
include "ExprSpec.dfy"
include "ExprCore.dfy"

module ExprProof {
  import BenchIO
  import BenchWorld
  import Schema = ExprSchema
  import Spec = ExprSpec
  import Core = ExprCore

  ghost function ResultOf(
    result: (bool, string, nat, BenchWorld.Bytes)
  ): Spec.EvalResult
  {
    if result.0 then
      Spec.EvalSuccess(result.1, result.2)
    else
      Spec.EvalFailure(result.3)
  }

  // Core folds left with an accumulator while `Spec.DecimalValue` peels the
  // last digit, so the bridge needs positional weights. They belong here, not
  // in the specification.
  ghost function Pow10(power: nat): int
    decreases power
  {
    if power == 0 then 1 else 10 * Pow10(power - 1)
  }

  lemma Pow10Positive(power: nat)
    ensures Pow10(power) > 0
    decreases power
  {
    if power > 0 {
      Pow10Positive(power - 1);
    }
  }

  lemma AllDigitsForward(text: string, i: nat)
    requires i <= |text|
    requires Core.AllDigitsFrom(text, i)
    ensures Spec.AllDigits(text[i..])
    decreases |text| - i
  {
    if i < |text| {
      AllDigitsForward(text, i + 1);
      forall j | 0 <= j < |text[i..]|
        ensures Spec.IsDigit(text[i..][j])
      {
        assert text[i..][j] == text[i + j];
      }
    }
  }

  lemma AllDigitsBackward(text: string, i: nat)
    requires i <= |text|
    requires Spec.AllDigits(text[i..])
    ensures Core.AllDigitsFrom(text, i)
    decreases |text| - i
  {
    if i < |text| {
      assert text[i..][0] == text[i];
      assert text[i..][1..] == text[i + 1..];
      AllDigitsBackward(text, i + 1);
    }
  }

  // Relates the two recursion directions of `Spec.DecimalValue`.
  lemma {:induction false} DecimalFrontPeel(digits: string)
    requires Spec.AllDigits(digits)
    requires |digits| > 0
    ensures Spec.DecimalValue(digits) ==
            Spec.DigitValue(digits[0]) * Pow10(|digits| - 1) +
            Spec.DecimalValue(digits[1..])
    decreases |digits|
  {
    if |digits| == 1 {
      assert digits[..0] == [];
      assert digits[1..] == [];
    } else {
      var front := digits[..|digits| - 1];
      assert |front| == |digits| - 1 > 0;
      assert front[0] == digits[0];
      DecimalFrontPeel(front);
      assert front[1..] == digits[1..|digits| - 1];
      var tail := digits[1..];
      assert |tail| == |digits| - 1;
      assert tail[..|tail| - 1] == digits[1..|digits| - 1];
      assert tail[|tail| - 1] == digits[|digits| - 1];
      assert Pow10(|digits| - 1) == 10 * Pow10(|digits| - 2);
    }
  }

  lemma {:induction false} ParseUnsignedPositional(text: string, i: nat, acc: int)
    requires i <= |text|
    requires Core.AllDigitsFrom(text, i)
    requires Spec.AllDigits(text[i..])
    ensures Core.ParseUnsigned(text, i, acc) ==
            acc * Pow10(|text| - i) + Spec.DecimalValue(text[i..])
    decreases |text| - i
  {
    if i < |text| {
      var digit := Core.DigitValue(text[i]);
      var suf := text[i..];
      assert suf[0] == text[i];
      assert suf[1..] == text[i + 1..];
      assert |suf| == |text| - i;
      AllDigitsForward(text, i + 1);
      ParseUnsignedPositional(text, i + 1, acc * 10 + digit);
      DecimalFrontPeel(suf);
      calc {
         Core.ParseUnsigned(text, i, acc);
      == Core.ParseUnsigned(text, i + 1, acc * 10 + digit);
      == (acc * 10 + digit) * Pow10(|text| - i - 1) +
         Spec.DecimalValue(text[i + 1..]);
      == acc * Pow10(|text| - i) +
         digit * Pow10(|text| - i - 1) +
         Spec.DecimalValue(suf[1..]);
      == acc * Pow10(|text| - i) + Spec.DecimalValue(suf);
      }
    }
  }

  lemma IsIntegerForward(text: string)
    requires Core.IsInteger(text)
    ensures Spec.IntegerValue(text, Core.ParseInteger(text))
  {
    if text[0] == '-' {
      AllDigitsForward(text, 1);
      ParseUnsignedPositional(text, 1, 0);
    } else {
      AllDigitsForward(text, 0);
      ParseUnsignedPositional(text, 0, 0);
      assert text[0..] == text;
    }
  }

  lemma IsIntegerBackward(text: string, value: int)
    requires Spec.IntegerValue(text, value)
    ensures Core.IsInteger(text)
    ensures Core.ParseInteger(text) == value
  {
    if text[0] == '-' {
      AllDigitsBackward(text, 1);
      ParseUnsignedPositional(text, 1, 0);
    } else {
      assert text[0..] == text;
      AllDigitsBackward(text, 0);
      ParseUnsignedPositional(text, 0, 0);
    }
  }

  // Appending a digit is now the defining equation of `Spec.DecimalValue`,
  // so this is a rewriting step rather than an induction.
  lemma AppendDigit(digits: string, digit: int)
    requires Spec.AllDigits(digits)
    requires 0 <= digit < 10
    ensures Spec.AllDigits(digits + [Core.DigitChar(digit)])
    ensures Spec.DecimalValue(digits + [Core.DigitChar(digit)]) ==
            Spec.DecimalValue(digits) * 10 + digit
  {
    var extended := digits + [Core.DigitChar(digit)];
    assert Core.DigitChar(digit) == (digit + ('0' as int)) as char;
    assert Spec.IsDigit(Core.DigitChar(digit));
    assert Spec.AllDigits(extended) by {
      forall j | 0 <= j < |extended|
        ensures Spec.IsDigit(extended[j])
      {
        if j < |digits| {
          assert extended[j] == digits[j];
        }
      }
    }
    assert |extended| == |digits| + 1;
    assert extended[..|extended| - 1] == digits;
    assert extended[|extended| - 1] == Core.DigitChar(digit);
    assert Spec.DigitValue(Core.DigitChar(digit)) == digit;
  }

  lemma DigitsUnsignedRepresentation(n: int)
    requires 0 <= n
    ensures Spec.DecimalRepresentation(n, Core.DigitsUnsigned(n))
    ensures Spec.AllDigits(Core.DigitsUnsigned(n))
    ensures Spec.DecimalValue(Core.DigitsUnsigned(n)) == n
    ensures |Core.DigitsUnsigned(n)| > 0
    ensures n > 0 ==> Core.DigitsUnsigned(n)[0] != '0'
    decreases n
  {
    if n < 10 {
      assert Core.DigitChar(n) == (n + ('0' as int)) as char;
      assert Spec.IsDigit(Core.DigitChar(n));
      assert Spec.AllDigits([Core.DigitChar(n)]);
      assert [Core.DigitChar(n)][..0] == [];
      assert Spec.DecimalValue([Core.DigitChar(n)]) == n;
    } else {
      var q := n / 10;
      var r := n % 10;
      DigitsUnsignedRepresentation(q);
      AppendDigit(Core.DigitsUnsigned(q), r);
      assert Core.DigitsUnsigned(n) ==
             Core.DigitsUnsigned(q) + [Core.DigitChar(r)];
      assert Spec.IntegerValue(Core.DigitsUnsigned(n), n);
      assert Core.DigitsUnsigned(q)[0] != '0';
    }
  }

  // Prefixing a character is now just a slicing fact.
  lemma ShiftDecimal(prefix: char, text: string)
    requires Spec.AllDigits(text)
    ensures Spec.AllDigits(([prefix] + text)[1..])
    ensures Spec.DecimalValue(([prefix] + text)[1..]) == Spec.DecimalValue(text)
  {
    assert ([prefix] + text)[1..] == text;
  }

  lemma DigitsRepresentation(n: int)
    ensures Spec.DecimalRepresentation(n, Core.Digits(n))
    decreases if n < 0 then 1 - n else n
  {
    if n < 0 {
      DigitsUnsignedRepresentation(-n);
      ShiftDecimal('-', Core.DigitsUnsigned(-n));
      assert Core.DigitsUnsigned(-n)[0] != '0';
    } else {
      DigitsUnsignedRepresentation(n);
    }
  }

  lemma ValueTruthRefinement(value: string)
    ensures Spec.ValueTruth(value, Core.ValueIsTrue(value))
  {
    if Core.IsInteger(value) {
      IsIntegerForward(value);
      if Spec.IntegerValue(value, 0) {
        IsIntegerBackward(value, 0);
      }
    } else {
      if Spec.IntegerValue(value, 0) {
        IsIntegerBackward(value, 0);
        assert false;
      }
    }
  }

  ghost predicate LexLessFrom(a: string, b: string, i: nat)
    requires i <= |a|
    requires i <= |b|
  {
    (exists first: nat ::
       i <= first < |a| &&
       first < |b| &&
       a[i..first] == b[i..first] &&
       a[first] < b[first]) ||
    (|a| < |b| && a[i..] == b[i..|a|])
  }

  lemma StringLessFromRefinement(a: string, b: string, i: nat)
    requires i <= |a|
    requires i <= |b|
    ensures Core.StringLessFrom(a, b, i) <==> LexLessFrom(a, b, i)
    decreases |a| - i, |b| - i
  {
    if i < |a| && i < |b| && a[i] == b[i] {
      StringLessFromRefinement(a, b, i + 1);
    }
  }

  lemma StringLessRefinement(a: string, b: string)
    ensures Core.StringLess(a, b) <==> Spec.StringLess(a, b)
  {
    StringLessFromRefinement(a, b, 0);
  }

  lemma ComparisonRefinement(left: string, op: string, right: string)
    ensures Spec.ComparisonRelation(left, op, right, Core.CompareValues(left, op, right))
  {
    if Core.IsInteger(left) && Core.IsInteger(right) {
      IsIntegerForward(left);
      IsIntegerForward(right);
    } else {
      if exists l: int, r: int ::
          Spec.IntegerValue(left, l) && Spec.IntegerValue(right, r) {
        var l: int, r: int :|
          Spec.IntegerValue(left, l) && Spec.IntegerValue(right, r);
        IsIntegerBackward(left, l);
        IsIntegerBackward(right, r);
        assert false;
      }
      StringLessRefinement(left, right);
      StringLessRefinement(right, left);
    }
  }

  lemma ArithmeticRefinement(op: string, left: string, right: string)
    requires op == "+" || op == "-" || op == "*" || op == "/" || op == "%"
    ensures Spec.ArithmeticRelation(
              op,
              left,
              right,
              if Core.ApplyArithmetic(op, left, right).0 then
                Spec.EvalSuccess(Core.ApplyArithmetic(op, left, right).1, 0)
              else
                Spec.EvalFailure(Core.ApplyArithmetic(op, left, right).2)
            )
  {
    if Core.IsInteger(left) && Core.IsInteger(right) {
      IsIntegerForward(left);
      IsIntegerForward(right);
      var l := Core.ParseInteger(left);
      var r := Core.ParseInteger(right);
      if !((op == "/" || op == "%") && r == 0) {
        if op == "+" {
          DigitsRepresentation(l + r);
        } else if op == "-" {
          DigitsRepresentation(l - r);
        } else if op == "*" {
          DigitsRepresentation(l * r);
        } else if op == "/" {
          DigitsRepresentation(Core.DivTrunc(l, r));
        } else {
          DigitsRepresentation(Core.ModTrunc(l, r));
        }
      }
    } else {
      if exists l: int, r: int ::
          Spec.IntegerValue(left, l) && Spec.IntegerValue(right, r) {
        var l: int, r: int :|
          Spec.IntegerValue(left, l) && Spec.IntegerValue(right, r);
        IsIntegerBackward(left, l);
        IsIntegerBackward(right, r);
        assert false;
      }
    }
  }

  lemma TakeSliceRefinement(text: string, count: nat)
    ensures Core.Take(text, count) ==
            (if count <= |text| then text[..count] else text)
    decreases count, |text|
  {
    if count > 0 && |text| > 0 {
      TakeSliceRefinement(text[1..], count - 1);
    }
  }

  lemma SubstringRefinement(text: string, posText: string, lenText: string)
    ensures Spec.SubstringRelation(
              text, posText, lenText, Core.SubstringValue(text, posText, lenText)
            )
  {
    if Core.IsInteger(posText) && Core.IsInteger(lenText) {
      IsIntegerForward(posText);
      IsIntegerForward(lenText);
      var pos := Core.ParseInteger(posText);
      var len := Core.ParseInteger(lenText);
      if pos > 0 && len > 0 && pos - 1 < |text| {
        TakeSliceRefinement(text[(pos - 1) as nat..], len as nat);
      }
    } else {
      if exists pos: int, len: int ::
          Spec.IntegerValue(posText, pos) && Spec.IntegerValue(lenText, len) {
        var pos: int, len: int :|
          Spec.IntegerValue(posText, pos) && Spec.IntegerValue(lenText, len);
        IsIntegerBackward(posText, pos);
        IsIntegerBackward(lenText, len);
        assert false;
      }
    }
  }

  lemma ContainsCharRefinement(chars: string, target: char, i: nat)
    requires i <= |chars|
    ensures Core.ContainsChar(chars, target, i) <==>
            target in chars[i..]
    decreases |chars| - i
  {
    if i < |chars| {
      assert chars[i..][0] == chars[i];
      assert chars[i..][1..] == chars[i + 1..];
      if chars[i] != target {
        ContainsCharRefinement(chars, target, i + 1);
      }
    }
  }

  lemma FindIndexRefinement(text: string, chars: string, i: nat)
    requires i <= |text|
    ensures var index := Core.FindIndexFrom(text, chars, i);
            if index == 0 then
              forall k :: i <= k < |text| ==> text[k] !in chars
            else
              i < index <= |text| &&
              text[index - 1] in chars &&
              (forall k :: i <= k < index - 1 ==> text[k] !in chars)
    decreases |text| - i
  {
    if i < |text| {
      ContainsCharRefinement(chars, text[i], 0);
      assert chars[0..] == chars;
      if !Core.ContainsChar(chars, text[i], 0) {
        FindIndexRefinement(text, chars, i + 1);
      }
    }
  }

  lemma IndexRefinement(text: string, chars: string)
    ensures Spec.IndexRelation(text, chars, Core.IndexValue(text, chars))
  {
    FindIndexRefinement(text, chars, 0);
    DigitsRepresentation(Core.FindIndexFrom(text, chars, 0));
  }

  lemma OrRefinement(tokens: seq<string>, i: nat)
    requires i <= |tokens|
    ensures Spec.OrJudgment(tokens, i, ResultOf(Core.ParseOr(tokens, i)))
    decreases |tokens| - i, 6
  {
    AndRefinement(tokens, i);
    var left := Core.ParseAnd(tokens, i);
    if left.0 {
      OrTailRefinement(tokens, left.1, left.2);
    }
  }

  lemma OrTailRefinement(tokens: seq<string>, left: string, i: nat)
    requires i <= |tokens|
    ensures Spec.OrTailJudgment(tokens, left, i, ResultOf(Core.ParseOrRest(tokens, left, i)))
    decreases |tokens| - i, 6
  {
    if i < |tokens| && tokens[i] == "|" {
      AndRefinement(tokens, i + 1);
      var right := Core.ParseAnd(tokens, i + 1);
      if right.0 {
        ValueTruthRefinement(left);
        OrTailRefinement(
          tokens, if Core.ValueIsTrue(left) then left else right.1, right.2
        );
      }
    }
  }

  lemma AndRefinement(tokens: seq<string>, i: nat)
    requires i <= |tokens|
    ensures Spec.AndJudgment(tokens, i, ResultOf(Core.ParseAnd(tokens, i)))
    decreases |tokens| - i, 5
  {
    CompareRefinement(tokens, i);
    var left := Core.ParseCompare(tokens, i);
    if left.0 {
      AndTailRefinement(tokens, left.1, left.2);
    }
  }

  lemma AndTailRefinement(tokens: seq<string>, left: string, i: nat)
    requires i <= |tokens|
    ensures Spec.AndTailJudgment(tokens, left, i, ResultOf(Core.ParseAndRest(tokens, left, i)))
    decreases |tokens| - i, 5
  {
    if i < |tokens| && tokens[i] == "&" {
      CompareRefinement(tokens, i + 1);
      var right := Core.ParseCompare(tokens, i + 1);
      if right.0 {
        ValueTruthRefinement(left);
        ValueTruthRefinement(right.1);
        AndTailRefinement(
          tokens,
          if Core.ValueIsTrue(left) && Core.ValueIsTrue(right.1) then left else "0",
          right.2
        );
      }
    }
  }

  lemma CompareRefinement(tokens: seq<string>, i: nat)
    requires i <= |tokens|
    ensures Spec.CompareJudgment(tokens, i, ResultOf(Core.ParseCompare(tokens, i)))
    decreases |tokens| - i, 4
  {
    AddRefinement(tokens, i);
    var left := Core.ParseAdd(tokens, i);
    if left.0 {
      CompareTailRefinement(tokens, left.1, left.2);
    }
  }

  lemma CompareTailRefinement(tokens: seq<string>, left: string, i: nat)
    requires i <= |tokens|
    ensures Spec.CompareTailJudgment(
              tokens, left, i, ResultOf(Core.ParseCompareRest(tokens, left, i))
            )
    decreases |tokens| - i, 4
  {
    if i < |tokens| && Core.IsCompareOp(tokens[i]) {
      AddRefinement(tokens, i + 1);
      var right := Core.ParseAdd(tokens, i + 1);
      if right.0 {
        ComparisonRefinement(left, tokens[i], right.1);
        CompareTailRefinement(
          tokens, Core.CompareValues(left, tokens[i], right.1), right.2
        );
      }
    }
  }

  lemma AddRefinement(tokens: seq<string>, i: nat)
    requires i <= |tokens|
    ensures Spec.AddJudgment(tokens, i, ResultOf(Core.ParseAdd(tokens, i)))
    decreases |tokens| - i, 3
  {
    MulRefinement(tokens, i);
    var left := Core.ParseMul(tokens, i);
    if left.0 {
      AddTailRefinement(tokens, left.1, left.2);
    }
  }

  lemma AddTailRefinement(tokens: seq<string>, left: string, i: nat)
    requires i <= |tokens|
    ensures Spec.AddTailJudgment(
              tokens, left, i, ResultOf(Core.ParseAddRest(tokens, left, i))
            )
    decreases |tokens| - i, 3
  {
    if i < |tokens| && (tokens[i] == "+" || tokens[i] == "-") {
      MulRefinement(tokens, i + 1);
      var right := Core.ParseMul(tokens, i + 1);
      if right.0 {
        ArithmeticRefinement(tokens[i], left, right.1);
        var applied := Core.ApplyArithmetic(tokens[i], left, right.1);
        if applied.0 {
          AddTailRefinement(tokens, applied.1, right.2);
        }
      }
    }
  }

  lemma MulRefinement(tokens: seq<string>, i: nat)
    requires i <= |tokens|
    ensures Spec.MulJudgment(tokens, i, ResultOf(Core.ParseMul(tokens, i)))
    decreases |tokens| - i, 2
  {
    MatchRefinement(tokens, i);
    var left := Core.ParseMatch(tokens, i);
    if left.0 {
      MulTailRefinement(tokens, left.1, left.2);
    }
  }

  lemma MulTailRefinement(tokens: seq<string>, left: string, i: nat)
    requires i <= |tokens|
    ensures Spec.MulTailJudgment(
              tokens, left, i, ResultOf(Core.ParseMulRest(tokens, left, i))
            )
    decreases |tokens| - i, 2
  {
    if i < |tokens| && (tokens[i] == "*" || tokens[i] == "/" || tokens[i] == "%") {
      MatchRefinement(tokens, i + 1);
      var right := Core.ParseMatch(tokens, i + 1);
      if right.0 {
        ArithmeticRefinement(tokens[i], left, right.1);
        var applied := Core.ApplyArithmetic(tokens[i], left, right.1);
        if applied.0 {
          MulTailRefinement(tokens, applied.1, right.2);
        }
      }
    }
  }

  lemma MatchRefinement(tokens: seq<string>, i: nat)
    requires i <= |tokens|
    ensures Spec.MatchJudgment(tokens, i, ResultOf(Core.ParseMatch(tokens, i)))
    decreases |tokens| - i, 1
  {
    PrimaryRefinement(tokens, i);
  }

  lemma PrimaryRefinement(tokens: seq<string>, i: nat)
    requires i <= |tokens|
    ensures Spec.PrimaryJudgment(tokens, i, ResultOf(Core.ParsePrimary(tokens, i)))
    decreases |tokens| - i, 0
  {
    if i >= |tokens| {
      return;
    }
    if tokens[i] == "(" {
      OrRefinement(tokens, i + 1);
    } else if tokens[i] == "length" {
      PrimaryRefinement(tokens, i + 1);
      var arg := Core.ParsePrimary(tokens, i + 1);
      if arg.0 {
        DigitsRepresentation(|arg.1|);
      }
    } else if tokens[i] == "substr" {
      PrimaryRefinement(tokens, i + 1);
      var text := Core.ParsePrimary(tokens, i + 1);
      if text.0 {
        PrimaryRefinement(tokens, text.2);
        var pos := Core.ParsePrimary(tokens, text.2);
        if pos.0 {
          PrimaryRefinement(tokens, pos.2);
          var len := Core.ParsePrimary(tokens, pos.2);
          if len.0 {
            SubstringRefinement(text.1, pos.1, len.1);
          }
        }
      }
    } else if tokens[i] == "index" {
      PrimaryRefinement(tokens, i + 1);
      var text := Core.ParsePrimary(tokens, i + 1);
      if text.0 {
        PrimaryRefinement(tokens, text.2);
        var chars := Core.ParsePrimary(tokens, text.2);
        if chars.0 {
          IndexRefinement(text.1, chars.1);
        }
      }
    }
  }

  lemma EvaluateRefinement(args: seq<string>)
    ensures Spec.ExecutionRelation(
              args,
              Core.EvaluateArgs(args).0,
              Core.EvaluateArgs(args).1,
              Core.EvaluateArgs(args).2
            )
  {
    if !(args == ["--help"]) && !(args == ["--version"]) {
      var exprArgs := Core.EffectiveArgs(args);
      if |exprArgs| > 0 {
        OrRefinement(exprArgs, 0);
        var parsed := Core.ParseOr(exprArgs, 0);
        if parsed.0 && parsed.2 == |exprArgs| {
          ValueTruthRefinement(parsed.1);
        }
      }
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.ExprCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    EvaluateRefinement(raw.args);
  }
}
