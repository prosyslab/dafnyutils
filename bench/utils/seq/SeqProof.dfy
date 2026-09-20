include "../../core/World.dfy"
include "SeqSchema.dfy"
include "SeqCore.dfy"
include "SeqSpec.dfy"

module SeqProof {
  import BenchIO
  import BW = BenchWorld
  import Schema = SeqSchema
  import Core = SeqCore
  import Spec = SeqSpec

  function ToSpecDecimal(c: Core.Decimal): Spec.Decimal
  {
    Spec.Decimal(c.raw, c.value, c.scale, c.negativeZero)
  }

  function ToSpecParse(parsed: Core.DecimalParse): Spec.DecimalParse
  {
    match parsed
    case DecimalOk(number) => Spec.DecimalOk(ToSpecDecimal(number))
    case DecimalErr(token) => Spec.DecimalErr(token)
  }

  function ToSpecPlan(plan: Core.NumberPlan): Spec.NumberPlan
  {
    match plan
    case NumbersOk(first, step, last) =>
      Spec.NumbersOk(ToSpecDecimal(first), ToSpecDecimal(step), ToSpecDecimal(last))
    case NumbersErr(stderr) => Spec.NumbersErr(stderr)
  }

  function FirstDot(text: string, position: nat): int
    requires position <= |text|
    ensures FirstDot(text, position) == -1 ||
            position <= FirstDot(text, position) < |text|
    decreases |text| - position
  {
    if position == |text| then
      -1
    else if text[position] == '.' then
      position
    else
      FirstDot(text, position + 1)
  }

  function RemainingDigitCount(end: nat, position: nat, dot: int): nat
    requires position <= end
    requires dot == -1 || 0 <= dot < end
  {
    end - position - (if position <= dot then 1 else 0)
  }

  function ContributionSequence(
    text: string,
    start: nat,
    end: nat,
    dot: int
  ): seq<int>
    requires start <= end <= |text|
    requires dot == -1 || 0 <= dot < end
  {
    Spec.DigitContributions(text, start, end, dot)
  }

  function PositionContribution(text: string, position: nat, end: nat, dot: int): int
    requires position < end <= |text|
    requires dot == -1 || 0 <= dot < end
  {
    if position == dot then 0 else
    Spec.DigitAt(text[position]) *
    Spec.Pow10(end - position - 1 - (if position < dot then 1 else 0))
  }

  lemma ContributionTail(text: string, start: nat, end: nat, dot: int)
    requires start < end <= |text|
    requires dot == -1 || 0 <= dot < end
    ensures ContributionSequence(text, start, end, dot)[1..] ==
            ContributionSequence(text, start + 1, end, dot)
  {
    reveal ContributionSequence;
    reveal PositionContribution;
    assert |ContributionSequence(text, start, end, dot)[1..]| ==
           |ContributionSequence(
             text, start + 1, end, dot
           )|;
    assert forall offset: nat
        | offset < |ContributionSequence(text, start, end, dot)[1..]| ::
        ContributionSequence(text, start, end, dot)[1..][offset] ==
        ContributionSequence(
          text, start + 1, end, dot
        )[offset] by {
      forall offset: nat
        | offset < |ContributionSequence(text, start, end, dot)[1..]|
        ensures ContributionSequence(text, start, end, dot)[1..][offset] ==
                ContributionSequence(
                  text, start + 1, end, dot
                )[offset]
      {
        assert start + 1 + offset == start + (offset + 1);
        assert ContributionSequence(text, start, end, dot)[1..][offset] ==
               PositionContribution(text, (start + offset + 1) as nat, end, dot);
        assert ContributionSequence(
            text, start + 1, end, dot
          )[offset] == PositionContribution(
                              text,
                              (start + 1 + offset) as nat,
                              end,
                              dot
                            );
      }
    }
  }

  lemma DigitFacts(ch: char)
    ensures Core.IsDigit(ch) == Spec.IsDigit(ch)
  {
  }

  lemma DigitValueAtEq(ch: char)
    requires Core.IsDigit(ch)
    ensures Core.DigitValue(ch) == Spec.DigitAt(ch)
  {
  }

  lemma Pow10Eq(n: nat)
    ensures Core.Pow10(n) == Spec.Pow10(n)
    decreases n
  {
    if n > 0 {
      Pow10Eq(n - 1);
    }
  }

  lemma CalculatedApplyExponentEq(
    token: string,
    value: int,
    scale: nat,
    negativeZero: bool,
    exponent: int
  )
    ensures ToSpecDecimal(Core.ApplyExponent(
                            token, value, scale, negativeZero, exponent
                          )) == Spec.ApplyExponent(token, value, scale, negativeZero, exponent)
  {
    if exponent >= 0 && exponent as nat > scale {
      Pow10Eq(exponent as nat - scale);
    }
  }

  lemma FirstDotFacts(text: string, position: nat)
    requires position <= |text|
    ensures FirstDot(text, position) == -1 ==>
              forall i: nat | position <= i < |text| :: text[i] != '.'
    ensures FirstDot(text, position) >= 0 ==>
              text[FirstDot(text, position)] == '.' &&
              (forall i: nat | position <= i < FirstDot(text, position) :: text[i] != '.')
    decreases |text| - position
  {
    if position < |text| && text[position] != '.' {
      FirstDotFacts(text, position + 1);
    }
  }

  lemma ExponentIndexFacts(text: string, start: nat)
    requires start <= |text|
    ensures Core.ExponentIndex(text, start) == -1 ==>
              forall i: nat | start <= i < |text| :: text[i] != 'e' && text[i] != 'E'
    ensures Core.ExponentIndex(text, start) >= 0 ==>
              var index := Core.ExponentIndex(text, start) as nat;
              start <= index < |text| &&
              (text[index] == 'e' || text[index] == 'E') &&
              (forall i: nat | start <= i < index :: text[i] != 'e' && text[i] != 'E')
    decreases |text| - start
  {
    if start < |text| && text[start] != 'e' && text[start] != 'E' {
      ExponentIndexFacts(text, start + 1);
    }
  }

  lemma ExponentIndexAt(text: string, start: nat, index: nat)
    requires start <= index < |text|
    requires text[index] == 'e' || text[index] == 'E'
    requires forall i: nat | start <= i < index :: text[i] != 'e' && text[i] != 'E'
    ensures Core.ExponentIndex(text, start) == index
    decreases index - start
  {
    if start < index {
      ExponentIndexAt(text, start + 1, index);
    }
  }

  lemma ScanNatSound(
    text: string,
    start: nat,
    sawDigit: bool,
    accumulator: nat
  )
    requires start <= |text|
    requires Core.ScanNat(text, start, sawDigit, accumulator).ok
    ensures forall i: nat | start <= i < |text| :: Core.IsDigit(text[i])
    decreases |text| - start
  {
    if start < |text| {
      ScanNatSound(
        text,
        start + 1,
        true,
        (accumulator * 10 + Core.DigitValue(text[start])) as nat
      );
    }
  }

  lemma {:isolate_assertions} ScanNatValueRelation(
    text: string,
    start: nat,
    sawDigit: bool,
    accumulator: nat
  )
    requires start <= |text|
    requires forall i: nat | start <= i < |text| :: Core.IsDigit(text[i])
    ensures Core.ScanNat(text, start, sawDigit, accumulator).value ==
            accumulator * Spec.Pow10(|text| - start) +
            Spec.IntSequenceSum(ContributionSequence(text, start, |text|, -1))
    decreases |text| - start
  {
    reveal ContributionSequence;
    reveal PositionContribution;
    if start < |text| {
      DigitValueAtEq(text[start]);
      ContributionTail(text, start, |text|, -1);
      ScanNatValueRelation(
        text,
        start + 1,
        true,
        accumulator * 10 + Core.DigitValue(text[start])
      );
      var remaining := |text| - start;
      assert 0 < remaining;
      assert ContributionSequence(text, start, |text|, -1)[0] ==
             Spec.DigitAt(text[start]) * Spec.Pow10(remaining - 1);
      assert Spec.IntSequenceSum(ContributionSequence(text, start, |text|, -1)) ==
             ContributionSequence(text, start, |text|, -1)[0] +
             Spec.IntSequenceSum(ContributionSequence(text, start + 1, |text|, -1));
      assert Spec.Pow10(remaining) == 10 * Spec.Pow10(remaining - 1);
    }
  }

  lemma ParseExponentSound(text: string)
    requires Core.ParseExponent(text).ExponentOk?
    ensures Spec.ExponentRelation(
              text,
              0,
              |text|,
              Core.ParseExponent(text).value
            )
  {
    var digitStart := if text[0] == '-' || text[0] == '+' then 1 else 0;
    var scan := Core.ScanNat(text, digitStart, false, 0);
    ScanNatSound(text, digitStart, false, 0);
    assert forall i: nat | digitStart <= i < |text| :: Core.IsDigit(text[i]);
    ScanNatValueRelation(text, digitStart, false, 0);
    assert scan.value ==
           Spec.IntSequenceSum(ContributionSequence(text, digitStart, |text|, -1));
    assert Spec.PositionalValueRelation(
        text, digitStart, |text|, -1, scan.value
      );
    assert forall position: nat {:trigger text[position]}
        | digitStart <= position < |text| ::
        Spec.IsDigit(text[position]) by {
      forall position: nat {:trigger text[position]}
    | digitStart <= position < |text|
        ensures Spec.IsDigit(text[position])
      {
        DigitFacts(text[position]);
      }
    }
  }

  lemma ScanDecimalSound(
    text: string,
    start: nat,
    sawDot: bool,
    sawDigit: bool,
    accumulator: int,
    scale: nat
  )
    requires start <= |text|
    requires 0 <= accumulator
    requires Core.ScanDecimal(text, start, sawDot, sawDigit, accumulator, scale).ok
    ensures sawDot ==>
              forall i: nat | start <= i < |text| :: Core.IsDigit(text[i])
    ensures !sawDot ==>
              forall i: nat | start <= i < |text| ::
                Core.IsDigit(text[i]) || text[i] == '.'
    ensures !sawDot ==>
              forall i: nat, j: nat | start <= i < j < |text| ::
                !(text[i] == '.' && text[j] == '.')
    decreases |text| - start
  {
    if start < |text| {
      if Core.IsDigit(text[start]) {
        ScanDecimalSound(
          text,
          start + 1,
          sawDot,
          true,
          accumulator * 10 + Core.DigitValue(text[start]),
          if sawDot then scale + 1 else scale
        );
      } else {
        ScanDecimalSound(text, start + 1, true, sawDigit, accumulator, scale);
      }
    }
  }

  lemma ScanDecimalDigitStep(
    text: string,
    start: nat,
    sawDot: bool,
    sawDigit: bool,
    accumulator: int,
    scale: nat
  )
    requires start < |text|
    requires 0 <= accumulator
    requires Core.IsDigit(text[start])
    ensures Core.ScanDecimal(
              text, start, sawDot, sawDigit, accumulator, scale
            ) == Core.ScanDecimal(
                   text,
                   start + 1,
                   sawDot,
                   true,
                   accumulator * 10 + Core.DigitValue(text[start]),
                   if sawDot then scale + 1 else scale
                 )
  {
  }

  lemma ScanDecimalDotStep(
    text: string,
    start: nat,
    sawDigit: bool,
    accumulator: int,
    scale: nat
  )
    requires start < |text|
    requires 0 <= accumulator
    requires text[start] == '.'
    ensures Core.ScanDecimal(
              text, start, false, sawDigit, accumulator, scale
            ) == Core.ScanDecimal(text, start + 1, true, sawDigit, accumulator, scale)
  {
  }

  lemma DecimalDigitAccumulation(
    accumulator: int,
    digit: int,
    power: int,
    tail: int
  )
    ensures (accumulator * 10 + digit) * power + tail ==
            accumulator * (10 * power) + (digit * power + tail)
  {
  }

  lemma {:vcs_split_on_every_assert} ScanDecimalValueRelation(
    text: string,
    start: nat,
    dot: int,
    accumulator: int,
    scale: nat,
    sawDot: bool,
    sawDigit: bool
  )
    requires start <= |text|
    requires 0 <= accumulator
    requires dot == -1 || 0 <= dot < |text|
    requires sawDot == (dot != -1 && dot < start)
    requires forall i: nat | start <= i < |text| ::
               if i == dot then text[i] == '.' else Core.IsDigit(text[i])
    ensures Core.ScanDecimal(text, start, sawDot, sawDigit, accumulator, scale).mantissa ==
            accumulator * Spec.Pow10(RemainingDigitCount(|text|, start, dot)) +
            Spec.IntSequenceSum(ContributionSequence(text, start, |text|, dot))
    decreases |text| - start
  {
    reveal ContributionSequence;
    reveal PositionContribution;
    reveal RemainingDigitCount;
    if start < |text| {
      if start == dot {
        ContributionTail(text, start, |text|, dot);
        ScanDecimalValueRelation(text, start + 1, dot, accumulator, scale, true, sawDigit);
        ScanDecimalDotStep(text, start, sawDigit, accumulator, scale);
        assert RemainingDigitCount(|text|, start, dot) ==
               RemainingDigitCount(|text|, start + 1, dot);
        assert ContributionSequence(text, start, |text|, dot)[0] == 0;
        assert Spec.IntSequenceSum(ContributionSequence(text, start, |text|, dot)) ==
               Spec.IntSequenceSum(ContributionSequence(text, start + 1, |text|, dot));
        assert Core.ScanDecimal(
            text, start, sawDot, sawDigit, accumulator, scale
          ).mantissa ==
               accumulator * Spec.Pow10(RemainingDigitCount(|text|, start, dot)) +
               Spec.IntSequenceSum(ContributionSequence(text, start, |text|, dot));
      } else {
        DigitValueAtEq(text[start]);
        ContributionTail(text, start, |text|, dot);
        ScanDecimalValueRelation(
          text,
          start + 1,
          dot,
          accumulator * 10 + Core.DigitValue(text[start]),
          if sawDot then scale + 1 else scale,
          sawDot,
          true
        );
        ScanDecimalDigitStep(text, start, sawDot, sawDigit, accumulator, scale);
        var remaining := RemainingDigitCount(|text|, start, dot);
        var power := Spec.Pow10(remaining - 1);
        var tailSum := Spec.IntSequenceSum(
          ContributionSequence(text, start + 1, |text|, dot)
        );
        assert 0 < remaining;
        assert RemainingDigitCount(|text|, start + 1, dot) == remaining - 1;
        assert ContributionSequence(text, start, |text|, dot)[0] ==
               Spec.DigitAt(text[start]) * power;
        assert Spec.IntSequenceSum(ContributionSequence(text, start, |text|, dot)) ==
               ContributionSequence(text, start, |text|, dot)[0] + tailSum;
        assert Spec.Pow10(remaining) == 10 * power;
        DecimalDigitAccumulation(
          accumulator, Spec.DigitAt(text[start]), power, tailSum
        );
        calc {
           Core.ScanDecimal(
             text, start, sawDot, sawDigit, accumulator, scale
           ).mantissa;
        == Core.ScanDecimal(
             text,
             start + 1,
             sawDot,
             true,
             accumulator * 10 + Core.DigitValue(text[start]),
             if sawDot then scale + 1 else scale
           ).mantissa;
        == (accumulator * 10 + Core.DigitValue(text[start])) * power + tailSum;
        == (accumulator * 10 + Spec.DigitAt(text[start])) * power + tailSum;
        == accumulator * (10 * power) +
           (Spec.DigitAt(text[start]) * power + tailSum);
        == accumulator * Spec.Pow10(remaining) +
           Spec.IntSequenceSum(ContributionSequence(text, start, |text|, dot));
        }
      }
    }
  }

  lemma ScanDecimalShapeRelation(
    text: string,
    start: nat,
    dot: int,
    accumulator: int,
    scale: nat,
    sawDot: bool,
    sawDigit: bool
  )
    requires start <= |text|
    requires 0 <= accumulator
    requires dot == -1 || 0 <= dot < |text|
    requires sawDot == (dot != -1 && dot < start)
    requires forall i: nat | start <= i < |text| ::
               if i == dot then text[i] == '.' else Core.IsDigit(text[i])
    ensures Core.ScanDecimal(text, start, sawDot, sawDigit, accumulator, scale).scale ==
            scale +
            (if sawDot then |text| - start
             else if dot == -1 then 0
             else |text| - dot - 1)
    ensures Core.ScanDecimal(text, start, sawDot, sawDigit, accumulator, scale).sawDot ==
            (sawDot || dot != -1)
    decreases |text| - start
  {
    if start < |text| {
      if start == dot {
        ScanDecimalShapeRelation(
          text, start + 1, dot, accumulator, scale, true, sawDigit
        );
      } else {
        ScanDecimalShapeRelation(
          text,
          start + 1,
          dot,
          accumulator * 10 + Core.DigitValue(text[start]),
          if sawDot then scale + 1 else scale,
          sawDot,
          true
        );
      }
    }
  }

  lemma {:isolate_assertions} ParseDecimalSound(token: string)
    requires Core.ParseDecimal(token).DecimalOk?
    ensures Spec.DecimalValueRelation(
              token,
              ToSpecDecimal(Core.ParseDecimal(token).number)
            )
  {
    var start := if token[0] == '-' || token[0] == '+' then 1 else 0;
    var exponentIndex := Core.ExponentIndex(token, start);
    ExponentIndexFacts(token, start);
    var mantissaText := if exponentIndex < 0 then token else token[..exponentIndex];
    var scan := Core.ScanDecimal(mantissaText, start, false, false, 0, 0);
    ScanDecimalSound(mantissaText, start, false, false, 0, 0);
    assert forall i: nat | start <= i < |mantissaText| ::
        Core.IsDigit(mantissaText[i]) || mantissaText[i] == '.';
    assert forall i: nat, j: nat | start <= i < j < |mantissaText| ::
        !(mantissaText[i] == '.' && mantissaText[j] == '.');
    var dot := FirstDot(mantissaText, start);
    FirstDotFacts(mantissaText, start);
    ScanDecimalValueRelation(mantissaText, start, dot, 0, 0, false, false);
    ScanDecimalShapeRelation(mantissaText, start, dot, 0, 0, false, false);
    assert dot == -1 ||
           (start <= dot < |mantissaText| &&
            mantissaText[dot] == '.' &&
            start < |mantissaText| - 1);
    assert forall position: nat {:trigger mantissaText[position]}
        | start <= position < |mantissaText| ::
        position == dot || Spec.IsDigit(mantissaText[position]) by {
      forall position: nat {:trigger mantissaText[position]}
    | start <= position < |mantissaText|
        ensures position == dot || Spec.IsDigit(mantissaText[position])
      {
        if position != dot {
          if mantissaText[position] == '.' {
            if dot == -1 {
              assert false;
            } else if position < dot {
              assert false;
            } else {
              assert start <= dot < position < |mantissaText|;
              assert false;
            }
          }
          DigitFacts(mantissaText[position]);
        }
      }
    }
    assert Spec.DotMarkerRelation(
        mantissaText, start, |mantissaText|, dot
      );
    assert scan.mantissa ==
           Spec.IntSequenceSum(ContributionSequence(
                                 mantissaText, start, |mantissaText|, dot
                               ));
    assert Spec.PositionalValueRelation(
        mantissaText, start, |mantissaText|, dot, scan.mantissa
      );
    assert Spec.MantissaRelation(
        mantissaText,
        start,
        |mantissaText|,
        scan.mantissa,
        scan.scale
      );
    if exponentIndex >= 0 {
      var index := exponentIndex as nat;
      var exponentText := token[exponentIndex + 1..];
      ParseExponentSound(exponentText);
      var exponent := Core.ParseExponent(exponentText).value;
      CalculatedApplyExponentEq(
        token,
        if token[0] == '-' then -scan.mantissa else scan.mantissa,
        scan.scale,
        token[0] == '-' && scan.mantissa == 0,
        exponent
      );
      assert start < index < |token|;
      assert token[index] == 'e' || token[index] == 'E';
      assert Spec.MantissaRelation(
          token[..index], start, index, scan.mantissa, scan.scale
        );
      assert Spec.ExponentRelation(
          token[index + 1..], 0, |token| - index - 1, exponent
        );
      assert forall position: nat {:trigger token[position]}
          | start <= position < |token| ::
          position == index ||
          (token[position] != 'e' && token[position] != 'E') by {
        forall position: nat {:trigger token[position]}
      | start <= position < |token|
          ensures position == index ||
                  (token[position] != 'e' && token[position] != 'E')
        {
          if position < index {
          } else if index < position {
            var suffixPosition := position - index - 1;
            assert token[position] == token[index + 1..][suffixPosition];
            var suffix := token[index + 1..];
            var digitStart :=
              if suffix[0] == '-' || suffix[0] == '+' then 1 else 0;
            if suffixPosition < digitStart {
              assert suffixPosition == 0;
              assert suffix[suffixPosition] == '-' || suffix[suffixPosition] == '+';
            } else {
              assert Spec.IsDigit(suffix[suffixPosition]);
            }
          }
        }
      }
      assert Spec.ExponentMarkerRelation(token, start, exponentIndex);
      assert ToSpecDecimal(Core.ParseDecimal(token).number) ==
             Spec.ApplyExponent(
               token,
               if token[0] == '-' then -scan.mantissa else scan.mantissa,
               scan.scale,
               token[0] == '-' && scan.mantissa == 0,
               exponent
             );
      var evidence := Spec.DecimalValueWitness(
        exponentIndex, dot, scan.mantissa, exponent
      );
      assert Spec.DecimalValueWitnessRelation(
          token, ToSpecDecimal(Core.ParseDecimal(token).number), evidence
        );
      assert start < index < |token| &&
             (token[index] == 'e' || token[index] == 'E') &&
             Spec.MantissaRelation(
               token[..index],
               start,
               index,
               scan.mantissa,
               scan.scale
             ) &&
             Spec.ExponentRelation(
               token[index + 1..],
               0,
               |token| - index - 1,
               exponent
             ) &&
             ToSpecDecimal(Core.ParseDecimal(token).number) ==
             Spec.ApplyExponent(
               token,
               if token[0] == '-' then -scan.mantissa else scan.mantissa,
               scan.scale,
               token[0] == '-' && scan.mantissa == 0,
               exponent
             );
    } else {
      assert mantissaText == token;
      assert Spec.ExponentMarkerRelation(token, start, -1);
      assert Spec.MantissaRelation(token, start, |token|, scan.mantissa, scan.scale);
      assert ToSpecDecimal(Core.ParseDecimal(token).number) ==
             Spec.Decimal(
               token,
               if token[0] == '-' then -scan.mantissa else scan.mantissa,
               scan.scale,
               token[0] == '-' && scan.mantissa == 0
             );
      var evidence := Spec.DecimalValueWitness(-1, dot, scan.mantissa, 0);
      assert Spec.DecimalValueWitnessRelation(
          token, ToSpecDecimal(Core.ParseDecimal(token).number), evidence
        );
    }
    assert Spec.DecimalValueRelation(
        token,
        ToSpecDecimal(Core.ParseDecimal(token).number)
      );
  }

  lemma ExponentIndexAbsent(text: string, start: nat)
    requires start <= |text|
    requires forall position: nat | start <= position < |text| ::
               text[position] != 'e' && text[position] != 'E'
    ensures Core.ExponentIndex(text, start) == -1
    decreases |text| - start
  {
    if start < |text| {
      ExponentIndexAbsent(text, start + 1);
    }
  }

  lemma ScanNatComplete(
    text: string,
    start: nat,
    sawDigit: bool,
    accumulator: nat
  )
    requires start <= |text|
    requires forall position: nat | start <= position < |text| ::
               Core.IsDigit(text[position])
    ensures Core.ScanNat(text, start, sawDigit, accumulator).ok
    ensures start < |text| ==> Core.ScanNat(text, start, sawDigit, accumulator).sawDigit
    decreases |text| - start
  {
    if start < |text| {
      ScanNatComplete(
        text,
        start + 1,
        true,
        (accumulator * 10 + Core.DigitValue(text[start])) as nat
      );
    }
  }

  lemma ScanDecimalComplete(
    text: string,
    start: nat,
    dot: int,
    sawDot: bool,
    sawDigit: bool,
    accumulator: int,
    scale: nat
  )
    requires start <= |text|
    requires 0 <= accumulator
    requires dot == -1 || 0 <= dot < |text|
    requires sawDot == (dot != -1 && dot < start)
    requires forall position: nat | start <= position < |text| ::
               position == dot || Core.IsDigit(text[position])
    requires dot < start || dot == -1 || text[dot] == '.'
    ensures Core.ScanDecimal(
              text, start, sawDot, sawDigit, accumulator, scale
            ).ok
    ensures (sawDigit || exists position: nat {:trigger text[position]}
               | start <= position < |text| ::
               position != dot) ==>
              Core.ScanDecimal(text, start, sawDot, sawDigit, accumulator, scale).sawDigit
    decreases |text| - start
  {
    if start < |text| {
      if start == dot {
        ScanDecimalComplete(text, start + 1, dot, true, sawDigit, accumulator, scale);
        if !sawDigit &&
           (exists position: nat {:trigger text[position]}
              | start <= position < |text| :: position != dot)
        {
          var position :| start <= position < |text| && position != dot;
          assert start + 1 <= position < |text|;
        }
      } else {
        ScanDecimalComplete(
          text,
          start + 1,
          dot,
          sawDot,
          true,
          accumulator * 10 + Core.DigitValue(text[start]),
          if sawDot then scale + 1 else scale
        );
      }
    }
  }

  lemma WitnessMantissaSyntax(
    token: string,
    number: Spec.Decimal,
    evidence: Spec.DecimalValueWitness
  )
    requires Spec.DecimalValueWitnessRelation(token, number, evidence)
    ensures
      var start := if token[0] == '-' || token[0] == '+' then 1 else 0;
      var mantissaText :=
        if evidence.exponentMarker == -1
        then token
        else token[..evidence.exponentMarker];
      forall position: nat {:trigger mantissaText[position]}
        | start <= position < |mantissaText| ::
        position == evidence.dot || Spec.IsDigit(mantissaText[position])
  {
  }

  lemma {:isolate_assertions} DecimalValueRelationImpliesCoreParseSuccess(
    token: string,
    number: Spec.Decimal
  )
    requires Spec.DecimalValueRelation(token, number)
    ensures Core.ParseDecimal(token).DecimalOk?
  {
    var evidence :| Spec.DecimalValueWitnessRelation(token, number, evidence);
    reveal Spec.DecimalValueWitnessRelation;
    var start := if token[0] == '-' || token[0] == '+' then 1 else 0;
    var marker := evidence.exponentMarker;
    WitnessMantissaSyntax(token, number, evidence);
    if marker == -1 {
      ExponentIndexAbsent(token, start);
    } else {
      assert forall position: nat | start <= position < marker ::
          token[position] != 'e' && token[position] != 'E';
      ExponentIndexAt(token, start, marker as nat);
    }
    assert Core.ExponentIndex(token, start) == marker;
    var mantissaText := if marker == -1 then token else token[..marker];
    var dot := evidence.dot;
    assert forall position: nat {:trigger mantissaText[position]}
        | start <= position < |mantissaText| ::
        position == dot || Spec.IsDigit(mantissaText[position]);
    assert forall position: nat {:trigger mantissaText[position]}
        | start <= position < |mantissaText| ::
        position == dot || Core.IsDigit(mantissaText[position]) by {
      forall position: nat {:trigger mantissaText[position]}
    | start <= position < |mantissaText|
        ensures position == dot || Core.IsDigit(mantissaText[position])
      {
        if position != dot {
          DigitFacts(mantissaText[position]);
        }
      }
    }
    ScanDecimalComplete(mantissaText, start, dot, false, false, 0, 0);
    var scan := Core.ScanDecimal(mantissaText, start, false, false, 0, 0);
    assert scan.ok && scan.sawDigit;
    if marker != -1 {
      var exponentText := token[marker + 1..];
      var digitStart :=
        if exponentText[0] == '-' || exponentText[0] == '+' then 1 else 0;
      assert forall position: nat {:trigger exponentText[position]}
          | digitStart <= position < |exponentText| ::
          Core.IsDigit(exponentText[position]) by {
        forall position: nat {:trigger exponentText[position]}
      | digitStart <= position < |exponentText|
          ensures Core.IsDigit(exponentText[position])
        {
          DigitFacts(exponentText[position]);
        }
      }
      ScanNatComplete(exponentText, digitStart, false, 0);
      assert Core.ParseExponent(exponentText).ExponentOk?;
    }
  }

  lemma DecimalParseRelation(token: string)
    ensures Spec.DecimalParseRelation(token, ToSpecParse(Core.ParseDecimal(token)))
  {
    var parsed := Core.ParseDecimal(token);
    match parsed
    case DecimalOk(_) =>
      ParseDecimalSound(token);
    case DecimalErr(_) =>
      assert forall number: Spec.Decimal ::
          !Spec.DecimalValueRelation(token, number) by {
        forall number: Spec.Decimal
          ensures !Spec.DecimalValueRelation(token, number)
        {
          if Spec.DecimalValueRelation(token, number) {
            DecimalValueRelationImpliesCoreParseSuccess(token, number);
          }
        }
      }
  }

  lemma NumberPlanRelation(args: seq<string>)
    ensures Spec.NumberPlanRelation(args, ToSpecPlan(Core.ParseNumbers(args)))
  {
    if 0 < |args| <= 3 {
      var firstText := if |args| == 1 then "1" else args[0];
      var stepText := if |args| == 3 then args[1] else "1";
      var lastText := if |args| == 1 then args[0] else if |args| == 2 then args[1] else args[2];
      DecimalParseRelation(firstText);
      if Core.ParseDecimal(firstText).DecimalOk? {
        DecimalParseRelation(stepText);
        if Core.ParseDecimal(stepText).DecimalOk? &&
           Core.ParseDecimal(stepText).number.value != 0
        {
          DecimalParseRelation(lastText);
        }
      }
    }
  }

  lemma DigitCharEq(d: int)
    ensures Core.DigitChar(d) == Spec.DigitChar(d)
  {
  }

  lemma CalculatedMaxScaleEq(
    first: Core.Decimal,
    step: Core.Decimal,
    last: Core.Decimal
  )
    ensures Core.MaxScale(first, step, last) ==
            Spec.MaxScale(ToSpecDecimal(first), ToSpecDecimal(step), ToSpecDecimal(last))
  {
  }

  lemma CalculatedRescaleEq(decimal: Core.Decimal, scale: nat)
    requires decimal.scale <= scale
    ensures Core.Rescale(decimal, scale) ==
            Spec.Rescale(ToSpecDecimal(decimal), scale)
  {
    Pow10Eq(scale - decimal.scale);
  }

  lemma TermCountEq(first: int, step: int, last: int)
    requires step != 0
    ensures Core.TermCount(first, step, last) == Spec.TermCount(first, step, last)
  {
  }

  lemma GenerateValuesAt(current: int, step: int, count: nat)
    ensures |Core.GenerateValues(current, step, count)| == count
    ensures forall i: nat {:trigger Core.GenerateValues(current, step, count)[i]}
              | i < count ::
              Core.GenerateValues(current, step, count)[i] == current + i * step
    decreases count
  {
    if count > 0 {
      GenerateValuesAt(current + step, step, count - 1);
    }
  }

  lemma RenderValuesAt(values: seq<int>, scale: nat, firstNegativeZero: bool)
    ensures |Core.RenderValues(values, scale, firstNegativeZero)| == |values|
    ensures forall i: nat {:trigger Core.RenderValues(values, scale, firstNegativeZero)[i]}
              | i < |values| ::
              Core.RenderValues(values, scale, firstNegativeZero)[i] ==
              Core.RenderFixed(values[i], scale, i == 0 && firstNegativeZero)
    decreases |values|
  {
    if |values| > 0 {
      RenderValuesAt(values[1..], scale, false);
    }
  }

  lemma RenderFixedEq(value: int, scale: nat, negativeZero: bool)
    ensures Core.RenderFixed(value, scale, negativeZero) ==
            Spec.RenderFixed(value, scale, negativeZero)
  {
    if scale > 0 {
      Pow10Eq(scale);
    }
    DigitsAndPaddingEq(value, scale, negativeZero);
  }

  lemma DigitsAndPaddingEq(value: int, scale: nat, negativeZero: bool)
    ensures Core.RenderFixed(value, scale, negativeZero) ==
            Spec.RenderFixed(value, scale, negativeZero)
  {
    RenderMagnitudeEq(if value < 0 then -value else value, scale);
  }

  lemma RenderMagnitudeEq(magnitude: int, scale: nat)
    requires 0 <= magnitude
    ensures Core.RenderMagnitude(magnitude, scale) == Spec.RenderMagnitude(magnitude, scale)
  {
    if scale == 0 {
      DigitsUnsignedEq(magnitude);
    } else {
      Pow10Eq(scale);
      Spec.DivNonnegative(magnitude, Core.Pow10(scale));
      DigitsUnsignedEq(magnitude / Core.Pow10(scale));
      DigitsUnsignedEq(magnitude % Core.Pow10(scale));
      LeftPadZerosEq(Core.DigitsUnsigned(magnitude % Core.Pow10(scale)), scale);
    }
  }

  lemma DigitsUnsignedEq(n: int)
    requires 0 <= n
    ensures Core.DigitsUnsigned(n) == Spec.DigitsUnsigned(n)
    decreases n
  {
    if n >= 10 {
      DigitsUnsignedEq(n / 10);
    }
  }

  lemma ZerosEq(n: nat)
    ensures Core.Zeros(n) == Spec.Zeros(n)
    decreases n
  {
    if n > 0 {
      ZerosEq(n - 1);
    }
  }

  lemma LeftPadZerosEq(text: BW.Bytes, width: nat)
    ensures Core.LeftPadZeros(text, width) == Spec.LeftPadZeros(text, width)
  {
    if width > |text| {
      ZerosEq(width - |text|);
    }
  }

  lemma WidthRelation(items: seq<BW.Bytes>)
    ensures Spec.WidthRelation(items, Core.MaxWidth(items))
    decreases |items|
  {
    if |items| > 0 {
      WidthRelation(items[1..]);
    }
  }

  lemma PadNumberEq(text: BW.Bytes, width: nat)
    ensures Core.PadNumber(text, width) == Spec.PadNumber(text, width)
  {
    if width > |text| {
      ZerosEq(width - |text|);
    }
  }

  lemma PadValuesAt(items: seq<BW.Bytes>, width: nat)
    ensures |Core.PadValues(items, width)| == |items|
    ensures forall i: nat {:trigger Core.PadValues(items, width)[i]} | i < |items| ::
              Core.PadValues(items, width)[i] == Spec.PadNumber(items[i], width)
    decreases |items|
  {
    if |items| > 0 {
      PadNumberEq(items[0], width);
      PadValuesAt(items[1..], width);
    }
  }

  function OutputFragments(items: seq<BW.Bytes>, separator: BW.Bytes): seq<BW.Bytes>
    decreases |items|
  {
    if |items| == 0 then
      []
    else
      [items[0] + (if |items| == 1 then ['\n'] else separator)] +
      OutputFragments(items[1..], separator)
  }

  lemma PrefixShiftSlice(
    prefix: BW.Bytes,
    data: BW.Bytes,
    lo: nat,
    hi: nat
  )
    requires lo <= hi <= |data|
    ensures (prefix + data)[|prefix| + lo..|prefix| + hi] == data[lo..hi]
  {
  }

  lemma {:isolate_assertions} PrependFragmentCuts(
    head: BW.Bytes,
    tailFragments: seq<BW.Bytes>,
    tailOutput: BW.Bytes,
    tailCuts: seq<nat>
  )
    requires Spec.FragmentCutsRelation(tailFragments, tailOutput, tailCuts)
    ensures exists cuts: seq<nat> ::
              Spec.FragmentCutsRelation(
                [head] + tailFragments,
                head + tailOutput,
                cuts
              )
  {
    var shiftedTailCuts :=
      seq(|tailCuts|, i requires 0 <= i < |tailCuts| =>
        |head| + tailCuts[i]);
    var cuts := [0] + shiftedTailCuts;
    assert |cuts| == |[head] + tailFragments| + 1;
    assert cuts[0] == 0;
    assert cuts[|[head] + tailFragments|] == |head + tailOutput|;
    forall i: nat {:trigger cuts[i], cuts[i + 1]} |
      i < |[head] + tailFragments|
      ensures cuts[i] <= cuts[i + 1] <= |head + tailOutput| &&
              (head + tailOutput)[cuts[i]..cuts[i + 1]] ==
              ([head] + tailFragments)[i]
    {
      if i == 0 {
        assert cuts[1] == |head|;
        assert (head + tailOutput)[..|head|] == head;
      } else {
        var j := i - 1;
        assert j < |tailFragments|;
        assert cuts[i] == |head| + tailCuts[j];
        assert cuts[i + 1] == |head| + tailCuts[j + 1];
        PrefixShiftSlice(head, tailOutput, tailCuts[j], tailCuts[j + 1]);
      }
    }
    assert Spec.FragmentCutsRelation(
        [head] + tailFragments, head + tailOutput, cuts
      );
  }

  lemma JoinItemsFragments(items: seq<BW.Bytes>, separator: BW.Bytes)
    ensures |OutputFragments(items, separator)| == |items|
    ensures forall i: nat {:trigger OutputFragments(items, separator)[i]}
              | i < |items| ::
              OutputFragments(items, separator)[i] ==
              items[i] + (if i + 1 == |items| then ['\n'] else separator)
    ensures exists cuts: seq<nat> ::
              Spec.FragmentCutsRelation(
                OutputFragments(items, separator),
                Core.JoinItems(items, separator),
                cuts
              )
    decreases |items|
  {
    if |items| == 0 {
      assert OutputFragments(items, separator) == [];
      assert Core.JoinItems(items, separator) == [];
      assert Spec.FragmentCutsRelation([], [], [0]);
      assert exists cuts: seq<nat> ::
          Spec.FragmentCutsRelation([], [], cuts);
    } else if |items| == 1 {
      var fragment := items[0] + ['\n'];
      assert OutputFragments(items, separator) == [fragment];
      assert Core.JoinItems(items, separator) == fragment;
      assert Spec.FragmentCutsRelation([fragment], fragment, [0, |fragment|]);
      assert exists cuts: seq<nat> ::
          Spec.FragmentCutsRelation([fragment], fragment, cuts);
    } else {
      JoinItemsFragments(items[1..], separator);
      var tailCuts: seq<nat> :|
        Spec.FragmentCutsRelation(
          OutputFragments(items[1..], separator),
          Core.JoinItems(items[1..], separator),
          tailCuts
        );
      var head := items[0] + separator;
      PrependFragmentCuts(
        head,
        OutputFragments(items[1..], separator),
        Core.JoinItems(items[1..], separator),
        tailCuts
      );
      assert OutputFragments(items, separator) ==
             [head] + OutputFragments(items[1..], separator);
      assert Core.JoinItems(items, separator) ==
             head + Core.JoinItems(items[1..], separator);
      assert exists cuts: seq<nat> ::
          Spec.FragmentCutsRelation(
            OutputFragments(items, separator),
            Core.JoinItems(items, separator),
            cuts
          );
    }
  }

  lemma SequenceOutputRelation(
    first: Core.Decimal,
    step: Core.Decimal,
    last: Core.Decimal,
    equalWidth: bool,
    separator: BW.Bytes
  )
    requires step.value != 0
    ensures Spec.SequenceOutputRelation(
              ToSpecDecimal(first),
              ToSpecDecimal(step),
              ToSpecDecimal(last),
              equalWidth,
              separator,
              Core.RenderSequence(first, step, last, equalWidth, separator)
            )
  {
    CalculatedMaxScaleEq(first, step, last);
    var scale := Core.MaxScale(first, step, last);
    CalculatedRescaleEq(first, scale);
    CalculatedRescaleEq(step, scale);
    CalculatedRescaleEq(last, scale);
    var firstValue := Core.Rescale(first, scale);
    var stepValue := Core.Rescale(step, scale);
    var lastValue := Core.Rescale(last, scale);
    TermCountEq(firstValue, stepValue, lastValue);
    var count := Core.TermCount(firstValue, stepValue, lastValue);
    var values := Core.GenerateValues(firstValue, stepValue, count);
    GenerateValuesAt(firstValue, stepValue, count);
    var rendered := Core.RenderValues(values, scale, first.negativeZero && first.value == 0);
    RenderValuesAt(values, scale, first.negativeZero && first.value == 0);
    assert forall i: nat | i < count ::
        rendered[i] == Spec.RenderFixed(
          firstValue + i * stepValue,
          scale,
          i == 0 && first.negativeZero && first.value == 0
        ) by {
      forall i: nat | i < count
        ensures rendered[i] == Spec.RenderFixed(
                                 firstValue + i * stepValue,
                                 scale,
                                 i == 0 && first.negativeZero && first.value == 0
                               )
      {
        RenderFixedEq(firstValue + i * stepValue, scale,
                      i == 0 && first.negativeZero && first.value == 0);
      }
    }
    var width := Core.MaxWidth(rendered);
    WidthRelation(rendered);
    var items := if equalWidth then Core.PadValues(rendered, width) else rendered;
    if equalWidth {
      PadValuesAt(rendered, width);
    }
    assert Spec.SequenceItemsRelation(
        ToSpecDecimal(first),
        ToSpecDecimal(step),
        ToSpecDecimal(last),
        equalWidth,
        rendered,
        items,
        width
      );
    JoinItemsFragments(items, separator);
    var cuts: seq<nat> :|
      Spec.FragmentCutsRelation(
        OutputFragments(items, separator),
        Core.JoinItems(items, separator),
        cuts
      );
    assert Spec.SequenceOutputWitnessRelation(
        ToSpecDecimal(first),
        ToSpecDecimal(step),
        ToSpecDecimal(last),
        equalWidth,
        separator,
        Core.JoinItems(items, separator),
        rendered,
        items,
        width,
        OutputFragments(items, separator),
        cuts
      );
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.SeqCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    NumberPlanRelation(raw.operands);
    if !Core.HelpSelected(raw) && !Core.VersionSelected(raw) {
      match Core.ParseNumbers(raw.operands)
      case NumbersErr(_) =>
      case NumbersOk(first, step, last) =>
        SequenceOutputRelation(
          first,
          step,
          last,
          raw.equalWidth,
          Core.Separator(raw)
        );
    }
  }
}
