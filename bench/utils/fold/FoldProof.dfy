include "../../core/World.dfy"
include "FoldSchema.dfy"
include "FoldCore.dfy"
include "FoldSpec.dfy"

module FoldProof {
  import BenchIO
  import BenchWorld
  import Core = FoldCore
  import Spec = FoldSpec
  import Schema = FoldSchema

  lemma IsDigitEq(ch: char)
    ensures Core.IsDigit(ch) == Spec.IsDigit(ch)
  {
  }

  lemma DigitValueEq(ch: char)
    requires Core.IsDigit(ch)
    ensures Core.DigitValue(ch) == Spec.DigitValue(ch)
  {
  }

  lemma StepColumnEq(
    byteMode: bool,
    ch: char,
    column: nat
  )
    ensures Core.StepColumn(byteMode, ch, column) ==
            Spec.StepColumn(byteMode, ch, column)
  {
    if byteMode {
    } else if ch == '\U{0}' {
    } else if ch == '\U{8}' {
    } else if ch == '\r' {
    } else if ch == '\t' {
    }
  }

  lemma IsBlankEq(ch: char)
    ensures Core.IsBlank(ch) == Spec.IsBlank(ch)
  {
  }

  // Core folds left with an accumulator while `Spec.DecimalValue` peels the
  // last digit, so the bridge needs positional weights. They belong here.
  ghost function Pow10(power: nat): nat
    decreases power
  {
    if power == 0 then 1 else 10 * Pow10(power - 1)
  }

  lemma {:induction false} DecimalFrontPeel(digits: string)
    requires Spec.EveryDigit(digits)
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
      assert front[0] == digits[0];
      DecimalFrontPeel(front);
      assert front[1..] == digits[1..|digits| - 1];
      var tail := digits[1..];
      assert tail[..|tail| - 1] == digits[1..|digits| - 1];
      assert tail[|tail| - 1] == digits[|digits| - 1];
      assert Pow10(|digits| - 1) == 10 * Pow10(|digits| - 2);
    }
  }

  // The accumulator at position i carries the value of the consumed prefix.
  lemma {:induction false} NatParseAccumulator(text: string, i: nat, acc: nat)
    requires i <= |text|
    requires Spec.EveryDigit(text[i..])
    ensures Core.ParseNatFrom(text, i, acc) ==
            (var total := acc * Pow10(|text| - i) + Spec.DecimalValue(text[i..]);
             if total == 0 then Schema.NatErr else Schema.NatOk(total))
    decreases |text| - i
  {
    var suf := text[i..];
    if i < |text| {
      assert suf[0] == text[i];
      assert suf[1..] == text[i + 1..];
      assert |suf| == |text| - i;
      assert Spec.IsDigit(text[i]);
      IsDigitEq(text[i]);
      DigitValueEq(text[i]);
      NatParseAccumulator(text, i + 1, acc * 10 + Core.DigitValue(text[i]));
      DecimalFrontPeel(suf);
      assert (acc * 10 + Spec.DigitValue(text[i])) * Pow10(|text| - i - 1) +
             Spec.DecimalValue(text[i + 1..]) ==
             acc * Pow10(|text| - i) + Spec.DecimalValue(suf);
    }
  }

  lemma {:induction false} NatParseErrOnNonDigit(text: string, i: nat, acc: nat)
    requires i <= |text|
    requires !Spec.EveryDigit(text[i..])
    ensures Core.ParseNatFrom(text, i, acc) == Schema.NatErr
    decreases |text| - i
  {
    var suf := text[i..];
    assert |suf| > 0;
    if i < |text| {
      assert suf[0] == text[i];
      assert suf[1..] == text[i + 1..];
      IsDigitEq(text[i]);
      if Core.IsDigit(text[i]) {
        assert !Spec.EveryDigit(text[i + 1..]) by {
          var k :| 0 <= k < |suf| && !Spec.IsDigit(suf[k]);
          assert k != 0;
          assert suf[1..][k - 1] == suf[k];
        }
        NatParseErrOnNonDigit(text, i + 1, acc * 10 + Core.DigitValue(text[i]));
      }
    }
  }

  lemma PositiveNatSatisfies(text: string)
    ensures Spec.PositiveNatRelation(
              text, Core.ParsePositiveNat(text)
            )
  {
    if |text| > 0 {
      assert text[0..] == text;
      if Spec.EveryDigit(text) {
        NatParseAccumulator(text, 0, 0);
        assert 0 * Pow10(|text|) == 0;
      } else {
        NatParseErrOnNonDigit(text, 0, 0);
      }
    }
  }

  lemma WidthArgsSatisfy(
    args: seq<Schema.WidthArg>,
    width: nat
  )
    requires width > 0
    ensures Spec.WidthArgsRelation(
              args, width, Core.ParseWidthArgs(args, width)
            )
    decreases |args|
  {
    if |args| > 0 {
      PositiveNatSatisfies(args[0].text);
      match Core.ParsePositiveNat(args[0].text)
      case NatErr =>
      case NatOk(nextWidth) =>
        if nextWidth > 0 {
          WidthArgsSatisfy(args[1..], nextWidth);
        }
    }
  }

  lemma InputsFromOperandsElement(
    operands: seq<string>,
    i: nat
  )
    requires i < |operands|
    ensures Core.InputsFromOperands(operands)[i] ==
            (if operands[i] == "-"
             then Schema.Stdin
             else Schema.File(operands[i]))
    decreases i
  {
    if i > 0 {
      InputsFromOperandsElement(operands[1..], i - 1);
    }
  }

  lemma InputsSatisfy(operands: seq<string>)
    ensures Spec.InputsRelation(
              operands,
              if |Core.InputsFromOperands(operands)| == 0
              then [Schema.Stdin]
              else Core.InputsFromOperands(operands)
            )
  {
    if |operands| > 0 {
      assert |Core.InputsFromOperands(operands)| == |operands| by {
        calc {
           |Core.InputsFromOperands(operands)|;
        == 1 + |Core.InputsFromOperands(operands[1..])|;
        == 1 + |operands[1..]|;
        == |operands|;
        }
      }
      forall i: nat | i < |operands|
        ensures Core.InputsFromOperands(operands)[i] ==
                (if operands[i] == "-"
                 then Schema.Stdin
                 else Schema.File(operands[i]))
      {
        InputsFromOperandsElement(operands, i);
      }
    }
  }

  lemma CommandSatisfies(raw: Schema.FoldCmdRaw)
    ensures Spec.CommandRelation(raw, Core.Command(raw))
  {
    WidthArgsSatisfy(raw.widthArgs, 80);
    var widthPlan := Core.ParseWidthArgs(raw.widthArgs, 80);
    if !Core.HelpBeforeOther(raw) &&
       !Core.VersionBeforeInvalid(raw) &&
       !widthPlan.hasInvalid {
      InputsSatisfy(raw.operands);
    }
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.FoldCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    CommandSatisfies(raw);
    reveal Core.CoreSummary();
    reveal Spec.Spec();
    var cmd := Core.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else if cmd.mode == Schema.ModeInvalidWidth {
    } else {
      assert exists stdoutPart: BenchWorld.Bytes,
          stderrPart: BenchWorld.Bytes,
          hadError: bool ::
          Spec.InputTraceRelation(
            cmd,
            old(io.fs()),
            old(io.stdin()),
            io.stdin(),
            stdoutPart,
            stderrPart,
            hadError
          ) &&
          io.stdout() == old(io.stdout()) + stdoutPart &&
          io.stderr() == old(io.stderr()) + stderrPart &&
          exit == (if hadError then 1 else 0);
    }
  }
}
