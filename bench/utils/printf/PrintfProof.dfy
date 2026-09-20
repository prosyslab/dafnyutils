include "../../core/World.dfy"
include "PrintfSchema.dfy"
include "PrintfCore.dfy"
include "PrintfSpec.dfy"

module PrintfProof {
  import BenchIO
  import BW = BenchWorld
  import Schema = PrintfSchema
  import Core = PrintfCore
  import Spec = PrintfSpec

  lemma ClassifyFragmentIff(
    format: string,
    args: seq<string>,
    start: nat,
    nextArg: nat,
    end: nat,
    afterArg: nat,
    output: BW.Bytes
  )
    requires start < |format|
    requires nextArg <= |args|
    ensures (Core.ClassifyFragment(format, args, start, nextArg) ==
             Spec.OneFragment(Spec.FormatFragment(end, afterArg, output))) ==
            Spec.FormatFragmentRelation(
              format, args, start, nextArg, end, afterArg, output)
  {
  }

  lemma RenderPassOkIndependentStartArg(
    format: string,
    args: seq<string>,
    start: nat,
    leftArg: nat,
    rightArg: nat
  )
    requires start <= |format|
    requires leftArg <= |args|
    requires rightArg <= |args|
    ensures Core.RenderPass(format, args, start, leftArg).0 ==
            Core.RenderPass(format, args, start, rightArg).0
    decreases |format| - start
  {
    if start < |format| {
      match Core.ClassifyFragment(format, args, start, leftArg)
      case NoFragment =>
      case OneFragment(left) =>
        match Core.ClassifyFragment(format, args, start, rightArg)
        case NoFragment =>
        case OneFragment(right) =>
          assert left.end == right.end;
          RenderPassOkIndependentStartArg(
            format, args, left.end, left.afterArg, right.afterArg);
    }
  }

  lemma RenderPassErrorShape(
    format: string,
    args: seq<string>,
    start: nat,
    startArg: nat
  )
    requires start <= |format|
    requires startArg <= |args|
    ensures !Core.RenderPass(format, args, start, startArg).0 ==>
              Core.RenderPass(format, args, start, startArg).1 == [] &&
              Core.RenderPass(format, args, start, startArg).3 == Spec.UnsupportedFormatMessage()
    decreases |format| - start
  {
    if start < |format| {
      match Core.ClassifyFragment(format, args, start, startArg)
      case NoFragment =>
      case OneFragment(fragment) =>
        RenderPassErrorShape(format, args, fragment.end, fragment.afterArg);
    }
  }

  lemma RenderPassProgressIndependentStartArg(
    format: string,
    args: seq<string>,
    start: nat,
    leftArg: nat,
    rightArg: nat
  )
    requires start <= |format|
    requires leftArg < |args|
    requires rightArg < |args|
    requires Core.RenderPass(format, args, start, leftArg).0
    ensures (Core.RenderPass(format, args, start, leftArg).2 > leftArg) ==
            (Core.RenderPass(format, args, start, rightArg).2 > rightArg)
    decreases |format| - start
  {
    if start < |format| {
      match Core.ClassifyFragment(format, args, start, leftArg)
      case NoFragment =>
      case OneFragment(left) =>
        match Core.ClassifyFragment(format, args, start, rightArg)
        case NoFragment =>
        case OneFragment(right) =>
          assert left.end == right.end;
          if left.afterArg == leftArg {
            assert right.afterArg == rightArg;
            RenderPassProgressIndependentStartArg(
              format, args, left.end, left.afterArg, right.afterArg);
          } else {
            assert left.afterArg > leftArg;
            assert right.afterArg > rightArg;
            RenderPassOkIndependentStartArg(
              format, args, start, leftArg, rightArg);
          }
    }
  }

  lemma RenderRepeatedFromSucceeds(
    format: string,
    args: seq<string>,
    startArg: nat
  )
    requires startArg <= |args|
    requires Core.RenderPass(format, args, 0, startArg).0
    ensures Core.RenderRepeatedFrom(format, args, startArg).0
    decreases |args| - startArg
  {
    var pass := Core.RenderPass(format, args, 0, startArg);
    if startArg < pass.2 < |args| {
      RenderPassOkIndependentStartArg(format, args, 0, startArg, pass.2);
      RenderRepeatedFromSucceeds(format, args, pass.2);
    }
  }

  lemma BuildFormatDerivation(
    format: string,
    args: seq<string>,
    start: nat,
    startArg: nat
  ) returns (derivation: Spec.FormatDerivation)
    requires start <= |format|
    requires startArg <= |args|
    ensures Core.RenderPass(format, args, start, startArg).0 ==>
              Spec.FormatDerivationRelation(
                format, args, start, startArg,
                Core.RenderPass(format, args, start, startArg).2,
                Core.RenderPass(format, args, start, startArg).1,
                derivation)
    decreases |format| - start
  {
    if start == |format| {
      derivation := Spec.FormatDone;
    } else {
      match Core.ClassifyFragment(format, args, start, startArg)
      case NoFragment =>
        derivation := Spec.FormatDone;
      case OneFragment(fragment) =>
        var rest := Core.RenderPass(format, args, fragment.end, fragment.afterArg);
        var restDerivation := BuildFormatDerivation(
          format, args, fragment.end, fragment.afterArg);
        derivation := Spec.FormatStep(fragment, rest.1, restDerivation);
    }
  }

  lemma FormatDerivationDeterminesPass(
    format: string,
    args: seq<string>,
    start: nat,
    startArg: nat,
    used: nat,
    output: BW.Bytes,
    derivation: Spec.FormatDerivation
  )
    requires Spec.FormatDerivationRelation(
               format, args, start, startArg, used, output, derivation)
    ensures Core.RenderPass(format, args, start, startArg) == (true, output, used, [])
    decreases derivation
  {
    match derivation
    case FormatDone =>
    case FormatStep(fragment, restOutput, rest) =>
      FormatDerivationDeterminesPass(
        format, args, fragment.end, fragment.afterArg, used, restOutput, rest);
  }

  lemma BuildRepeatedDerivation(
    format: string,
    args: seq<string>,
    startArg: nat
  ) returns (derivation: Spec.RepeatedDerivation)
    requires startArg <= |args|
    ensures Core.RenderRepeatedFrom(format, args, startArg).0 ==>
              (Core.RenderPass(format, args, 0, startArg).2 == startArg ||
               Spec.RepeatedPassesFromRelation(
                 format, args, startArg,
                 Core.RenderRepeatedFrom(format, args, startArg).1,
                 derivation))
    decreases |args| - startArg
  {
    var pass := Core.RenderPass(format, args, 0, startArg);
    if pass.0 && pass.2 > startArg {
      var passDerivation := BuildFormatDerivation(format, args, 0, startArg);
      assert Spec.FormatPassRelation(format, args, startArg, pass.2, pass.1) by {
        assert exists d: Spec.FormatDerivation ::
            Spec.FormatDerivationRelation(
              format, args, 0, startArg, pass.2, pass.1, d) by {
          ghost var d := passDerivation;
        }
      }
      if pass.2 >= |args| {
        derivation := Spec.RepeatedStep(pass.2, pass.1, [], Spec.RepeatedDone);
      } else {
        RenderPassOkIndependentStartArg(format, args, 0, startArg, pass.2);
        RenderPassProgressIndependentStartArg(format, args, 0, startArg, pass.2);
        RenderRepeatedFromSucceeds(format, args, pass.2);
        var rest := Core.RenderRepeatedFrom(format, args, pass.2);
        assert Core.RenderPass(format, args, 0, pass.2).2 > pass.2;
        var restDerivation := BuildRepeatedDerivation(format, args, pass.2);
        assert Spec.RepeatedPassesFromRelation(
            format, args, pass.2, rest.1, restDerivation);
        derivation := Spec.RepeatedStep(pass.2, pass.1, rest.1, restDerivation);
      }
    } else {
      derivation := Spec.RepeatedDone;
    }
  }

  lemma RenderRepeatedRefines(format: string, args: seq<string>)
    ensures Spec.RenderRelation(
              format, args,
              Core.RenderRepeated(format, args).0,
              Core.RenderRepeated(format, args).1,
              Core.RenderRepeated(format, args).2)
  {
    var pass := Core.RenderPass(format, args, 0, 0);
    if pass.0 {
      var passDerivation := BuildFormatDerivation(format, args, 0, 0);
      assert Spec.FormatPassRelation(format, args, 0, pass.2, pass.1) by {
        assert exists d: Spec.FormatDerivation ::
            Spec.FormatDerivationRelation(format, args, 0, 0, pass.2, pass.1, d) by {
          ghost var d := passDerivation;
        }
      }
      if pass.2 > 0 {
        RenderRepeatedFromSucceeds(format, args, 0);
        var repeatedDerivation := BuildRepeatedDerivation(format, args, 0);
        assert Spec.RepeatedPassesFromRelation(
            format, args, 0, Core.RenderRepeated(format, args).1, repeatedDerivation);
      }
    } else {
      RenderPassErrorShape(format, args, 0, 0);
      assert !(exists passOutput: BW.Bytes, used: nat ::
                 Spec.FormatPassRelation(format, args, 0, used, passOutput)) by {
        if exists passOutput: BW.Bytes, used: nat ::
            Spec.FormatPassRelation(format, args, 0, used, passOutput) {
          var passOutput: BW.Bytes, used: nat :|
            Spec.FormatPassRelation(format, args, 0, used, passOutput);
          var derivation: Spec.FormatDerivation :|
            Spec.FormatDerivationRelation(
              format, args, 0, 0, used, passOutput, derivation);
          FormatDerivationDeterminesPass(
            format, args, 0, 0, used, passOutput, derivation);
        }
      }
    }
  }

  lemma EvaluateRefines(raw: Schema.PrintfCmdRaw)
    ensures Spec.EvaluationRelation(
              raw, Core.Evaluate(raw).0, Core.Evaluate(raw).1, Core.Evaluate(raw).2)
  {
    if !Schema.HelpSelected(raw) &&
       !Schema.VersionSelected(raw) &&
       |raw.operands| > 0 {
      RenderRepeatedRefines(raw.operands[0], raw.operands[1..]);
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.PrintfCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    EvaluateRefines(raw);
  }
}
