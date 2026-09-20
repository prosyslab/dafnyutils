include "Base64Schema.dfy"
include "Base64Core.dfy"
include "Base64Spec.dfy"

module Base64Proof {
  import BenchIO
  import BW = BenchWorld
  import Schema = Base64Schema
  import Core = Base64Core
  import Spec = Base64Spec

  lemma ParseNatFromCharacterization(
    text: string,
    i: nat,
    acc: nat
  )
    requires i <= |text|
    ensures forall value: nat ::
              Spec.DecimalValueFromRelation(text, i, acc, value) ==
              (Core.ParseNatFrom(text, i, acc) ==
               Core.NatOk(value))
    decreases |text| - i
  {
    forall value: nat
      ensures
        Spec.DecimalValueFromRelation(text, i, acc, value) ==
        (Core.ParseNatFrom(text, i, acc) ==
         Core.NatOk(value))
    {
      reveal Spec.DecimalValueFromRelation();
      reveal Core.ParseNatFrom();
      if i < |text| {
        reveal Core.IsDigit();
        if '0' <= text[i] <= '9' {
          reveal Core.DigitValue();
          ParseNatFromCharacterization(
            text,
            i + 1,
            acc * 10 +
            (((text[i] as int) - ('0' as int)) as nat)
          );
        }
      }
    }
  }

  lemma ParseNatCharacterization(text: string)
    ensures forall value: nat ::
              Spec.DecimalValueRelation(text, value) ==
              (Core.ParseNat(text) == Core.NatOk(value))
  {
    reveal Spec.DecimalValueRelation();
    reveal Core.ParseNat();
    if |text| > 0 {
      ParseNatFromCharacterization(text, 0, 0);
    }
  }

  lemma FirstInvalidWrapUnique(
    args: seq<Schema.WidthArg>,
    first: nat,
    second: nat
  )
    requires Spec.FirstInvalidWrap(args, first)
    requires Spec.FirstInvalidWrap(args, second)
    ensures first == second
  {
    reveal Spec.FirstInvalidWrap();
    if first == 0 && second > 0 {
      var value: nat :|
        Spec.DecimalValueRelation(args[0].text, value);
      assert false;
    } else if second == 0 && first > 0 {
      var value: nat :|
        Spec.DecimalValueRelation(args[0].text, value);
      assert false;
    } else if first > 0 && second > 0 {
      FirstInvalidWrapUnique(
        args[1..], first - 1, second - 1
      );
    }
  }

  lemma FirstInvalidHasNoValue(
    args: seq<Schema.WidthArg>,
    index: nat
  )
    requires Spec.FirstInvalidWrap(args, index)
    ensures !(exists value: nat ::
                Spec.DecimalValueRelation(args[index].text, value))
    decreases index
  {
    reveal Spec.FirstInvalidWrap();
    if index > 0 {
      FirstInvalidHasNoValue(args[1..], index - 1);
    }
  }

  lemma AllWrapsValidAt(
    args: seq<Schema.WidthArg>,
    index: nat
  ) returns (value: nat)
    requires Spec.AllWrapsValid(args)
    requires index < |args|
    ensures Spec.DecimalValueRelation(
              args[index].text, value
            )
    decreases index
  {
    reveal Spec.AllWrapsValid();
    if index == 0 {
      value :|
        Spec.DecimalValueRelation(args[0].text, value);
    } else {
      value := AllWrapsValidAt(args[1..], index - 1);
    }
  }

  lemma PrependValidToFirstInvalid(
    head: Schema.WidthArg,
    tail: seq<Schema.WidthArg>,
    index: nat
  )
    requires exists value: nat ::
               Spec.DecimalValueRelation(head.text, value)
    requires Spec.FirstInvalidWrap(tail, index)
    ensures Spec.FirstInvalidWrap([head] + tail, index + 1)
  {
    var value: nat :|
      Spec.DecimalValueRelation(head.text, value);
    reveal Spec.FirstInvalidWrap();
    assert Spec.DecimalValueRelation(
        ([head] + tail)[0].text, value
      );
    assert Spec.FirstInvalidWrap(
        ([head] + tail)[1..], index
      );
  }

  lemma PrependValidToAllValid(
    head: Schema.WidthArg,
    tail: seq<Schema.WidthArg>
  )
    requires exists value: nat ::
               Spec.DecimalValueRelation(head.text, value)
    requires Spec.AllWrapsValid(tail)
    ensures Spec.AllWrapsValid([head] + tail)
  {
    var value: nat :|
      Spec.DecimalValueRelation(head.text, value);
    reveal Spec.AllWrapsValid();
    assert Spec.DecimalValueRelation(
        ([head] + tail)[0].text, value
      );
    assert Spec.AllWrapsValid(([head] + tail)[1..]);
  }

  lemma ParseWrapArgsCharacterization(
    args: seq<Schema.WidthArg>,
    initialWidth: nat
  )
    ensures var plan := Core.ParseWrapArgs(args, initialWidth);
            plan.hasInvalid ==>
              exists i: nat ::
                Spec.FirstInvalidWrap(args, i) &&
                plan.invalidText == args[i].text &&
                plan.invalidTokenIndex == args[i].tokenIndex
    ensures var plan := Core.ParseWrapArgs(args, initialWidth);
            !plan.hasInvalid ==> Spec.AllWrapsValid(args)
    ensures var plan := Core.ParseWrapArgs(args, initialWidth);
            !plan.hasInvalid && |args| == 0 ==>
              plan.width == initialWidth
    ensures var plan := Core.ParseWrapArgs(args, initialWidth);
            !plan.hasInvalid && |args| > 0 ==>
              Spec.DecimalValueRelation(
                args[|args| - 1].text,
                plan.width
              )
    decreases |args|
  {
    if |args| == 0 {
      reveal Spec.AllWrapsValid();
    } else {
      ParseNatCharacterization(args[0].text);
      match Core.ParseNat(args[0].text) {
        case NatErr =>
          reveal Spec.FirstInvalidWrap();
                 forall value: nat
                   ensures !Spec.DecimalValueRelation(
                             args[0].text, value
                           )
                 {
                   assert Core.ParseNat(args[0].text) !=
                          Core.NatOk(value);
                 }
                 assert !(exists value: nat ::
                            Spec.DecimalValueRelation(
                              args[0].text, value
                            ));
                 assert Spec.FirstInvalidWrap(args, 0);
                 assert exists i: nat ::
                     i == 0 &&
                     Spec.FirstInvalidWrap(args, i);
        case NatOk(nextWidth) =>
          ParseWrapArgsCharacterization(args[1..], nextWidth);
          var tailPlan :=
            Core.ParseWrapArgs(args[1..], nextWidth);
          if tailPlan.hasInvalid {
            var tailIndex: nat :|
              Spec.FirstInvalidWrap(args[1..], tailIndex) &&
              tailPlan.invalidText ==
              args[1..][tailIndex].text &&
              tailPlan.invalidTokenIndex ==
              args[1..][tailIndex].tokenIndex;
            var index := tailIndex + 1;
            assert args == [args[0]] + args[1..];
            PrependValidToFirstInvalid(
              args[0], args[1..], tailIndex
            );
            assert Spec.FirstInvalidWrap(args, index);
          } else {
            assert args == [args[0]] + args[1..];
            PrependValidToAllValid(args[0], args[1..]);
            if |args| == 1 {
              assert tailPlan.width == nextWidth;
            }
            assert Spec.AllWrapsValid(args);
          }
      }
    }
  }

  lemma InputsFromOperandsSatisfies(operands: seq<string>)
    ensures Spec.InputsRelation(
              operands,
              Core.InputsFromOperands(operands)
            )
    decreases |operands|
  {
    reveal Spec.InputsRelation();
    if |operands| > 0 {
      InputsFromOperandsSatisfies(operands[1..]);
    }
  }

  lemma CommandSatisfiesRelation(raw: Schema.Base64CmdRaw)
    ensures Spec.CommandRelation(raw, Core.Command(raw))
  {
    var plan := Core.ParseWrapArgs(raw.wrapArgs, 76);
    ParseWrapArgsCharacterization(raw.wrapArgs, 76);
    InputsFromOperandsSatisfies(raw.operands);

    assert Core.HelpBeforeInvalid(raw) ==
           Spec.HelpSelected(raw) by {
      reveal Core.HelpBeforeInvalid();
      reveal Spec.HelpSelected();
      if plan.hasInvalid {
        var first: nat :|
          Spec.FirstInvalidWrap(raw.wrapArgs, first) &&
          plan.invalidText == raw.wrapArgs[first].text &&
          plan.invalidTokenIndex ==
          raw.wrapArgs[first].tokenIndex;
        forall i: nat | Spec.FirstInvalidWrap(raw.wrapArgs, i)
          ensures
            (raw.helpTokenIndex <=
             raw.wrapArgs[i].tokenIndex) ==
            (raw.helpTokenIndex <= plan.invalidTokenIndex)
        {
          FirstInvalidWrapUnique(raw.wrapArgs, first, i);
          assert i == first;
          calc {
             raw.wrapArgs[i].tokenIndex;
          == raw.wrapArgs[first].tokenIndex;
          == plan.invalidTokenIndex;
          }
          assert
            (raw.helpTokenIndex <=
             raw.wrapArgs[i].tokenIndex) ==>
              (raw.helpTokenIndex <= plan.invalidTokenIndex);
          assert
            (raw.helpTokenIndex <= plan.invalidTokenIndex) ==>
              (raw.helpTokenIndex <=
               raw.wrapArgs[i].tokenIndex);
        }
      } else {
        forall i: nat | Spec.FirstInvalidWrap(raw.wrapArgs, i)
          ensures false
        {
          FirstInvalidHasNoValue(raw.wrapArgs, i);
          var value :=
            AllWrapsValidAt(raw.wrapArgs, i);
          assert false;
        }
      }
    }
    assert Core.VersionBeforeInvalid(raw) ==
           Spec.VersionSelected(raw) by {
      reveal Core.VersionBeforeInvalid();
      reveal Spec.VersionSelected();
      if plan.hasInvalid {
        var first: nat :|
          Spec.FirstInvalidWrap(raw.wrapArgs, first) &&
          plan.invalidText == raw.wrapArgs[first].text &&
          plan.invalidTokenIndex ==
          raw.wrapArgs[first].tokenIndex;
        forall i: nat | Spec.FirstInvalidWrap(raw.wrapArgs, i)
          ensures
            (raw.versionTokenIndex <=
             raw.wrapArgs[i].tokenIndex) ==
            (raw.versionTokenIndex <= plan.invalidTokenIndex)
        {
          FirstInvalidWrapUnique(raw.wrapArgs, first, i);
          assert i == first;
          calc {
             raw.wrapArgs[i].tokenIndex;
          == raw.wrapArgs[first].tokenIndex;
          == plan.invalidTokenIndex;
          }
          assert
            (raw.versionTokenIndex <=
             raw.wrapArgs[i].tokenIndex) ==>
              (raw.versionTokenIndex <= plan.invalidTokenIndex);
          assert
            (raw.versionTokenIndex <= plan.invalidTokenIndex) ==>
              (raw.versionTokenIndex <=
               raw.wrapArgs[i].tokenIndex);
        }
      } else {
        forall i: nat | Spec.FirstInvalidWrap(raw.wrapArgs, i)
          ensures false
        {
          FirstInvalidHasNoValue(raw.wrapArgs, i);
          var value :=
            AllWrapsValidAt(raw.wrapArgs, i);
          assert false;
        }
      }
    }

    reveal Spec.CommandRelation();
    reveal Spec.RunOrExtraAtWidth();
    reveal Spec.RunInputsRelation();
    reveal Core.Command();
    if !plan.hasInvalid {
      forall i: nat | Spec.FirstInvalidWrap(raw.wrapArgs, i)
        ensures false
      {
        FirstInvalidHasNoValue(raw.wrapArgs, i);
        var value := AllWrapsValidAt(raw.wrapArgs, i);
        assert false;
      }
    }
    if |raw.operands| <= 1 && |raw.operands| > 0 {
      assert Spec.InputsRelation(
          raw.operands,
          Core.InputsFromOperands(raw.operands)
        );
    }
    if !Core.HelpBeforeInvalid(raw) &&
       !Core.VersionBeforeInvalid(raw) &&
       |raw.wrapArgs| > 0 &&
       plan.hasInvalid {
      var i: nat :|
        Spec.FirstInvalidWrap(raw.wrapArgs, i) &&
        plan.invalidText == raw.wrapArgs[i].text &&
        plan.invalidTokenIndex ==
        raw.wrapArgs[i].tokenIndex;
    } else if !Core.HelpBeforeInvalid(raw) &&
              !Core.VersionBeforeInvalid(raw) &&
              |raw.wrapArgs| > 0 &&
              !plan.hasInvalid {
      assert Spec.AllWrapsValid(raw.wrapArgs);
      assert Spec.DecimalValueRelation(
          raw.wrapArgs[|raw.wrapArgs| - 1].text,
          plan.width
        );
      assert Spec.RunOrExtraAtWidth(
          raw, plan.width, Core.Command(raw)
        );
      assert exists width: nat
          {:trigger Spec.DecimalValueRelation(
            raw.wrapArgs[|raw.wrapArgs| - 1].text,
            width
          )} ::
          Spec.AllWrapsValid(raw.wrapArgs) &&
          Spec.DecimalValueRelation(
            raw.wrapArgs[|raw.wrapArgs| - 1].text,
            width
          ) &&
          Spec.RunOrExtraAtWidth(
            raw, width, Core.Command(raw)
          );
    }
  }

  lemma AlphabetEq(index: nat)
    requires index < 64
    ensures Core.Alphabet(index) == Spec.Alphabet(index)
  {
  }

  lemma ByteValueEq(ch: char)
    ensures Core.ByteValue(ch) == Spec.ByteValue(ch)
  {
  }

  lemma ByteCharEq(value: nat)
    ensures Core.ByteChar(value) == Spec.ByteChar(value)
  {
  }

  lemma DecodeValueEq(ch: char)
    ensures Core.DecodeValue(ch) == Spec.DecodeValue(ch)
  {
  }

  lemma Valid64Eq(ch: char)
    ensures Core.Valid64(ch) == Spec.Valid64(ch)
  {
    DecodeValueEq(ch);
  }

  lemma KeptInputRelationImpliesSpec(
    data: BW.Bytes,
    ignoreGarbage: bool,
    kept: BW.Bytes,
    indices: seq<nat>
  )
    requires Core.KeptInputRelation(
               data, ignoreGarbage, kept, indices
             )
    ensures Spec.KeptInputRelation(
              data, ignoreGarbage, kept, indices
            )
  {
    reveal Core.KeptInputRelation();
    reveal Spec.KeptInputRelation();
    reveal Core.StrictlyIncreasing();
    reveal Spec.StrictlyIncreasing();
    forall i: nat | i < |data|
      ensures Core.Valid64(data[i]) ==
              Spec.Valid64(data[i])
    {
      Valid64Eq(data[i]);
    }
  }

  lemma EncodeBlockRelationEquivalent(
    data: BW.Bytes,
    encoded: BW.Bytes,
    block: nat
  )
    requires block < (|data| + 2) / 3
    requires |encoded| == 4 * ((|data| + 2) / 3)
    ensures Core.EncodeBlockRelation(data, encoded, block) ==
            Spec.EncodeBlockRelation(data, encoded, block)
  {
    reveal Core.EncodeBlockRelation();
    reveal Spec.EncodeBlockRelation();
    var input := 3 * block;
    ByteValueEq(data[input]);
    if input + 1 < |data| {
      ByteValueEq(data[input + 1]);
    }
    if input + 2 < |data| {
      ByteValueEq(data[input + 2]);
    }
  }

  lemma EncodeRelationImpliesSpec(
    data: BW.Bytes,
    encoded: BW.Bytes
  )
    requires Core.EncodeRelation(data, encoded)
    ensures Spec.EncodeRelation(data, encoded)
  {
    reveal Core.EncodeRelation();
    reveal Spec.EncodeRelation();
    forall block: nat | block < (|data| + 2) / 3
      ensures Spec.EncodeBlockRelation(data, encoded, block)
    {
      EncodeBlockRelationEquivalent(data, encoded, block);
    }
  }

  lemma FragmentsConcatenateImpliesSpec(
    fragments: seq<BW.Bytes>,
    combined: BW.Bytes,
    cuts: seq<nat>
  )
    requires Core.FragmentsConcatenate(
               fragments, combined, cuts
             )
    ensures Spec.FragmentsConcatenate(
              fragments, combined, cuts
            )
  {
    reveal Core.FragmentsConcatenate();
    reveal Spec.FragmentsConcatenate();
  }

  lemma {:isolate_assertions}
    WrappedWitnessRelationImpliesSpec(
    encoded: BW.Bytes,
    width: nat,
    output: BW.Bytes,
    chunks: seq<BW.Bytes>,
    cuts: seq<nat>
  )
    requires width > 0
    requires Core.WrappedWitnessRelation(
               encoded, width, output, chunks, cuts
             )
    ensures Spec.WrappedWitnessRelation(
              encoded, width, output, chunks, cuts
            )
  {
    assert (|encoded| == 0) == (|chunks| == 0);
    forall line: int {:trigger chunks[line]} |
      0 <= line < |chunks|
      ensures
        var start := line * width;
        var end :=
          if (line + 1) * width < |encoded|
          then (line + 1) * width
          else |encoded|;
        start < |encoded| &&
        start < end <= |encoded| &&
        chunks[line] == encoded[start..end] + ['\n'] &&
        (line + 1 < |chunks| ==>
           (line + 1) * width < |encoded|) &&
        (line + 1 == |chunks| ==>
           (line + 1) * width >= |encoded|)
    {
      assert chunks[line] == chunks[line];
    }
    assert Spec.FragmentsConcatenate(chunks, output, cuts) by {
      FragmentsConcatenateImpliesSpec(chunks, output, cuts);
    }
  }

  lemma WrappedRelationImpliesSpec(
    encoded: BW.Bytes,
    width: nat,
    output: BW.Bytes
  )
    requires Core.WrappedRelation(encoded, width, output)
    ensures Spec.WrappedRelation(encoded, width, output)
  {
    reveal Core.WrappedRelation();
    reveal Spec.WrappedRelation();
    if width > 0 {
      var chunks: seq<BW.Bytes>, cuts: seq<nat> :|
        Core.WrappedWitnessRelation(
          encoded, width, output, chunks, cuts
        );
      WrappedWitnessRelationImpliesSpec(
        encoded, width, output, chunks, cuts
      );
    }
  }

  lemma DecodeFullBlockRelationEquivalent(
    data: BW.Bytes,
    start: nat,
    output: BW.Bytes
  )
    requires start + 4 <= |data|
    ensures Core.DecodeFullBlockRelation(
              data, start, output
            ) == Spec.DecodeFullBlockRelation(
                   data, start, output
                 )
  {
    reveal Core.DecodeFullBlockRelation();
    reveal Spec.DecodeFullBlockRelation();
    Valid64Eq(data[start]);
    Valid64Eq(data[start + 1]);
    Valid64Eq(data[start + 2]);
    Valid64Eq(data[start + 3]);
    DecodeValueEq(data[start]);
    DecodeValueEq(data[start + 1]);
    DecodeValueEq(data[start + 2]);
    DecodeValueEq(data[start + 3]);
  }

  lemma DecodeTerminalRelationImpliesSpec(
    data: BW.Bytes,
    output: BW.Bytes,
    ok: bool
  )
    requires Core.DecodeTerminalRelation(data, output, ok)
    ensures Spec.DecodeTerminalRelation(data, output, ok)
  {
    reveal Core.DecodeTerminalRelation();
    reveal Spec.DecodeTerminalRelation();
    if |data| >= 4 {
      forall fullOutput: BW.Bytes
        ensures Core.DecodeFullBlockRelation(
                  data, 0, fullOutput
                ) == Spec.DecodeFullBlockRelation(
                       data, 0, fullOutput
                     )
      {
        DecodeFullBlockRelationEquivalent(
          data, 0, fullOutput
        );
      }
    }
    if |data| >= 2 {
      Valid64Eq(data[0]);
      Valid64Eq(data[1]);
      DecodeValueEq(data[0]);
      DecodeValueEq(data[1]);
    }
    if |data| >= 3 {
      Valid64Eq(data[2]);
      DecodeValueEq(data[2]);
    }
  }

  lemma DecodeWitnessRelationImpliesSpec(
    data: BW.Bytes,
    output: BW.Bytes,
    ok: bool,
    blocks: nat,
    fragments: seq<BW.Bytes>,
    cuts: seq<nat>
  )
    requires Core.DecodeWitnessRelation(
               data, output, ok, blocks, fragments, cuts
             )
    ensures Spec.DecodeWitnessRelation(
              data, output, ok, blocks, fragments, cuts
            )
  {
    reveal Core.DecodeWitnessRelation();
    reveal Spec.DecodeWitnessRelation();
    forall block: nat | block < blocks
      ensures Spec.DecodeFullBlockRelation(
                data, 4 * block, fragments[block]
              )
    {
      DecodeFullBlockRelationEquivalent(
        data, 4 * block, fragments[block]
      );
    }
    DecodeTerminalRelationImpliesSpec(
      data[4 * blocks..],
      fragments[blocks],
      ok
    );
    FragmentsConcatenateImpliesSpec(
      fragments, output, cuts
    );
  }

  lemma DecodeRelationImpliesSpec(
    data: BW.Bytes,
    output: BW.Bytes,
    ok: bool
  )
    requires Core.DecodeRelation(data, output, ok)
    ensures Spec.DecodeRelation(data, output, ok)
  {
    reveal Core.DecodeRelation();
    reveal Spec.DecodeRelation();
    var blocks: nat,
        fragments: seq<BW.Bytes>,
        cuts: seq<nat> :|
      Core.DecodeWitnessRelation(
        data, output, ok, blocks, fragments, cuts
      );
    DecodeWitnessRelationImpliesSpec(
      data, output, ok, blocks, fragments, cuts
    );
  }

  lemma TransformRelationImpliesSpec(
    cmd: Schema.Base64Cmd,
    data: BW.Bytes,
    output: BW.Bytes,
    ok: bool
  )
    requires Core.TransformRelation(cmd, data, output, ok)
    ensures Spec.TransformRelation(cmd, data, output, ok)
  {
    reveal Core.TransformRelation();
    reveal Spec.TransformRelation();
    if cmd.decode {
      var kept: BW.Bytes, indices: seq<nat> :|
        Core.KeptInputRelation(
          data, cmd.ignoreGarbage, kept, indices
        ) &&
        Core.DecodeRelation(kept, output, ok);
      KeptInputRelationImpliesSpec(
        data, cmd.ignoreGarbage, kept, indices
      );
      DecodeRelationImpliesSpec(kept, output, ok);
    } else {
      var encoded: BW.Bytes :|
        Core.EncodeRelation(data, encoded) &&
        Core.WrappedRelation(
          encoded, cmd.wrapWidth, output
        ) &&
        ok;
      EncodeRelationImpliesSpec(data, encoded);
      WrappedRelationImpliesSpec(
        encoded, cmd.wrapWidth, output
      );
    }
  }

  twostate lemma InputTraceRelationImpliesSpec(
    cmd: Schema.Base64Cmd,
    io: BenchIO.IO,
    data: BW.Bytes,
    errorOutput: BW.Bytes,
    hadReadError: bool
  )
    requires Core.InputTraceRelation(
               cmd, io, data, errorOutput, hadReadError
             )
    ensures Spec.InputTraceRelation(
              cmd, io, data, errorOutput, hadReadError
            )
  {
    reveal Core.InputTraceRelation();
    reveal Spec.InputTraceRelation();
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.Base64CmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    CommandSatisfiesRelation(raw);
    reveal Core.CoreSummary();
    reveal Spec.Spec();
    var cmd := Core.Command(raw);
    if cmd.mode == Schema.ModeRun {
      var data: BW.Bytes,
          errorOutput: BW.Bytes,
          hadReadError: bool,
          output: BW.Bytes,
          ok: bool :|
        Core.InputTraceRelation(
          cmd, io, data, errorOutput, hadReadError
        ) &&
        Core.TransformRelation(cmd, data, output, ok) &&
        io.stdin() ==
        (if cmd.inputs[0].Stdin?
         then []
         else old(io.stdin())) &&
        io.stdout() == old(io.stdout()) + output &&
        io.stderr() ==
        old(io.stderr()) + errorOutput +
        (if ok then [] else Spec.InvalidInputMessage()) &&
        exit ==
        (if hadReadError || !ok then 1 else 0);
      InputTraceRelationImpliesSpec(
        cmd, io, data, errorOutput, hadReadError
      );
      TransformRelationImpliesSpec(
        cmd, data, output, ok
      );
    }
  }
}
