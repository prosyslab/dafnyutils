include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/CliTypes.dfy"
include "Base64Schema.dfy"
include "Base64Spec.dfy"

module Base64Core {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import CliTypes
  import Schema = Base64Schema
  import Spec = Base64Spec

  datatype TransformResult = TransformResult(out: BenchWorld.Bytes, ok: bool)
  datatype NatParse = NatOk(value: nat) | NatErr
  datatype WrapParse = WrapParse(
    hasInvalid: bool,
    invalidText: string,
    invalidTokenIndex: int,
    width: nat
  )

  function IsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function DigitValue(ch: char): nat
    requires IsDigit(ch)
  {
    ((ch as int) - ('0' as int)) as nat
  }

  function ParseNatFrom(text: string, i: nat, acc: nat): NatParse
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      NatOk(acc)
    else if !IsDigit(text[i]) then
      NatErr
    else
      ParseNatFrom(text, i + 1, acc * 10 + DigitValue(text[i]))
  } by method {
    var j: nat := i;
    var value: nat := acc;
    while j < |text|
      invariant i <= j <= |text|
      invariant ParseNatFrom(text, j, value) ==
                ParseNatFrom(text, i, acc)
      decreases |text| - j
    {
      if !IsDigit(text[j]) {
        return NatErr;
      }
      value := value * 10 + DigitValue(text[j]);
      j := j + 1;
    }
    return NatOk(value);
  }

  function ParseNat(text: string): NatParse
  {
    if |text| == 0 then NatErr else ParseNatFrom(text, 0, 0)
  }

  function ParseWrapArgs(
    args: seq<Schema.WidthArg>,
    width: nat
  ): WrapParse
    decreases |args|
  {
    if |args| == 0 then
      WrapParse(false, "", -1, width)
    else
      match ParseNat(args[0].text)
      case NatErr =>
        WrapParse(true, args[0].text, args[0].tokenIndex, width)
      case NatOk(nextWidth) =>
        ParseWrapArgs(args[1..], nextWidth)
  } by method {
    var remaining: seq<Schema.WidthArg> := args;
    var currentWidth: nat := width;
    while |remaining| > 0
      invariant ParseWrapArgs(remaining, currentWidth) ==
                ParseWrapArgs(args, width)
      decreases |remaining|
    {
      match ParseNat(remaining[0].text) {
        case NatErr =>
          return WrapParse(
              true,
              remaining[0].text,
              remaining[0].tokenIndex,
              currentWidth
            );
        case NatOk(nextWidth) =>
          currentWidth := nextWidth;
          remaining := remaining[1..];
      }
    }
    return WrapParse(false, "", -1, currentWidth);
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<Schema.Base64CmdRaw>)
    decreases *
  {
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var wrapArgs: seq<Schema.WidthArg> := [];

    var i := 0;
    while i < |argv| && i < e.tokenIndex
      decreases |argv| - i
    {
      var token := argv[i];
      var consumedNext := false;
      if token == "--help" {
        seenHelp := true;
        if helpTokenIndex == -1 {
          helpTokenIndex := i;
        }
      } else if token == "--version" {
        seenVersion := true;
        if versionTokenIndex == -1 {
          versionTokenIndex := i;
        }
      } else if token == "-w" || token == "--wrap" {
        if i + 1 < |argv| && i + 1 < e.tokenIndex {
          wrapArgs :=
            wrapArgs + [Schema.WidthArg(argv[i + 1], i)];
          consumedNext := true;
        }
      } else if 7 <= |token| && token[..7] == "--wrap=" {
        wrapArgs := wrapArgs + [Schema.WidthArg(token[7..], i)];
      } else if |token| > 2 &&
                token[0] == '-' &&
                token[1] == 'w' {
        wrapArgs := wrapArgs + [Schema.WidthArg(token[2..], i)];
      }

      if consumedNext {
        i := i + 2;
      } else {
        i := i + 1;
      }
    }

    var raw := Schema.Base64CmdRaw(
      false,
      false,
      seenHelp,
      seenVersion,
      helpTokenIndex,
      versionTokenIndex,
      wrapArgs,
      []
    );
    var wrapPlan := ParseWrapArgs(wrapArgs, 76);
    if seenHelp &&
       (!seenVersion || helpTokenIndex <= versionTokenIndex) &&
       (!wrapPlan.hasInvalid ||
        helpTokenIndex <= wrapPlan.invalidTokenIndex) {
      plan := CliTypes.CliRun(raw);
      return;
    }
    if seenVersion &&
       (!wrapPlan.hasInvalid ||
        versionTokenIndex <= wrapPlan.invalidTokenIndex) {
      plan := CliTypes.CliRun(raw);
      return;
    }
    if wrapPlan.hasInvalid {
      plan := CliTypes.CliRun(raw);
      return;
    }

    var msg := Schema.Base64FormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }

  function Alphabet(index: nat): char
    requires index < 64
  {
    if index < 26 then
      (('A' as int) + index as int) as char
    else if index < 52 then
      (('a' as int) + (index - 26) as int) as char
    else if index < 62 then
      (('0' as int) + (index - 52) as int) as char
    else if index == 62 then
      '+'
    else
      '/'
  }

  function ByteValue(ch: char): nat
    ensures ByteValue(ch) < 256
  {
    ((ch as int) as nat) % 256
  }

  function ByteChar(value: nat): char
  {
    (value % 256) as char
  }

  function DecodeValue(ch: char): int
  {
    if 'A' <= ch <= 'Z' then
      (ch as int) - ('A' as int)
    else if 'a' <= ch <= 'z' then
      26 + (ch as int) - ('a' as int)
    else if '0' <= ch <= '9' then
      52 + (ch as int) - ('0' as int)
    else if ch == '+' then
      62
    else if ch == '/' then
      63
    else
      -1
  }

  function Valid64(ch: char): bool
  {
    DecodeValue(ch) >= 0
  }

  ghost predicate StrictlyIncreasing(indices: seq<nat>)
  {
    forall i, j ::
      0 <= i < j < |indices| ==> indices[i] < indices[j]
  }

  ghost predicate KeptInputRelation(
    data: BenchWorld.Bytes,
    ignoreGarbage: bool,
    kept: BenchWorld.Bytes,
    indices: seq<nat>
  )
  {
    |indices| == |kept| &&
    StrictlyIncreasing(indices) &&
    (forall k :: 0 <= k < |indices| ==>
                   indices[k] < |data| && kept[k] == data[indices[k]]) &&
    (forall i :: 0 <= i < |data| ==>
                   ((i in indices) ==
                    (if ignoreGarbage
                     then Valid64(data[i]) || data[i] == '='
                     else data[i] != '\n')))
  }

  ghost predicate EncodeBlockRelation(
    data: BenchWorld.Bytes,
    encoded: BenchWorld.Bytes,
    block: nat
  )
    requires block < (|data| + 2) / 3
    requires |encoded| == 4 * ((|data| + 2) / 3)
  {
    var input := 3 * block;
    var output := 4 * block;
    var b0 := ByteValue(data[input]);
    encoded[output] == Alphabet(b0 / 4) &&
    encoded[output + 1] ==
    Alphabet(
      (b0 % 4) * 16 +
      (if input + 1 < |data|
       then ByteValue(data[input + 1]) / 16
       else 0)
    ) &&
    encoded[output + 2] ==
    (if input + 1 < |data|
     then Alphabet(
               (ByteValue(data[input + 1]) % 16) * 4 +
               (if input + 2 < |data|
                then ByteValue(data[input + 2]) / 64
                else 0)
             )
     else '=') &&
    encoded[output + 3] ==
    (if input + 2 < |data|
     then Alphabet(ByteValue(data[input + 2]) % 64)
     else '=')
  }

  ghost predicate EncodeRelation(
    data: BenchWorld.Bytes,
    encoded: BenchWorld.Bytes
  )
  {
    |encoded| == 4 * ((|data| + 2) / 3) &&
    forall block :: 0 <= block < (|data| + 2) / 3 ==>
                      EncodeBlockRelation(data, encoded, block)
  }

  ghost predicate WrappedWitnessRelation(
    encoded: BenchWorld.Bytes,
    width: nat,
    output: BenchWorld.Bytes,
    chunks: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
    requires width > 0
  {
    ((|encoded| == 0) == (|chunks| == 0)) &&
    (forall line {:trigger chunks[line]} ::
       0 <= line < |chunks| ==>
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
            (line + 1) * width >= |encoded|)) &&
    FragmentsConcatenate(chunks, output, cuts)
  }

  ghost predicate WrappedRelation(
    encoded: BenchWorld.Bytes,
    width: nat,
    output: BenchWorld.Bytes
  )
  {
    if width == 0 then
      output == encoded
    else
      exists chunks: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
        WrappedWitnessRelation(
          encoded, width, output, chunks, cuts
        )
  }

  ghost predicate DecodeFullBlockRelation(
    data: BenchWorld.Bytes,
    start: nat,
    output: BenchWorld.Bytes
  )
    requires start + 4 <= |data|
  {
    var c0 := data[start];
    var c1 := data[start + 1];
    var c2 := data[start + 2];
    var c3 := data[start + 3];
    Valid64(c0) && Valid64(c1) &&
    ((Valid64(c2) && Valid64(c3) &&
      output == [
        ByteChar(
          (DecodeValue(c0) * 4 + DecodeValue(c1) / 16) as nat
        ),
        ByteChar(
          (((DecodeValue(c1) % 16) * 16 +
            DecodeValue(c2) / 4) as nat)
        ),
        ByteChar(
          ((((DecodeValue(c2) % 4) * 64) +
            DecodeValue(c3)) as nat)
        )
      ]) ||
     (c2 == '=' && c3 == '=' &&
      DecodeValue(c1) % 16 == 0 &&
      output == [
        ByteChar(
          (DecodeValue(c0) * 4 + DecodeValue(c1) / 16) as nat
        )
      ]) ||
     (Valid64(c2) && c3 == '=' &&
      DecodeValue(c2) % 4 == 0 &&
      output == [
        ByteChar(
          (DecodeValue(c0) * 4 + DecodeValue(c1) / 16) as nat
        ),
        ByteChar(
          (((DecodeValue(c1) % 16) * 16 +
            DecodeValue(c2) / 4) as nat)
        )
      ]))
  }

  ghost predicate DecodeTerminalRelation(
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    ok: bool
  )
  {
    var remaining := |data|;
    (remaining >= 4 ==>
       !(exists fullOutput: BenchWorld.Bytes ::
           DecodeFullBlockRelation(data, 0, fullOutput))) &&
    if remaining == 0 then
      output == [] && ok
    else if remaining == 1 then
      output == [] && !ok
    else
      var c0 := data[0];
      var c1 := data[1];
      if !Valid64(c0) || !Valid64(c1) then
        output == [] && !ok
      else if remaining == 2 then
        output == [
          ByteChar(
            (DecodeValue(c0) * 4 + DecodeValue(c1) / 16) as nat
          )
        ] &&
        (ok == (DecodeValue(c1) % 16 == 0))
      else
        var c2 := data[2];
        if c2 == '=' then
          output == [
            ByteChar(
              (DecodeValue(c0) * 4 +
               DecodeValue(c1) / 16) as nat
            )
          ] &&
          !ok
        else if !Valid64(c2) then
          output == [] && !ok
        else if remaining == 3 then
          output == [
            ByteChar(
              (DecodeValue(c0) * 4 +
               DecodeValue(c1) / 16) as nat
            ),
            ByteChar(
              (((DecodeValue(c1) % 16) * 16 +
                DecodeValue(c2) / 4) as nat)
            )
          ] &&
          (ok == (DecodeValue(c2) % 4 == 0))
        else
          var c3 := data[3];
          if c3 == '=' then
            output == [
              ByteChar(
                (DecodeValue(c0) * 4 +
                 DecodeValue(c1) / 16) as nat
              ),
              ByteChar(
                (((DecodeValue(c1) % 16) * 16 +
                  DecodeValue(c2) / 4) as nat)
              )
            ] &&
            !ok
          else
            output == [] && !ok
  }

  ghost predicate FragmentsConcatenate(
    fragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |combined| &&
    forall i {:trigger cuts[i]} ::
      0 <= i < |fragments| ==>
        cuts[i] <= cuts[i + 1] &&
        cuts[i + 1] <= |combined| &&
        cuts[i + 1] == cuts[i] + |fragments[i]| &&
        combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate DecodeWitnessRelation(
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    ok: bool,
    blocks: nat,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    4 * blocks <= |data| &&
    |fragments| == blocks + 1 &&
    (forall block :: 0 <= block < blocks ==>
                       DecodeFullBlockRelation(
                         data, 4 * block, fragments[block]
                       )) &&
    DecodeTerminalRelation(
      data[4 * blocks..], fragments[blocks], ok
    ) &&
    FragmentsConcatenate(fragments, output, cuts)
  }

  ghost predicate DecodeRelation(
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    ok: bool
  )
  {
    exists blocks: nat,
      fragments: seq<BenchWorld.Bytes>,
      cuts: seq<nat> ::
      DecodeWitnessRelation(
        data, output, ok, blocks, fragments, cuts
      )
  }

  ghost predicate TransformRelation(
    cmd: Schema.Base64Cmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    ok: bool
  )
  {
    if cmd.decode then
      exists kept: BenchWorld.Bytes, indices: seq<nat> ::
        KeptInputRelation(
          data, cmd.ignoreGarbage, kept, indices
        ) &&
        DecodeRelation(kept, output, ok)
    else
      exists encoded: BenchWorld.Bytes ::
        EncodeRelation(data, encoded) &&
        WrappedRelation(encoded, cmd.wrapWidth, output) &&
        ok
  }

  ghost function ShiftIndices(indices: seq<nat>): seq<nat>
    decreases |indices|
  {
    if |indices| == 0 then
      []
    else
      [indices[0] + 1] + ShiftIndices(indices[1..])
  }

  lemma ShiftIndicesFacts(indices: seq<nat>)
    requires StrictlyIncreasing(indices)
    ensures |ShiftIndices(indices)| == |indices|
    ensures StrictlyIncreasing(ShiftIndices(indices))
    ensures forall k :: 0 <= k < |indices| ==>
                          ShiftIndices(indices)[k] == indices[k] + 1
  {
    reveal StrictlyIncreasing();
    if |indices| > 0 {
      ShiftIndicesFacts(indices[1..]);
    }
  }

  lemma ShiftIndicesMembership(indices: seq<nat>, value: nat)
    ensures (value in ShiftIndices(indices)) ==
            (0 < value && value - 1 in indices)
    decreases |indices|
  {
    if |indices| > 0 {
      ShiftIndicesMembership(indices[1..], value);
    }
  }

  method FilterInputMethod(
    data: BenchWorld.Bytes,
    ignoreGarbage: bool
  ) returns (
      kept: BenchWorld.Bytes,
      ghost indices: seq<nat>
    )
    ensures KeptInputRelation(
              data, ignoreGarbage, kept, indices
            )
    decreases |data|
  {
    if |data| == 0 {
      kept := [];
      indices := [];
      reveal KeptInputRelation();
      reveal StrictlyIncreasing();
    } else {
      var tailKept, tailIndices :=
        FilterInputMethod(data[1..], ignoreGarbage);
      ShiftIndicesFacts(tailIndices);
      var keep :=
        if ignoreGarbage
        then Valid64(data[0]) || data[0] == '='
        else data[0] != '\n';
      kept := (if keep then [data[0]] else []) + tailKept;
      indices :=
        (if keep then [0] else []) + ShiftIndices(tailIndices);
      reveal KeptInputRelation();
      if keep {
        assert StrictlyIncreasing([0] + ShiftIndices(tailIndices));
      }
      assert forall k :: 0 <= k < |indices| ==>
                           indices[k] < |data| && kept[k] == data[indices[k]] by {
        forall k | 0 <= k < |indices|
          ensures indices[k] < |data| &&
                  kept[k] == data[indices[k]]
        {
          if keep && k > 0 {
            assert indices[k] == tailIndices[k - 1] + 1;
            assert kept[k] == tailKept[k - 1];
            assert data[tailIndices[k - 1] + 1] ==
                   data[1..][tailIndices[k - 1]];
          } else if !keep {
            assert indices[k] == tailIndices[k] + 1;
            assert kept[k] == tailKept[k];
            assert data[tailIndices[k] + 1] ==
                   data[1..][tailIndices[k]];
          }
        }
      }
      assert forall i :: 0 <= i < |data| ==>
                           ((i in indices) ==
                            (if ignoreGarbage
                             then Valid64(data[i]) || data[i] == '='
                             else data[i] != '\n')) by {
        forall i | 0 <= i < |data|
          ensures
            ((i in indices) ==
             (if ignoreGarbage
              then Valid64(data[i]) || data[i] == '='
              else data[i] != '\n'))
        {
          ShiftIndicesMembership(tailIndices, i);
          if i > 0 {
            assert data[i] == data[1..][i - 1];
          }
        }
      }
    }
  }

  method EncodeDataMethod(
    data: BenchWorld.Bytes
  ) returns (encoded: BenchWorld.Bytes)
    ensures EncodeRelation(data, encoded)
    decreases |data|
  {
    var headEncoded: BenchWorld.Bytes := [];
    var tailEncoded: BenchWorld.Bytes := [];
    if |data| == 0 {
      encoded := [];
    } else if |data| == 1 {
      var b0 := ByteValue(data[0]);
      encoded := [
        Alphabet(b0 / 4),
        Alphabet((b0 % 4) * 16),
        '=',
        '='
      ];
    } else if |data| == 2 {
      var b0 := ByteValue(data[0]);
      var b1 := ByteValue(data[1]);
      encoded := [
        Alphabet(b0 / 4),
        Alphabet((b0 % 4) * 16 + b1 / 16),
        Alphabet((b1 % 16) * 4),
        '='
      ];
    } else if |data| == 3 {
      var b0 := ByteValue(data[0]);
      var b1 := ByteValue(data[1]);
      var b2 := ByteValue(data[2]);
      encoded := [
        Alphabet(b0 / 4),
        Alphabet((b0 % 4) * 16 + b1 / 16),
        Alphabet((b1 % 16) * 4 + b2 / 64),
        Alphabet(b2 % 64)
      ];
    } else {
      headEncoded := EncodeDataMethod(data[..3]);
      tailEncoded := EncodeDataMethod(data[3..]);
      encoded := headEncoded + tailEncoded;
      assert |headEncoded| == 4;
    }
    reveal EncodeRelation();
    if |data| <= 3 {
      forall block | 0 <= block < (|data| + 2) / 3
        ensures EncodeBlockRelation(data, encoded, block)
      {
        assert block == 0;
        reveal EncodeBlockRelation();
      }
    } else {
      forall block | 0 <= block < (|data| + 2) / 3
        ensures EncodeBlockRelation(data, encoded, block)
      {
        reveal EncodeBlockRelation();
        if block == 0 {
          assert EncodeBlockRelation(
              data[..3], headEncoded, 0
            );
          reveal EncodeBlockRelation();
          assert data[..3][0] == data[0];
          assert data[..3][1] == data[1];
          assert data[..3][2] == data[2];
          assert encoded[0] == headEncoded[0];
          assert encoded[1] == headEncoded[1];
          assert encoded[2] == headEncoded[2];
          assert encoded[3] == headEncoded[3];
        } else {
          var tailBlock := block - 1;
          assert tailBlock < (|data[3..]| + 2) / 3;
          assert EncodeBlockRelation(
              data[3..], tailEncoded, tailBlock
            );
          reveal EncodeBlockRelation();
          assert 3 * block == 3 + 3 * tailBlock;
          assert 4 * block == 4 + 4 * tailBlock;
          assert data[3 * block] == data[3..][3 * tailBlock];
          assert encoded[4 * block] ==
                 tailEncoded[4 * tailBlock];
        }
      }
    }
  }

  ghost function ShiftCuts(
    cuts: seq<nat>,
    amount: nat
  ): seq<nat>
  {
    seq(|cuts|, i requires 0 <= i < |cuts| => cuts[i] + amount)
  }

  lemma ShiftCutsIndex(
    cuts: seq<nat>,
    amount: nat,
    index: nat
  )
    requires index < |cuts|
    ensures ShiftCuts(cuts, amount)[index] == cuts[index] + amount
  {
  }

  lemma PrependSlice<T>(
    head: seq<T>,
    tail: seq<T>,
    start: nat,
    end: nat
  )
    requires start <= end <= |tail|
    ensures (head + tail)[
            |head| + start..|head| + end
            ] == tail[start..end]
  {
  }

  lemma {:isolate_assertions} PrependFragment(
    head: BenchWorld.Bytes,
    tailFragments: seq<BenchWorld.Bytes>,
    tail: BenchWorld.Bytes,
    tailCuts: seq<nat>
  )
    requires FragmentsConcatenate(
               tailFragments, tail, tailCuts
             )
    ensures FragmentsConcatenate(
              [head] + tailFragments,
              head + tail,
              [0] + ShiftCuts(tailCuts, |head|)
            )
  {
    reveal FragmentsConcatenate();
    forall i: nat {:trigger ([0] + ShiftCuts(
      tailCuts, |head|
      ))[i]} | i < |[head] + tailFragments|
      ensures ([0] + ShiftCuts(tailCuts, |head|))[i] <=
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] &&
              ([0] + ShiftCuts(tailCuts, |head|))[i + 1] <=
              |head + tail| &&
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
        PrependSlice(
          head, tail, tailCuts[k], tailCuts[k + 1]
        );
      }
    }
  }

  lemma ShiftWrappedLine(
    text: BenchWorld.Bytes,
    width: nat,
    tailOutput: BenchWorld.Bytes,
    tailChunks: seq<BenchWorld.Bytes>,
    tailCuts: seq<nat>,
    tailLine: nat
  )
    requires width > 0
    requires width < |text|
    requires WrappedWitnessRelation(
               text[width..], width, tailOutput, tailChunks, tailCuts
             )
    requires tailLine < |tailChunks|
    ensures
      var line := tailLine + 1;
      var chunks := [text[..width] + ['\n']] + tailChunks;
      var start := line * width;
      var end :=
        if (line + 1) * width < |text|
        then (line + 1) * width
        else |text|;
      start < |text| &&
      start < end <= |text| &&
      chunks[line] == text[start..end] + ['\n'] &&
      (line + 1 < |chunks| ==>
         (line + 1) * width < |text|) &&
      (line + 1 == |chunks| ==>
         (line + 1) * width >= |text|)
  {
    var tail := text[width..];
    reveal WrappedWitnessRelation();
    var tailStart := tailLine * width;
    var tailEnd :=
      if (tailLine + 1) * width < |tail|
      then (tailLine + 1) * width
      else |tail|;
    assert tailChunks[tailLine] == tailChunks[tailLine];
    assert tailStart < |tail|;
    assert tailStart < tailEnd <= |tail|;
    assert tailChunks[tailLine] ==
           tail[tailStart..tailEnd] + ['\n'];
    assert (tailLine + 1 < |tailChunks| ==>
              (tailLine + 1) * width < |tail|);
    assert (tailLine + 1 == |tailChunks| ==>
              (tailLine + 1) * width >= |tail|);
    var line := tailLine + 1;
    assert line * width == width + tailLine * width;
    var end :=
      if (line + 1) * width < |text|
      then (line + 1) * width
      else |text|;
    assert |text| == width + |tail|;
    if (tailLine + 1) * width < |tail| {
      assert (line + 1) * width < |text|;
      assert tailEnd == (tailLine + 1) * width;
      assert end == (line + 1) * width;
      assert end == width + tailEnd;
    } else {
      assert (line + 1) * width >= |text|;
      assert tailEnd == |tail|;
      assert end == |text|;
      assert end == width + tailEnd;
    }
    assert line * width < |text|;
    assert line * width < end <= |text|;
    assert text == text[..width] + tail;
    PrependSlice(
      text[..width], tail, tailStart, tailEnd
    );
    assert text[line * width..end] ==
           tail[tailStart..tailEnd];
  }

  lemma PrependWrappedWitness(
    text: BenchWorld.Bytes,
    width: nat,
    tailOutput: BenchWorld.Bytes,
    tailChunks: seq<BenchWorld.Bytes>,
    tailCuts: seq<nat>
  )
    requires width > 0
    requires width < |text|
    requires WrappedWitnessRelation(
               text[width..], width, tailOutput, tailChunks, tailCuts
             )
    ensures WrappedWitnessRelation(
              text,
              width,
              text[..width] + ['\n'] + tailOutput,
              [text[..width] + ['\n']] + tailChunks,
              [0] + ShiftCuts(tailCuts, width + 1)
            )
  {
    var tail := text[width..];
    var head := text[..width] + ['\n'];
    var chunks := [head] + tailChunks;
    forall line | 0 <= line < |chunks|
      ensures
        var start := line * width;
        var end :=
          if (line + 1) * width < |text|
          then (line + 1) * width
          else |text|;
        start < |text| &&
        start < end <= |text| &&
        chunks[line] == text[start..end] + ['\n'] &&
        (line + 1 < |chunks| ==>
           (line + 1) * width < |text|) &&
        (line + 1 == |chunks| ==>
           (line + 1) * width >= |text|)
    {
      if line > 0 {
        var tailLine := line - 1;
        assert tailLine < |tailChunks|;
        ShiftWrappedLine(
          text, width, tailOutput, tailChunks, tailCuts,
          tailLine
        );
        assert line == tailLine + 1;
      }
    }
    assert FragmentsConcatenate(
      chunks, head + tailOutput,
      [0] + ShiftCuts(tailCuts, width + 1)
    ) by {
      PrependFragment(head, tailChunks, tailOutput, tailCuts);
    }
  }

  method WrapEncodedMethod(
    text: BenchWorld.Bytes,
    width: nat
  ) returns (
      output: BenchWorld.Bytes,
      ghost chunks: seq<BenchWorld.Bytes>,
      ghost cuts: seq<nat>
    )
    ensures width > 0 ==> WrappedWitnessRelation(
                text, width, output, chunks, cuts
              )
    ensures WrappedRelation(text, width, output)
    decreases |text|
  {
    if width == 0 {
      output := text;
      chunks := [];
      cuts := [0];
      reveal WrappedRelation();
    } else if |text| == 0 {
      output := [];
      chunks := [];
      cuts := [0];
      reveal WrappedWitnessRelation();
      reveal FragmentsConcatenate();
    } else if |text| <= width {
      output := text + ['\n'];
      chunks := [output];
      cuts := [0, |output|];
      reveal WrappedWitnessRelation();
      reveal FragmentsConcatenate();
    } else {
      var tail := text[width..];
      var head := text[..width] + ['\n'];
      var tailOutput, tailChunks, tailCuts :=
        WrapEncodedMethod(tail, width);
      output := head + tailOutput;
      chunks := [head] + tailChunks;
      cuts := [0] + ShiftCuts(tailCuts, |head|);
      assert |head| == width + 1;
      PrependWrappedWitness(
        text, width, tailOutput, tailChunks, tailCuts
      );
    }
    reveal WrappedRelation();
  }

  method DecodeTerminalMethod(
    data: BenchWorld.Bytes
  ) returns (result: TransformResult)
    requires !(|data| >= 4 &&
               exists blockOutput: BenchWorld.Bytes ::
                 DecodeFullBlockRelation(data, 0, blockOutput))
    ensures DecodeTerminalRelation(
              data, result.out, result.ok
            )
  {
    if |data| == 0 {
      result := TransformResult([], true);
    } else if |data| == 1 {
      result := TransformResult([], false);
    } else if !Valid64(data[0]) || !Valid64(data[1]) {
      result := TransformResult([], false);
    } else {
      var v0 := DecodeValue(data[0]);
      var v1 := DecodeValue(data[1]);
      if |data| == 2 {
        result := TransformResult(
          [ByteChar((v0 * 4 + v1 / 16) as nat)],
          v1 % 16 == 0
        );
      } else if data[2] == '=' {
        result := TransformResult(
          [ByteChar((v0 * 4 + v1 / 16) as nat)],
          false
        );
      } else if !Valid64(data[2]) {
        result := TransformResult([], false);
      } else {
        var v2 := DecodeValue(data[2]);
        var out := [
          ByteChar((v0 * 4 + v1 / 16) as nat),
          ByteChar((((v1 % 16) * 16 + v2 / 4) as nat))
        ];
        if |data| == 3 {
          result := TransformResult(out, v2 % 4 == 0);
        } else if data[3] == '=' {
          result := TransformResult(out, false);
        } else {
          result := TransformResult([], false);
        }
      }
    }
    reveal DecodeTerminalRelation();
  }

  lemma ShiftDecodeFullBlock(
    data: BenchWorld.Bytes,
    start: nat,
    output: BenchWorld.Bytes
  )
    requires |data| >= 4
    requires start + 4 <= |data[4..]|
    requires DecodeFullBlockRelation(
               data[4..], start, output
             )
    ensures DecodeFullBlockRelation(
              data, start + 4, output
            )
  {
    reveal DecodeFullBlockRelation();
  }

  method DecodeRestMethod(
    data: BenchWorld.Bytes
  ) returns (
      result: TransformResult,
      ghost blocks: nat,
      ghost fragments: seq<BenchWorld.Bytes>,
      ghost cuts: seq<nat>
    )
    ensures DecodeWitnessRelation(
              data,
              result.out,
              result.ok,
              blocks,
              fragments,
              cuts
            )
    decreases |data|
  {
    var full := false;
    var blockOutput: BenchWorld.Bytes := [];
    if |data| >= 4 &&
       Valid64(data[0]) && Valid64(data[1]) {
      var v0 := DecodeValue(data[0]);
      var v1 := DecodeValue(data[1]);
      if data[2] == '=' {
        if data[3] == '=' && v1 % 16 == 0 {
          blockOutput := [
            ByteChar((v0 * 4 + v1 / 16) as nat)
          ];
          full := true;
        }
      } else if Valid64(data[2]) {
        var v2 := DecodeValue(data[2]);
        if data[3] == '=' {
          if v2 % 4 == 0 {
            blockOutput := [
              ByteChar((v0 * 4 + v1 / 16) as nat),
              ByteChar((((v1 % 16) * 16 + v2 / 4) as nat))
            ];
            full := true;
          }
        } else if Valid64(data[3]) {
          var v3 := DecodeValue(data[3]);
          blockOutput := [
            ByteChar((v0 * 4 + v1 / 16) as nat),
            ByteChar((((v1 % 16) * 16 + v2 / 4) as nat)),
            ByteChar(((((v2 % 4) * 64) + v3) as nat))
          ];
          full := true;
        }
      }
    }
    if full {
      assert DecodeFullBlockRelation(
          data, 0, blockOutput
        ) by {
        reveal DecodeFullBlockRelation();
      }
      var tailResult, tailBlocks, tailFragments, tailCuts :=
        DecodeRestMethod(data[4..]);
      result := TransformResult(
        blockOutput + tailResult.out, tailResult.ok
      );
      blocks := tailBlocks + 1;
      fragments := [blockOutput] + tailFragments;
      cuts := [0] + ShiftCuts(tailCuts, |blockOutput|);
      reveal DecodeWitnessRelation();
      PrependFragment(
        blockOutput,
        tailFragments,
        tailResult.out,
        tailCuts
      );
      forall block | 0 <= block < blocks
        ensures DecodeFullBlockRelation(
                  data, 4 * block, fragments[block]
                )
      {
        if block > 0 {
          var tailBlock := block - 1;
          assert DecodeFullBlockRelation(
              data[4..],
              4 * tailBlock,
              tailFragments[tailBlock]
            );
          ShiftDecodeFullBlock(
            data, 4 * tailBlock, tailFragments[tailBlock]
          );
          assert 4 * block == 4 * tailBlock + 4;
        }
      }
      assert data[4 * blocks..] ==
             data[4..][4 * tailBlocks..];
    } else {
      assert !(|data| >= 4 &&
               exists fullOutput: BenchWorld.Bytes ::
                 DecodeFullBlockRelation(
                   data, 0, fullOutput
                 )) by {
        reveal DecodeFullBlockRelation();
      }
      result := DecodeTerminalMethod(data);
      blocks := 0;
      fragments := [result.out];
      cuts := [0, |result.out|];
      reveal DecodeWitnessRelation();
      reveal FragmentsConcatenate();
    }
  }

  function InputsFromOperands(operands: seq<string>): seq<Schema.Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then Schema.Stdin else Schema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  } by method {
    var inputs: seq<Schema.Input> := [];
    var i := |operands|;
    while 0 < i
      invariant 0 <= i <= |operands|
      invariant inputs == InputsFromOperands(operands[i..])
      decreases i
    {
      i := i - 1;
      var head :=
        if operands[i] == "-"
        then Schema.Stdin
        else Schema.File(operands[i]);
      assert operands[i..] == [operands[i]] + operands[i + 1..];
      inputs := [head] + inputs;
    }
    return inputs;
  }

  function HelpBeforeInvalid(raw: Schema.Base64CmdRaw): bool
  {
    var wrapPlan := ParseWrapArgs(raw.wrapArgs, 76);
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) &&
    (!wrapPlan.hasInvalid || raw.helpTokenIndex <= wrapPlan.invalidTokenIndex)
  }

  function VersionBeforeInvalid(raw: Schema.Base64CmdRaw): bool
  {
    var wrapPlan := ParseWrapArgs(raw.wrapArgs, 76);
    raw.seenVersion &&
    (!wrapPlan.hasInvalid || raw.versionTokenIndex <= wrapPlan.invalidTokenIndex)
  }

  function Command(raw: Schema.Base64CmdRaw): Schema.Base64Cmd
  {
    var wrapPlan := ParseWrapArgs(raw.wrapArgs, 76);
    var mode :=
      if HelpBeforeInvalid(raw) then
        Schema.ModeHelp
      else if VersionBeforeInvalid(raw) then
        Schema.ModeVersion
      else
        Schema.ModeRun;
    if mode != Schema.ModeRun then
      Schema.Base64Cmd(mode, raw.seenDecode, false, 76, "", [])
    else if |raw.wrapArgs| == 0 then
      if |raw.operands| > 1 then
        Schema.Base64Cmd(
          Schema.ModeExtraOperand(raw.operands[1]),
          raw.seenDecode,
          false,
          76,
          "",
          []
        )
      else
        Schema.Base64Cmd(
          Schema.ModeRun,
          raw.seenDecode,
          raw.seenIgnoreGarbage,
          76,
          "",
          if |raw.operands| == 0
          then [Schema.Stdin]
          else InputsFromOperands(raw.operands)
        )
    else if wrapPlan.hasInvalid then
      Schema.Base64Cmd(
        Schema.ModeInvalidWrap,
        raw.seenDecode,
        false,
        76,
        wrapPlan.invalidText,
        []
      )
    else if |raw.operands| > 1 then
      Schema.Base64Cmd(
        Schema.ModeExtraOperand(raw.operands[1]),
        raw.seenDecode,
        false,
        wrapPlan.width,
        "",
        []
      )
    else
      Schema.Base64Cmd(
        Schema.ModeRun,
        raw.seenDecode,
        raw.seenIgnoreGarbage,
        wrapPlan.width,
        "",
        if |raw.operands| == 0
        then [Schema.Stdin]
        else InputsFromOperands(raw.operands)
      )
  }

  lemma CommandRunHasOneInput(raw: Schema.Base64CmdRaw)
    ensures Command(raw).mode == Schema.ModeRun ==>
              |Command(raw).inputs| == 1
  {
    if |raw.operands| == 1 {
      assert |InputsFromOperands(raw.operands)| == 1;
    }
  }

  twostate predicate InputTraceRelation(
    cmd: Schema.Base64Cmd,
    io: BenchIO.IO,
    data: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadReadError: bool
  )
    reads io.Footprint()
  {
    |cmd.inputs| == 1 &&
    match cmd.inputs[0]
    case Stdin =>
      data == old(io.stdin()) &&
      errorOutput == [] &&
      !hadReadError
    case File(path) =>
      match IOContract.ReadFileResultFields(old(io.fs()), path)
      case Ok(fileData) =>
        data == fileData &&
        errorOutput == [] &&
        !hadReadError
      case Err(err) =>
        data == [] &&
        errorOutput == Spec.ErrorMessage(path, err) &&
        hadReadError
  }

  twostate predicate CoreSummary(raw: Schema.Base64CmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeInvalidWrap then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() ==
      old(io.stderr()) +
      Spec.InvalidWrapMessage(cmd.invalidWrapValue) &&
      exit == 1
    else if cmd.mode != Schema.ModeRun then
      match cmd.mode
      case ModeExtraOperand(operand) =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() ==
        old(io.stderr()) + Spec.ExtraOperandMessage(operand) &&
        exit == 1
      case _ => false
    else
      exists data: BenchWorld.Bytes,
        errorOutput: BenchWorld.Bytes,
        hadReadError: bool,
        output: BenchWorld.Bytes,
        ok: bool ::
        InputTraceRelation(
          cmd, io, data, errorOutput, hadReadError
        ) &&
        TransformRelation(
          cmd, data, output, ok
        ) &&
        io.stdin() ==
        (if cmd.inputs[0].Stdin?
         then []
         else old(io.stdin())) &&
        io.stdout() ==
        old(io.stdout()) + output &&
        io.stderr() ==
        old(io.stderr()) + errorOutput +
        (if ok
         then []
         else Spec.InvalidInputMessage()) &&
        exit ==
        (if hadReadError || !ok
         then 1
         else 0)
  }

  method ProcessInput(
    cmd: Schema.Base64Cmd,
    io: BenchIO.IO
  ) returns (data: BenchWorld.Bytes, errOut: BenchWorld.Bytes, hadReadError: bool)
    modifies io.stdinRegion
    requires |cmd.inputs| == 1
    ensures io.stdin() ==
            (if cmd.inputs[0].Stdin? then [] else old(io.stdin()))
    ensures InputTraceRelation(
              cmd, io, data, errOut, hadReadError
            )
  {
    match cmd.inputs[0]
    case Stdin =>
      data := io.ReadStdinAll();
      errOut := [];
      hadReadError := false;
    case File(path) =>
      var res := io.ReadFile(path);
      match res
      case Ok(chunk) =>
        data := chunk;
        errOut := [];
        hadReadError := false;
      case Err(err) =>
        data := [];
        errOut := Spec.ErrorMessage(path, err);
        hadReadError := true;
  }

  method TransformMethod(
    cmd: Schema.Base64Cmd,
    data: BenchWorld.Bytes
  ) returns (result: TransformResult)
    ensures TransformRelation(
              cmd, data, result.out, result.ok
            )
  {
    reveal TransformRelation();
    if cmd.decode {
      var kept, indices :=
        FilterInputMethod(data, cmd.ignoreGarbage);
      var decoded, blocks, fragments, cuts :=
        DecodeRestMethod(kept);
      result := decoded;
      reveal DecodeRelation();
    } else {
      var encoded := EncodeDataMethod(data);
      var output, chunks, cuts :=
        WrapEncodedMethod(encoded, cmd.wrapWidth);
      result := TransformResult(output, true);
    }
  }

  method RunCore(raw: Schema.Base64CmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preStdin := io.stdin();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Command(raw);
    if cmd.mode == Schema.ModeHelp {
      io.AppendStdout(Spec.HelpText());
      exit := 0;
      assert io.stdin() == preStdin;
      assert io.stderr() == preStderr;
      assert CoreSummary(raw, io, exit);
      return;
    }
    if cmd.mode == Schema.ModeVersion {
      io.AppendStdout(Spec.VersionText());
      exit := 0;
      assert io.stdin() == preStdin;
      assert io.stderr() == preStderr;
      assert CoreSummary(raw, io, exit);
      return;
    }
    if cmd.mode == Schema.ModeInvalidWrap {
      io.AppendStderr(Spec.InvalidWrapMessage(cmd.invalidWrapValue));
      exit := 1;
      assert io.stdin() == preStdin;
      assert io.stdout() == preStdout;
      assert CoreSummary(raw, io, exit);
      return;
    }
    if cmd.mode.ModeExtraOperand? {
      io.AppendStderr(Spec.ExtraOperandMessage(cmd.mode.operand));
      exit := 1;
      assert io.stdin() == preStdin;
      assert io.stdout() == preStdout;
      assert CoreSummary(raw, io, exit);
      return;
    }

    CommandRunHasOneInput(raw);
    var data: BenchWorld.Bytes;
    var errOut: BenchWorld.Bytes;
    var hadReadError: bool;
    assert |cmd.inputs| == 1;
    data, errOut, hadReadError := ProcessInput(cmd, io);
    var transform := TransformMethod(cmd, data);
    io.AppendStdout(transform.out);
    assert io.stdout() == preStdout + transform.out;
    if |errOut| > 0 {
      io.AppendStderr(errOut);
    } else {
      assert io.stderr() == preStderr + errOut;
    }
    if !transform.ok {
      io.AppendStderr(Spec.InvalidInputMessage());
    }
    exit := if hadReadError || !transform.ok then 1 else 0;
    assert InputTraceRelation(
        cmd, io, data, errOut, hadReadError
      );
    assert io.stdin() ==
           (if cmd.inputs[0].Stdin? then [] else preStdin);
    assert io.stdout() == preStdout + transform.out;
    assert io.stderr() ==
           preStderr + errOut +
           (if transform.ok
            then []
            else Spec.InvalidInputMessage());
    assert CoreSummary(raw, io, exit) by {
      reveal CoreSummary();
      assert exists traceData: BenchWorld.Bytes,
          errorOutput: BenchWorld.Bytes,
          traceHadReadError: bool,
          output: BenchWorld.Bytes,
          ok: bool ::
          traceData == data &&
          errorOutput == errOut &&
          traceHadReadError == hadReadError &&
          output == transform.out &&
          ok == transform.ok &&
          InputTraceRelation(
            cmd, io, traceData, errorOutput, traceHadReadError
          ) &&
          TransformRelation(
            cmd, traceData, output, ok
          ) &&
          io.stdin() ==
          (if cmd.inputs[0].Stdin?
           then []
           else preStdin) &&
          io.stdout() ==
          preStdout + output &&
          io.stderr() ==
          preStderr + errorOutput +
          (if ok
           then []
           else Spec.InvalidInputMessage()) &&
          exit ==
          (if traceHadReadError ||
              !ok
           then 1
           else 0);
    }
  }
}
