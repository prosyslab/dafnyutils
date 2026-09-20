include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "TrSchema.dfy"
include "TrSpec.dfy"

module TrCore {
  import BenchIO
  import BenchWorld
  import IOContract
  import TrSchema
  import Spec = TrSpec

  datatype TrMode =
    | ModeRun
    | ModeHelp
    | ModeVersion
    | ModeMissingOperand(message: BenchWorld.Bytes)
    | ModeExtraOperand(operand: string)
    | ModeUnsupportedSet(operand: string)
    | ModeEmptySet2

  datatype TrCmd = TrCmd(
    mode: TrMode,
    deleteSet: bool,
    squeeze: bool,
    set1: BenchWorld.Bytes,
    set2: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes
  )

  datatype SetDecode = SetOk(bytes: BenchWorld.Bytes) | SetUnsupported(operand: string)

  function IsAscii(ch: char): bool
  {
    0 <= ch as int < 128
  }

  function IsSetSyntaxMarker(ch: char): bool
  {
    ch == '\\'
  }

  function ContainsPairFrom(text: string, i: nat, first: char, second: char): bool
    requires i <= |text|
    decreases |text| - i
  {
    (i + 1 < |text| && text[i] == first && text[i + 1] == second) ||
    (i < |text| && ContainsPairFrom(text, i + 1, first, second))
  }

  function ContainsCharFrom(text: string, i: nat, target: char): bool
    requires i <= |text|
    decreases |text| - i
  {
    i < |text| && (text[i] == target || ContainsCharFrom(text, i + 1, target))
  }

  function StartsUnsupportedConstruct(text: string, i: nat): bool
    requires i <= |text|
  {
    i < |text| && text[i] == '[' && (
      (i + 1 < |text| && text[i + 1] == ':' && ContainsPairFrom(text, i + 2, ':', ']')) ||
      (i + 1 < |text| && text[i + 1] == '=' && ContainsPairFrom(text, i + 2, '=', ']')) ||
      (i + 2 < |text| && text[i + 2] == '*' && ContainsCharFrom(text, i + 3, ']'))
    )
  }

  function RangeChars(lo: char, hi: char): BenchWorld.Bytes
    requires IsAscii(lo)
    requires IsAscii(hi)
    requires lo as int <= hi as int
    decreases (hi as int) - (lo as int)
  {
    if lo == hi then
      [lo]
    else
      [lo] + RangeChars(((lo as int) + 1) as char, hi)
  }

  function DecodeSetFrom(text: string, i: nat): SetDecode
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      SetOk([])
    else if StartsUnsupportedConstruct(text, i) then
      SetUnsupported(text)
    else if IsSetSyntaxMarker(text[i]) then
      SetUnsupported(text)
    else if i + 2 < |text| && text[i + 1] == '-' then
      if IsAscii(text[i]) && IsAscii(text[i + 2]) && text[i] as int <= text[i + 2] as int then
        match DecodeSetFrom(text, i + 3)
        case SetOk(rest) => SetOk(RangeChars(text[i], text[i + 2]) + rest)
        case SetUnsupported(_) => SetUnsupported(text)
      else
        SetUnsupported(text)
    else if !IsAscii(text[i]) then
      SetUnsupported(text)
    else
      match DecodeSetFrom(text, i + 1)
      case SetOk(rest) => SetOk([text[i]] + rest)
      case SetUnsupported(_) => SetUnsupported(text)
  } by method {
    if i == |text| {
      return SetOk([]);
    } else if StartsUnsupportedConstruct(text, i) {
      return SetUnsupported(text);
    } else if IsSetSyntaxMarker(text[i]) {
      return SetUnsupported(text);
    } else if i + 2 < |text| && text[i + 1] == '-' {
      if IsAscii(text[i]) && IsAscii(text[i + 2]) && text[i] as int <= text[i + 2] as int {
        var tail := DecodeSetFrom(text, i + 3);
        match tail
        case SetOk(rest) =>
          return SetOk(RangeChars(text[i], text[i + 2]) + rest);
        case SetUnsupported(_) =>
          return SetUnsupported(text);
      } else {
        return SetUnsupported(text);
      }
    } else if !IsAscii(text[i]) {
      return SetUnsupported(text);
    } else {
      var tail := DecodeSetFrom(text, i + 1);
      match tail
      case SetOk(rest) =>
        return SetOk([text[i]] + rest);
      case SetUnsupported(_) =>
        return SetUnsupported(text);
    }
  }

  function DecodeSet(text: string): SetDecode
  {
    DecodeSetFrom(text, 0)
  } by method {
    return DecodeSetFrom(text, 0);
  }

  function HasUnsupportedOperand(operands: seq<string>): string
    decreases |operands|
  {
    if |operands| == 0 then
      ""
    else
      match DecodeSet(operands[0])
      case SetOk(_) => HasUnsupportedOperand(operands[1..])
      case SetUnsupported(_) => operands[0]
  } by method {
    if |operands| == 0 {
      return "";
    } else {
      var decoded := DecodeSet(operands[0]);
      match decoded
      case SetOk(_) =>
        return HasUnsupportedOperand(operands[1..]);
      case SetUnsupported(_) =>
        return operands[0];
    }
  }

  function SetBytes(text: string): BenchWorld.Bytes
  {
    match DecodeSet(text)
    case SetOk(bytes) => bytes
    case SetUnsupported(_) => []
  } by method {
    var decoded := DecodeSet(text);
    return
      match decoded
      case SetOk(bytes) => bytes
      case SetUnsupported(_) => [];
  }

  // Deferred GNU behavior: classes, equivalence classes, repeats, escapes,
  // complements, truncate mode, locale behavior, and multibyte characters are
  // intentionally outside this ASCII byte-set benchmark slice.
  function Command(raw: TrSchema.TrCmdRaw): TrCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else if |raw.operands| == 0 then
        ModeMissingOperand(Spec.MissingOperandMessageSpec())
      else if !raw.seenDelete && !raw.seenSqueeze && |raw.operands| == 1 then
        ModeMissingOperand(Spec.MissingSet2MessageSpec())
      else if raw.seenDelete && raw.seenSqueeze && |raw.operands| == 1 then
        ModeMissingOperand(Spec.MissingSet2MessageSpec())
      else if raw.seenDelete && !raw.seenSqueeze && |raw.operands| > 1 then
        ModeExtraOperand(raw.operands[1])
      else if |raw.operands| > 2 then
        ModeExtraOperand(raw.operands[2])
      else if HasUnsupportedOperand(raw.operands) != "" then
        ModeUnsupportedSet(HasUnsupportedOperand(raw.operands))
      else if !raw.seenDelete && |raw.operands| == 2 && |SetBytes(raw.operands[1])| == 0 then
        ModeEmptySet2
      else
        ModeRun;
    var set1 := if |raw.operands| > 0 then SetBytes(raw.operands[0]) else [];
    var set2 := if |raw.operands| > 1 then SetBytes(raw.operands[1]) else [];
    var squeezeSet :=
      if raw.seenSqueeze && |raw.operands| > 1 then set2 else set1;
    TrCmd(mode, raw.seenDelete, raw.seenSqueeze, set1, set2, squeezeSet)
  } by method {
    var unsupported := HasUnsupportedOperand(raw.operands);
    var set1: BenchWorld.Bytes := [];
    var set2: BenchWorld.Bytes := [];
    if |raw.operands| > 0 {
      set1 := SetBytes(raw.operands[0]);
    }
    if |raw.operands| > 1 {
      set2 := SetBytes(raw.operands[1]);
    }
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else if |raw.operands| == 0 then
        ModeMissingOperand(Spec.MissingOperandMessageSpec())
      else if !raw.seenDelete && !raw.seenSqueeze && |raw.operands| == 1 then
        ModeMissingOperand(Spec.MissingSet2MessageSpec())
      else if raw.seenDelete && raw.seenSqueeze && |raw.operands| == 1 then
        ModeMissingOperand(Spec.MissingSet2MessageSpec())
      else if raw.seenDelete && !raw.seenSqueeze && |raw.operands| > 1 then
        ModeExtraOperand(raw.operands[1])
      else if |raw.operands| > 2 then
        ModeExtraOperand(raw.operands[2])
      else if unsupported != "" then
        ModeUnsupportedSet(unsupported)
      else if !raw.seenDelete && |raw.operands| == 2 && |set2| == 0 then
        ModeEmptySet2
      else
        ModeRun;
    var squeezeSet := if raw.seenSqueeze && |raw.operands| > 1 then set2 else set1;
    return TrCmd(mode, raw.seenDelete, raw.seenSqueeze, set1, set2, squeezeSet);
  }

  function Contains(bytes: BenchWorld.Bytes, ch: char): bool
    decreases |bytes|
  {
    |bytes| > 0 && (bytes[0] == ch || Contains(bytes[1..], ch))
  } by method {
    if |bytes| == 0 {
      return false;
    } else {
      return bytes[0] == ch || Contains(bytes[1..], ch);
    }
  }

  function TranslateWithCandidate(
    set1: BenchWorld.Bytes,
    set2: BenchWorld.Bytes,
    ch: char,
    candidate: char
  ): char
    requires |set2| > 0
    ensures candidate is BenchWorld.RawByte ==>
              TranslateWithCandidate(set1, set2, ch, candidate) is BenchWorld.RawByte
    decreases |set1|
  {
    if |set1| == 0 then
      candidate
    else
      var nextCandidate := if set1[0] == ch then set2[0] else candidate;
      TranslateWithCandidate(set1[1..], if |set2| > 1 then set2[1..] else set2, ch, nextCandidate)
  } by method {
    if |set1| == 0 {
      return candidate;
    } else {
      var nextCandidate := if set1[0] == ch then set2[0] else candidate;
      return TranslateWithCandidate(
          set1[1..],
          if |set2| > 1 then set2[1..] else set2,
          ch,
          nextCandidate
        );
    }
  }

  function TranslateWith(set1: BenchWorld.Bytes, set2: BenchWorld.Bytes, ch: char): char
    requires |set2| > 0
    ensures ch is BenchWorld.RawByte ==> TranslateWith(set1, set2, ch) is BenchWorld.RawByte
  {
    TranslateWithCandidate(set1, set2, ch, ch)
  } by method {
    return TranslateWithCandidate(set1, set2, ch, ch);
  }

  function DeleteAndTranslate(cmd: TrCmd, data: BenchWorld.Bytes): BenchWorld.Bytes
    decreases |data|
  {
    if |data| == 0 then
      []
    else if cmd.deleteSet && Contains(cmd.set1, data[0]) then
      DeleteAndTranslate(cmd, data[1..])
    else
      var out := if !cmd.deleteSet && |cmd.set2| > 0 then
                   TranslateWith(cmd.set1, cmd.set2, data[0])
                 else
                   data[0];
      [out] + DeleteAndTranslate(cmd, data[1..])
  } by method {
    if |data| == 0 {
      return [];
    } else {
      var selected := Contains(cmd.set1, data[0]);
      if cmd.deleteSet && selected {
        return DeleteAndTranslate(cmd, data[1..]);
      } else {
        var ch := data[0];
        if !cmd.deleteSet && |cmd.set2| > 0 {
          ch := TranslateWith(cmd.set1, cmd.set2, data[0]);
        }
        return [ch] + DeleteAndTranslate(cmd, data[1..]);
      }
    }
  }

  function SqueezeFrom(
    data: BenchWorld.Bytes,
    squeezeBytes: BenchWorld.Bytes,
    hasPrevious: bool,
    previous: char
  ): BenchWorld.Bytes
    decreases |data|
  {
    if |data| == 0 then
      []
    else if hasPrevious && data[0] == previous && Contains(squeezeBytes, data[0]) then
      SqueezeFrom(data[1..], squeezeBytes, true, previous)
    else
      [data[0]] + SqueezeFrom(data[1..], squeezeBytes, true, data[0])
  } by method {
    if |data| == 0 {
      return [];
    } else {
      var selected := Contains(squeezeBytes, data[0]);
      if hasPrevious && data[0] == previous && selected {
        return SqueezeFrom(data[1..], squeezeBytes, true, previous);
      } else {
        return [data[0]] + SqueezeFrom(data[1..], squeezeBytes, true, data[0]);
      }
    }
  }

  function RenderData(cmd: TrCmd, data: BenchWorld.Bytes): BenchWorld.Bytes
  {
    var transformed := DeleteAndTranslate(cmd, data);
    if cmd.squeeze then SqueezeFrom(transformed, cmd.squeezeSet, false, '\0') else transformed
  } by method {
    var transformed := DeleteAndTranslate(cmd, data);
    if cmd.squeeze {
      return SqueezeFrom(transformed, cmd.squeezeSet, false, '\0');
    } else {
      return transformed;
    }
  }

  twostate predicate CoreSummary(raw: TrSchema.TrCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    match cmd.mode
    case ModeHelp =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    case ModeVersion =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    case ModeMissingOperand(message) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + message &&
      exit == 1
    case ModeExtraOperand(operand) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.ExtraOperandMessageSpec(operand) &&
      exit == 1
    case ModeUnsupportedSet(operand) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.UnsupportedSetMessageSpec(operand) &&
      exit == 1
    case ModeEmptySet2 =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.EmptySet2MessageSpec() &&
      exit == 1
    case ModeRun =>
      io.stdin() == IOContract.AfterReadStdinFields(old(io.stdin())) &&
      io.stdout() == old(io.stdout()) + RenderData(cmd, old(io.stdin())) &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
  }

  method RunCore(raw: TrSchema.TrCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preStdin := io.stdin();
    var cmd := Command(raw);

    match cmd.mode {
      case ModeHelp =>
        io.AppendStdout(Spec.HelpTextSpec());
        exit := 0;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeVersion =>
        io.AppendStdout(Spec.VersionTextSpec());
        exit := 0;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeMissingOperand(message) =>
        io.AppendStderr(message);
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeExtraOperand(operand) =>
        io.AppendStderr(Spec.ExtraOperandMessageSpec(operand));
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeUnsupportedSet(operand) =>
        io.AppendStderr(Spec.UnsupportedSetMessageSpec(operand));
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeEmptySet2 =>
        io.AppendStderr(Spec.EmptySet2MessageSpec());
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      case ModeRun =>
        var data := io.ReadStdinAll();
        assert IOContract.ReadStdinAllFields(preStdin, io.stdin(), data);
        assert data == preStdin;
        assert io.stdin() == IOContract.AfterReadStdinFields(preStdin);
        var out := RenderData(cmd, data);
        io.AppendStdout(out);
        exit := 0;
    }
    assert CoreSummary(raw, io, exit);
  }
}
