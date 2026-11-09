include "../Spec/TrSpec.dfy"
include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../Spec/TrSchema.dfy"

module TrCore {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import TrSchema
  import Schema = TrSchema
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
    squeezeSet: BenchWorld.Bytes,
    warnings: BenchWorld.Bytes
  )

  type SetDecode = Result.Result<BenchWorld.Bytes, string>
  datatype SetAtom = SetAtom(next: nat, bytes: BenchWorld.Bytes)

  function AtomAt(text: string, i: nat): SetAtom
    requires i < |text|
    ensures i < AtomAt(text, i).next <= |text|
  {
    SetAtom(Spec.AtomNext(text, i), Spec.AtomBytes(text, i))
  }

  function WarningBytesFrom(text: string, i: nat): BenchWorld.Bytes
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then []
    else Spec.WarningAtSpec(text, i) +
         WarningBytesFrom(text, AtomAt(text, i).next)
  } by method {
    if i == |text| {
      return [];
    }
    var atom := AtomAt(text, i);
    return Spec.WarningAtSpec(text, i) + WarningBytesFrom(text, atom.next);
  }

  function RangeChars(lo: char, hi: char): BenchWorld.Bytes
    requires 0 <= lo as int < 256
    requires 0 <= hi as int < 256
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
      Result.Ok([])
    else if Spec.StartsUnsupportedConstruct(text[i..]) then
      Result.Err(text)
    else
      var atom := AtomAt(text, i);
      if atom.next < |text| && text[atom.next] == '-' && atom.next + 1 < |text| then
        var end := AtomAt(text, atom.next + 1);
        if |atom.bytes| == 1 && |end.bytes| == 1 &&
           atom.bytes[0] as int < 256 && end.bytes[0] as int < 256 &&
           atom.bytes[0] as int <= end.bytes[0] as int then
          match DecodeSetFrom(text, end.next)
          case Ok(rest) => Result.Ok(RangeChars(atom.bytes[0], end.bytes[0]) + rest)
          case Err(_) => Result.Err(text)
        else
          Result.Err(text)
      else
        match DecodeSetFrom(text, atom.next)
        case Ok(rest) => Result.Ok(atom.bytes + rest)
        case Err(_) => Result.Err(text)
  } by method {
    if i == |text| {
      return Result.Ok([]);
    } else if Spec.StartsUnsupportedConstruct(text[i..]) {
      return Result.Err(text);
    } else {
      var atom := AtomAt(text, i);
      if atom.next < |text| && text[atom.next] == '-' && atom.next + 1 < |text| {
        var end := AtomAt(text, atom.next + 1);
        if |atom.bytes| == 1 && |end.bytes| == 1 &&
           atom.bytes[0] as int < 256 && end.bytes[0] as int < 256 &&
           atom.bytes[0] as int <= end.bytes[0] as int {
          var tail := DecodeSetFrom(text, end.next);
          match tail
          case Ok(rest) =>
            return Result.Ok(RangeChars(atom.bytes[0], end.bytes[0]) + rest);
          case Err(_) =>
            return Result.Err(text);
        } else {
          return Result.Err(text);
        }
      } else {
        var tail := DecodeSetFrom(text, atom.next);
        match tail
        case Ok(rest) =>
          return Result.Ok(atom.bytes + rest);
        case Err(_) =>
          return Result.Err(text);
      }
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
      case Ok(_) => HasUnsupportedOperand(operands[1..])
      case Err(_) => operands[0]
  } by method {
    if |operands| == 0 {
      return "";
    } else {
      var decoded := DecodeSet(operands[0]);
      match decoded
      case Ok(_) =>
        return HasUnsupportedOperand(operands[1..]);
      case Err(_) =>
        return operands[0];
    }
  }

  function SetBytes(text: string): BenchWorld.Bytes
  {
    match DecodeSet(text)
    case Ok(bytes) => bytes
    case Err(_) => []
  } by method {
    var decoded := DecodeSet(text);
    return
      match decoded
      case Ok(bytes) => bytes
      case Err(_) => [];
  }

  // Deferred GNU behavior: classes, equivalence classes, repeats,
  // complements, truncate mode and locale-dependent collation remain outside
  // this literal-byte benchmark slice.
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
        ModeMissingOperand(Spec.MissingSet2MessageSpec(raw.operands[0], false))
      else if raw.seenDelete && raw.seenSqueeze && |raw.operands| == 1 then
        ModeMissingOperand(Spec.MissingSet2MessageSpec(raw.operands[0], true))
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
    var warnings :=
      (if |raw.operands| > 0 then WarningBytesFrom(raw.operands[0], 0) else []) +
      (if |raw.operands| > 1 && DecodeSet(raw.operands[0]).Ok? then
         WarningBytesFrom(raw.operands[1], 0) else []);
    TrCmd(mode, raw.seenDelete, raw.seenSqueeze, set1, set2, squeezeSet, warnings)
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
        ModeMissingOperand(Spec.MissingSet2MessageSpec(raw.operands[0], false))
      else if raw.seenDelete && raw.seenSqueeze && |raw.operands| == 1 then
        ModeMissingOperand(Spec.MissingSet2MessageSpec(raw.operands[0], true))
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
    var warnings: BenchWorld.Bytes := [];
    if |raw.operands| > 0 {
      warnings := WarningBytesFrom(raw.operands[0], 0);
      if |raw.operands| > 1 && DecodeSet(raw.operands[0]).Ok? {
        warnings := warnings + WarningBytesFrom(raw.operands[1], 0);
      }
    }
    return TrCmd(mode, raw.seenDelete, raw.seenSqueeze, set1, set2, squeezeSet, warnings);
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

  twostate predicate PreparedSummary(raw: TrSchema.TrCmdRaw, io: BenchIO.IO, exit: int, resultStdout: StreamWorld.Bytes, resultStderr: StreamWorld.Bytes)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    match cmd.mode
    case ModeHelp =>
      io.stdin() == old(io.stdin()) &&
      resultStdout == old(io.stdout()) + Spec.HelpTextSpec() &&
      resultStderr == old(io.stderr()) &&
      exit == 0
    case ModeVersion =>
      io.stdin() == old(io.stdin()) &&
      resultStdout == old(io.stdout()) + Spec.VersionTextSpec() &&
      resultStderr == old(io.stderr()) &&
      exit == 0
    case ModeMissingOperand(message) =>
      io.stdin() == old(io.stdin()) &&
      resultStdout == old(io.stdout()) &&
      resultStderr == old(io.stderr()) + message &&
      exit == 1
    case ModeExtraOperand(operand) =>
      io.stdin() == old(io.stdin()) &&
      resultStdout == old(io.stdout()) &&
      resultStderr == old(io.stderr()) +
      Spec.ExtraOperandMessageSpec(operand, |raw.operands| == 2) &&
      exit == 1
    case ModeUnsupportedSet(operand) =>
      io.stdin() == old(io.stdin()) &&
      resultStdout == old(io.stdout()) &&
      resultStderr == old(io.stderr()) + cmd.warnings +
      Spec.UnsupportedSetMessageSpec(operand) &&
      exit == 1
    case ModeEmptySet2 =>
      io.stdin() == old(io.stdin()) &&
      resultStdout == old(io.stdout()) &&
      resultStderr == old(io.stderr()) + Spec.EmptySet2MessageSpec() &&
      exit == 1
    case ModeRun =>
      var read := IOContract.ObservedReadStdinResultFields(old(io.stdin()), old(io.trustedStreams()));
      var input := IOContract.ReadResultData(read);
      io.stdin() == IOContract.ObservedReadStdinRemainingFields(old(io.stdin()), old(io.trustedStreams())) &&
      resultStdout == old(io.stdout()) + RenderData(cmd, input) &&
      resultStderr == old(io.stderr()) + cmd.warnings +
      (if read.Ok? then [] else Spec.ReadError(IOContract.ResultErrno(read))) &&
      exit == (if read.Ok? then 0 else 1)
  }

  twostate predicate CoreSummary(raw: Schema.TrCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSummary(raw, io, normalExit, old(io.stdout()) + output, old(io.stderr()) + diagnostics) &&
      Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit)
  }

  method Prepare(raw: TrSchema.TrCmdRaw, io: BenchIO.IO) returns (exit: int, resultStdout: StreamWorld.Bytes, resultStderr: StreamWorld.Bytes)
    modifies io.stdinRegion
    ensures PreparedSummary(raw, io, exit, old(io.stdout()) + resultStdout, old(io.stderr()) + resultStderr)
    decreases *
  {
    hide *;
    reveal PreparedSummary();
    ghost var emissionBeforeOut := io.stdout();
    ghost var emissionBeforeErr := io.stderr();
    resultStdout := [];
    resultStderr := [];
    ghost var preStdin := io.stdin();
    var cmd := Command(raw);

    match cmd.mode {
      case ModeHelp =>
        resultStdout := resultStdout + (Spec.HelpTextSpec());
        exit := 0;
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + resultStdout, emissionBeforeErr + resultStderr);
        return;
      case ModeVersion =>
        resultStdout := resultStdout + (Spec.VersionTextSpec());
        exit := 0;
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + resultStdout, emissionBeforeErr + resultStderr);
        return;
      case ModeMissingOperand(message) =>
        resultStderr := resultStderr + (message);
        exit := 1;
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + resultStdout, emissionBeforeErr + resultStderr);
        return;
      case ModeExtraOperand(operand) =>
        resultStderr := resultStderr + (Spec.ExtraOperandMessageSpec(operand, |raw.operands| == 2));
        exit := 1;
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + resultStdout, emissionBeforeErr + resultStderr);
        return;
      case ModeUnsupportedSet(operand) =>
        resultStderr := resultStderr + (cmd.warnings);
        resultStderr := resultStderr + (Spec.UnsupportedSetMessageSpec(operand));
        exit := 1;
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + resultStdout, emissionBeforeErr + resultStderr);
        return;
      case ModeEmptySet2 =>
        resultStderr := resultStderr + (Spec.EmptySet2MessageSpec());
        exit := 1;
        assert PreparedSummary(raw, io, exit, emissionBeforeOut + resultStdout, emissionBeforeErr + resultStderr);
        return;
      case ModeRun =>
        resultStderr := resultStderr + (cmd.warnings);
        var read := io.ReadStdin();
        var data := IOContract.ReadResultData(read);
        var out := RenderData(cmd, data);
        resultStdout := resultStdout + (out);
        if read.Err? {
          var reason := io.GetCLocaleErrnoText(IOContract.ResultErrno(read));
          resultStderr := resultStderr + (Spec.ReadErrorText(reason));
          assert Spec.ReadErrorText(reason) == Spec.ReadError(IOContract.ResultErrno(read)) by {
            reveal Spec.ReadError();
          }
        }
        exit := if read.Ok? then 0 else 1;
    }
    assert PreparedSummary(raw, io, exit, emissionBeforeOut + resultStdout, emissionBeforeErr + resultStderr);
  }


  method Flush(output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
               normalExit: int, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                io.trustedStreams(), output, diagnostics, normalExit, exit)
  {
    var committed: nat := 0;
    var outErr := 0;
    if |output| != 0 {
      var result := io.WriteStdout(output);
      committed := StreamContract.WriteResultCommitted(result);
      outErr := StreamContract.ResultErrno(result);
    }
    var finalDiagnostics := diagnostics;
    if outErr != 0 {
      var reason := io.GetCLocaleErrnoText(outErr);
      finalDiagnostics := diagnostics + (if normalExit != 0 then
                                           Spec.WriteErrorAfterReadFailure() else Spec.WriteErrorText(reason));
    }
    assert finalDiagnostics == diagnostics + (if outErr == 0 then []
                                              else if normalExit != 0 then Spec.WriteErrorAfterReadFailure()
                                              else Spec.WriteErrorText(StreamContract.CLocaleErrnoTextResult(outErr)));
    var errCommitted: nat := 0;
    var errErr := 0;
    if |finalDiagnostics| != 0 {
      var result := io.WriteStderr(finalDiagnostics);
      errCommitted := StreamContract.WriteResultCommitted(result);
      errErr := StreamContract.ResultErrno(result);
      assert StreamContract.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                                            finalDiagnostics, errCommitted, errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
    assert Spec.EmissionOutcomeFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                      io.trustedStreams(), output, diagnostics, normalExit, exit, committed, outErr, errCommitted, errErr);
  }

  method RunCore(raw: Schema.TrCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var normalExit, output, diagnostics := Prepare(raw, io);
    exit := Flush(output, diagnostics, normalExit, io);
  }
}
