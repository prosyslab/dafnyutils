include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "HeadSchema.dfy"
include "HeadRecordCore.dfy"
include "HeadSpec.dfy"

module HeadCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import HeadSchema
  import HeadRecordCore
  import Spec = HeadSpec

  function InputsFromOperands(operands: seq<string>): seq<HeadSchema.Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then HeadSchema.Stdin("standard input") else HeadSchema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  } by method {
    if |operands| == 0 {
      return [];
    } else {
      var input :=
        if operands[0] == "-"
        then HeadSchema.Stdin("standard input")
        else HeadSchema.File(operands[0]);
      return [input] + InputsFromOperands(operands[1..]);
    }
  }

  ghost function HelpBeforeOther(raw: HeadSchema.HeadCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) &&
    (raw.invalidCountTokenIndex == -1 || raw.helpTokenIndex <= raw.invalidCountTokenIndex)
  }

  ghost function VersionBeforeInvalid(raw: HeadSchema.HeadCmdRaw): bool
  {
    raw.seenVersion &&
    (raw.invalidCountTokenIndex == -1 || raw.versionTokenIndex <= raw.invalidCountTokenIndex)
  }

  function Command(raw: HeadSchema.HeadCmdRaw): HeadSchema.HeadCmd
  {
    var mode :=
      if HelpBeforeOther(raw) then
        HeadSchema.ModeHelp
      else if VersionBeforeInvalid(raw) then
        HeadSchema.ModeVersion
      else if raw.invalidCountTokenIndex != -1 then
        HeadSchema.ModeInvalidCount
      else
        HeadSchema.ModeRun;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == HeadSchema.ModeRun && |inputs| == 0 then [HeadSchema.Stdin("standard input")] else inputs;
    HeadSchema.HeadCmd(
      mode,
      raw.selection,
      raw.headerMode,
      raw.zeroTerminated,
      raw.invalidCountUnit,
      raw.invalidCountValue,
      runInputs
    )
  } by method {
    var mode :=
      if raw.seenHelp &&
         (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) &&
         (raw.invalidCountTokenIndex == -1 ||
          raw.helpTokenIndex <= raw.invalidCountTokenIndex) then
        HeadSchema.ModeHelp
      else if raw.seenVersion &&
              (raw.invalidCountTokenIndex == -1 ||
               raw.versionTokenIndex <= raw.invalidCountTokenIndex) then
        HeadSchema.ModeVersion
      else if raw.invalidCountTokenIndex != -1 then
        HeadSchema.ModeInvalidCount
      else
        HeadSchema.ModeRun;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs :=
      if mode == HeadSchema.ModeRun && |inputs| == 0
      then [HeadSchema.Stdin("standard input")]
      else inputs;
    return HeadSchema.HeadCmd(
        mode,
        raw.selection,
        raw.headerMode,
        raw.zeroTerminated,
        raw.invalidCountUnit,
        raw.invalidCountValue,
        runInputs
      );
  }

  ghost function IsStdinInput(input: HeadSchema.Input): bool
  {
    match input
    case Stdin(_) => true
    case File(_) => false
  }

  function InputName(input: HeadSchema.Input): string
  {
    match input
    case Stdin(displayName) => displayName
    case File(path) => path
  } by method {
    return
      match input
      case Stdin(displayName) => displayName
      case File(path) => path;
  }

  ghost function PrefixStdinCore(cmd: HeadSchema.HeadCmd, preStdin: BenchWorld.Bytes, i: nat): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      preStdin
    else
      match cmd.inputs[i - 1]
      case Stdin(_) => []
      case File(_) => PrefixStdinCore(cmd, preStdin, i - 1)
  }

  ghost function ReadResultCore(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): BenchWorld.Result<BenchWorld.Bytes>
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin(_) => BenchWorld.Ok(PrefixStdinCore(cmd, preStdin, i))
    case File(path) => IOContract.ReadFileResultFields(preFs, path)
  }

  function TakeFirstBytes(data: BenchWorld.Bytes, count: nat): BenchWorld.Bytes
  {
    if |data| <= count then data else data[..count]
  } by method {
    return if |data| <= count then data else data[..count];
  }

  function TakeAllButLastBytes(data: BenchWorld.Bytes, count: nat): BenchWorld.Bytes
  {
    if |data| <= count then [] else data[..|data| - count]
  } by method {
    return if |data| <= count then [] else data[..|data| - count];
  }

  function RenderData(cmd: HeadSchema.HeadCmd, data: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if cmd.selection.unit == HeadSchema.CountBytes then
      if cmd.selection.fromEnd then TakeAllButLastBytes(data, cmd.selection.amount) else TakeFirstBytes(data, cmd.selection.amount)
    else
      var delimiter := HeadRecordCore.RecordDelimiter(cmd.zeroTerminated);
      if cmd.selection.fromEnd then
        HeadRecordCore.TakeAllButLastRecords(data, cmd.selection.amount, delimiter)
      else
        HeadRecordCore.TakeFirstRecords(data, cmd.selection.amount, delimiter)
  } by method {
    if cmd.selection.unit == HeadSchema.CountBytes {
      if cmd.selection.fromEnd {
        return TakeAllButLastBytes(data, cmd.selection.amount);
      } else {
        return TakeFirstBytes(data, cmd.selection.amount);
      }
    } else {
      var delimiter := HeadRecordCore.RecordDelimiter(cmd.zeroTerminated);
      if cmd.selection.fromEnd {
        return HeadRecordCore.TakeAllButLastRecords(
            data, cmd.selection.amount, delimiter
          );
      } else {
        return HeadRecordCore.TakeFirstRecords(
            data, cmd.selection.amount, delimiter
          );
      }
    }
  }

  function ShouldPrintHeaders(cmd: HeadSchema.HeadCmd): bool
  {
    cmd.headerMode == HeadSchema.HeadersAlways ||
    (cmd.headerMode == HeadSchema.HeadersMultiple && |cmd.inputs| > 1)
  } by method {
    return cmd.headerMode == HeadSchema.HeadersAlways ||
           (cmd.headerMode == HeadSchema.HeadersMultiple && |cmd.inputs| > 1);
  }

  function HeaderForInput(cmd: HeadSchema.HeadCmd, input: HeadSchema.Input, printedHeaders: int): BenchWorld.Bytes
  {
    if ShouldPrintHeaders(cmd) then
      (if printedHeaders == 0 then [] else ['\n']) +
      "==> " + Utf8.Encode(InputName(input)) + " <==\n"
    else
      []
  } by method {
    if ShouldPrintHeaders(cmd) {
      return (if printedHeaders == 0 then [] else ['\n']) +
        "==> " + Utf8.Encode(InputName(input)) + " <==\n";
    } else {
      return [];
    }
  }

  function IsSuccessfulRead(result: BenchWorld.Result<BenchWorld.Bytes>): bool
  {
    match result
    case Ok(_) => true
    case Err(_) => false
  } by method {
    return
      match result
      case Ok(_) => true
      case Err(_) => false;
  }

  function OutputPiece(
    cmd: HeadSchema.HeadCmd,
    input: HeadSchema.Input,
    result: BenchWorld.Result<BenchWorld.Bytes>,
                              printedHeaders: int
  ): BenchWorld.Bytes
  {
    match result
    case Ok(data) => HeaderForInput(cmd, input, printedHeaders) + RenderData(cmd, data)
    case Err(_) => []
  } by method {
    match result
    case Ok(data) =>
      return HeaderForInput(cmd, input, printedHeaders) +
        RenderData(cmd, data);
    case Err(_) =>
      return [];
  }

  function ErrorPiece(input: HeadSchema.Input, result: BenchWorld.Result<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match input
    case Stdin(_) => []
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => Spec.ErrorMessage(path, err)
  } by method {
    match input
    case Stdin(_) =>
      return [];
    case File(path) =>
      match result
      case Ok(_) =>
        return [];
      case Err(err) =>
        return Spec.ErrorMessage(path, err);
  }

  function HadErrorPiece(input: HeadSchema.Input, result: BenchWorld.Result<BenchWorld.Bytes>): bool
  {
    match input
    case Stdin(_) => false
    case File(_) =>
      match result
      case Ok(_) => false
      case Err(_) => true
  } by method {
    return
      match input
      case Stdin(_) => false
      case File(_) =>
        match result
        case Ok(_) => false
        case Err(_) => true;
  }

  ghost function PrefixSuccessCountCore(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): nat
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      0
    else
      PrefixSuccessCountCore(cmd, preFs, preStdin, i - 1) +
      (if IsSuccessfulRead(ReadResultCore(cmd, preFs, preStdin, i - 1)) then 1 else 0)
  }

  ghost function PrefixOutputCore(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixOutputCore(cmd, preFs, preStdin, i - 1) +
      OutputPiece(
        cmd,
        cmd.inputs[i - 1],
        ReadResultCore(cmd, preFs, preStdin, i - 1),
        PrefixSuccessCountCore(cmd, preFs, preStdin, i - 1)
      )
  }

  ghost function PrefixErrorOutputCore(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): BenchWorld.Bytes
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      []
    else
      PrefixErrorOutputCore(cmd, preFs, preStdin, i - 1) +
      ErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1))
  }

  ghost function PrefixHadErrorCore(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  ): bool
    requires i <= |cmd.inputs|
    decreases i
  {
    if i == 0 then
      false
    else
      PrefixHadErrorCore(cmd, preFs, preStdin, i - 1) ||
      HadErrorPiece(cmd.inputs[i - 1], ReadResultCore(cmd, preFs, preStdin, i - 1))
  }

  ghost function RunOutputCore(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes
  ): BenchWorld.Bytes
  {
    PrefixOutputCore(cmd, preFs, preStdin, |cmd.inputs|)
  }

  twostate predicate CoreSummary(raw: HeadSchema.HeadCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    if cmd.mode == HeadSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == HeadSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == HeadSchema.ModeInvalidCount then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue) &&
      exit == 1
    else
      io.stdin() == PrefixStdinCore(cmd, old(io.stdin()), |cmd.inputs|) &&
      io.stdout() == old(io.stdout()) + RunOutputCore(cmd, old(io.fs()), old(io.stdin())) &&
      io.stderr() == old(io.stderr()) + PrefixErrorOutputCore(cmd, old(io.fs()), old(io.stdin()), |cmd.inputs|) &&
      exit == (if PrefixHadErrorCore(cmd, old(io.fs()), old(io.stdin()), |cmd.inputs|) then 1 else 0)
  }

  lemma PrefixStdinCoreStep(cmd: HeadSchema.HeadCmd, preStdin: BenchWorld.Bytes, i: nat)
    requires i < |cmd.inputs|
    ensures PrefixStdinCore(cmd, preStdin, i + 1) ==
            match cmd.inputs[i]
            case Stdin(_) => IOContract.AfterReadStdinFields(PrefixStdinCore(cmd, preStdin, i))
            case File(_) => PrefixStdinCore(cmd, preStdin, i)
  {
  }

  lemma PrefixSuccessCountCoreStep(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixSuccessCountCore(cmd, preFs, preStdin, i + 1) ==
            PrefixSuccessCountCore(cmd, preFs, preStdin, i) +
            (if IsSuccessfulRead(ReadResultCore(cmd, preFs, preStdin, i)) then 1 else 0)
  {
  }

  lemma PrefixOutputCoreStep(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixOutputCore(cmd, preFs, preStdin, i + 1) ==
            PrefixOutputCore(cmd, preFs, preStdin, i) +
            OutputPiece(
              cmd,
              cmd.inputs[i],
              ReadResultCore(cmd, preFs, preStdin, i),
              PrefixSuccessCountCore(cmd, preFs, preStdin, i)
            )
  {
  }

  lemma PrefixErrorOutputCoreStep(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixErrorOutputCore(cmd, preFs, preStdin, i + 1) ==
            PrefixErrorOutputCore(cmd, preFs, preStdin, i) +
            ErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i))
  {
  }

  lemma PrefixHadErrorCoreStep(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat
  )
    requires i < |cmd.inputs|
    ensures PrefixHadErrorCore(cmd, preFs, preStdin, i + 1) ==
            (PrefixHadErrorCore(cmd, preFs, preStdin, i) ||
             HadErrorPiece(cmd.inputs[i], ReadResultCore(cmd, preFs, preStdin, i)))
  {
  }

  method RunCore(raw: HeadSchema.HeadCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStdin := io.stdin();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Command(raw);

    if cmd.mode == HeadSchema.ModeHelp {
      var help := Spec.HelpText();
      io.AppendStdout(help);
      exit := 0;
      assert io.stdin() == preStdin;
      assert io.stderr() == preStderr;
      assert io.stdout() == preStdout + Spec.HelpText();
      return;
    }

    if cmd.mode == HeadSchema.ModeVersion {
      var version := Spec.VersionText();
      io.AppendStdout(version);
      exit := 0;
      assert io.stdin() == preStdin;
      assert io.stderr() == preStderr;
      assert io.stdout() == preStdout + Spec.VersionText();
      return;
    }

    if cmd.mode == HeadSchema.ModeInvalidCount {
      var invalid :=
        Spec.InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue);
      io.AppendStderr(invalid);
      exit := 1;
      assert io.stdin() == preStdin;
      assert io.stdout() == preStdout;
      assert io.stderr() == preStderr + Spec.InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue);
      return;
    }

    var out: BenchWorld.Bytes := [];
    var err: BenchWorld.Bytes := [];
    var hadError := false;
    var successes := 0;

    var i := 0;
    while i < |cmd.inputs|
      invariant 0 <= i <= |cmd.inputs|
      invariant io.stdin() == PrefixStdinCore(cmd, preStdin, i)
      invariant io.stdout() == preStdout
      invariant io.stderr() == preStderr
      invariant out == PrefixOutputCore(cmd, preFs, preStdin, i)
      invariant err == PrefixErrorOutputCore(cmd, preFs, preStdin, i)
      invariant hadError == PrefixHadErrorCore(cmd, preFs, preStdin, i)
      invariant successes == PrefixSuccessCountCore(cmd, preFs, preStdin, i)
      decreases |cmd.inputs| - i
    {
      var input := cmd.inputs[i];
      var readResult: BenchWorld.Result<BenchWorld.Bytes>;
      match input {
        case Stdin(_) =>
          ghost var beforeStdin := io.stdin();
          var data := io.ReadStdinAll();
          readResult := BenchWorld.Ok(data);
          PrefixStdinCoreStep(cmd, preStdin, i);
          PrefixSuccessCountCoreStep(cmd, preFs, preStdin, i);
          PrefixOutputCoreStep(cmd, preFs, preStdin, i);
          PrefixErrorOutputCoreStep(cmd, preFs, preStdin, i);
          PrefixHadErrorCoreStep(cmd, preFs, preStdin, i);
          assert beforeStdin == PrefixStdinCore(cmd, preStdin, i);
          assert IOContract.ReadStdinAllFields(beforeStdin, io.stdin(), data);
          assert data == beforeStdin;
        case File(path) =>
          readResult := io.ReadFile(path);
      }
      if input.File? {
        PrefixStdinCoreStep(cmd, preStdin, i);
        PrefixSuccessCountCoreStep(cmd, preFs, preStdin, i);
        PrefixOutputCoreStep(cmd, preFs, preStdin, i);
        PrefixErrorOutputCoreStep(cmd, preFs, preStdin, i);
        PrefixHadErrorCoreStep(cmd, preFs, preStdin, i);
      }
      assert readResult == ReadResultCore(cmd, preFs, preStdin, i);

      var piece := OutputPiece(cmd, input, readResult, successes);
      var errorPiece := ErrorPiece(input, readResult);
      var inputHadError := HadErrorPiece(input, readResult);
      var ok := IsSuccessfulRead(readResult);

      out := out + piece;
      err := err + errorPiece;
      hadError := hadError || inputHadError;
      successes := successes + (if ok then 1 else 0);
      i := i + 1;
    }

    if |out| > 0 {
      io.AppendStdout(out);
    } else {
      assert out == [];
      assert io.stdout() == preStdout + out;
    }
    if |err| > 0 {
      io.AppendStderr(err);
    } else {
      assert err == [];
      assert io.stderr() == preStderr + err;
    }
    exit := if hadError then 1 else 0;

    assert out == RunOutputCore(cmd, preFs, preStdin);
    assert err == PrefixErrorOutputCore(cmd, preFs, preStdin, |cmd.inputs|);
    assert hadError == PrefixHadErrorCore(cmd, preFs, preStdin, |cmd.inputs|);
    assert io.stdin() == PrefixStdinCore(cmd, preStdin, |cmd.inputs|);
    assert io.stdout() == preStdout + RunOutputCore(cmd, preFs, preStdin);
    assert io.stderr() == preStderr + PrefixErrorOutputCore(cmd, preFs, preStdin, |cmd.inputs|);
  }
}
