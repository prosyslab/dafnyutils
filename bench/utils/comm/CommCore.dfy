include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "CommSchema.dfy"
include "CommRenderCore.dfy"
include "CommSpec.dfy"

module CommCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = CommSchema
  import Render = CommRenderCore
  import Spec = CommSpec

  ghost function FirstOperand(operands: seq<string>): string
  {
    if |operands| > 0 then operands[0] else ""
  }

  ghost function SecondOperand(operands: seq<string>): string
  {
    if |operands| > 1 then operands[1] else ""
  }

  function InputFromOperand(operand: string): Schema.CommInput
  {
    if operand == "-" then Schema.Stdin else Schema.File(operand)
  } by method {
    return if operand == "-" then Schema.Stdin else Schema.File(operand);
  }

  function Command(raw: Schema.CommCmdRaw): Schema.CommCmd
  {
    var first := FirstOperand(raw.operands);
    var second := SecondOperand(raw.operands);
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        Schema.ModeHelp
      else if raw.seenVersion then
        Schema.ModeVersion
      else if Render.HasConflictingOutputDelimiters(raw.outputDelimiters) then
        Schema.ModeMultipleOutputDelimiters
      else if |raw.operands| == 0 then
        Schema.ModeMissingOperand
      else if |raw.operands| == 1 then
        Schema.ModeMissingOperandAfter(raw.operands[0])
      else if |raw.operands| > 2 then
        Schema.ModeExtraOperand(raw.operands[2])
      else if first == "-" && second == "-" then
        Schema.ModeRepeatedStdinOperand
      else
        Schema.ModeRun;
    Schema.CommCmd(
      mode,
      raw.suppress1,
      raw.suppress2,
      raw.suppress3,
      raw.total,
      raw.zeroTerminated,
      Render.OutputDelimiterFromValues(raw.outputDelimiters),
      InputFromOperand(first),
      InputFromOperand(second)
    )
  } by method {
    var first := if |raw.operands| > 0 then raw.operands[0] else "";
    var second := if |raw.operands| > 1 then raw.operands[1] else "";
    var conflicting := Render.HasConflictingOutputDelimiters(raw.outputDelimiters);
    var delimiter := Render.OutputDelimiterFromValues(raw.outputDelimiters);
    var input1 := InputFromOperand(first);
    var input2 := InputFromOperand(second);
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        Schema.ModeHelp
      else if raw.seenVersion then
        Schema.ModeVersion
      else if conflicting then
        Schema.ModeMultipleOutputDelimiters
      else if |raw.operands| == 0 then
        Schema.ModeMissingOperand
      else if |raw.operands| == 1 then
        Schema.ModeMissingOperandAfter(raw.operands[0])
      else if |raw.operands| > 2 then
        Schema.ModeExtraOperand(raw.operands[2])
      else if first == "-" && second == "-" then
        Schema.ModeRepeatedStdinOperand
      else
        Schema.ModeRun;
    return Schema.CommCmd(
        mode,
        raw.suppress1,
        raw.suppress2,
        raw.suppress3,
        raw.total,
        raw.zeroTerminated,
        delimiter,
        input1,
        input2
      );
  }

  ghost function InputResult(
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    input: Schema.CommInput
  ): BenchWorld.Result<BenchWorld.Bytes>
  {
    match input
    case Stdin => BenchWorld.Ok(preStdin)
    case File(path) => IOContract.ReadFileResultFields(preFs, path)
  }

  ghost function AfterInputRead(preStdin: BenchWorld.Bytes, input: Schema.CommInput): BenchWorld.Bytes
  {
    match input
    case Stdin => IOContract.AfterReadStdinFields(preStdin)
    case File(_) => preStdin
  }

  ghost function ReadFirstResult(
    cmd: Schema.CommCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes
  ): BenchWorld.Result<BenchWorld.Bytes>
  {
    if cmd.mode == Schema.ModeRun then
      InputResult(preFs, preStdin, cmd.input1)
    else
      BenchWorld.Ok([])
  }

  ghost function AfterFirstRead(cmd: Schema.CommCmd, preStdin: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if cmd.mode == Schema.ModeRun then AfterInputRead(preStdin, cmd.input1) else preStdin
  }

  ghost function ReadSecondResult(
    cmd: Schema.CommCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes
  ): BenchWorld.Result<BenchWorld.Bytes>
  {
    if cmd.mode == Schema.ModeRun then
      InputResult(preFs, AfterFirstRead(cmd, preStdin), cmd.input2)
    else
      BenchWorld.Ok([])
  }

  ghost function AfterSecondRead(cmd: Schema.CommCmd, preStdin: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if cmd.mode == Schema.ModeRun then AfterInputRead(AfterFirstRead(cmd, preStdin), cmd.input2) else preStdin
  }

  function OutputForReads(
    cmd: Schema.CommCmd,
    first: BenchWorld.Result<BenchWorld.Bytes>,
                             second: BenchWorld.Result<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match first
    case Ok(leftData) =>
      (match second
       case Ok(rightData) =>
         if Render.DataSorted(leftData, cmd.zeroTerminated) &&
            Render.DataSorted(rightData, cmd.zeroTerminated) then
           Render.RenderData(cmd, leftData, rightData)
         else
           []
       case Err(_) => [])
    case Err(_) => []
  } by method {
    var out: BenchWorld.Bytes;
    match first {
      case Ok(leftData) =>
        match second {
          case Ok(rightData) =>
            var leftSorted := Render.DataSorted(leftData, cmd.zeroTerminated);
            var rightSorted := Render.DataSorted(rightData, cmd.zeroTerminated);
            if leftSorted && rightSorted {
              out := Render.RenderData(cmd, leftData, rightData);
            } else {
              out := [];
            }
          case Err(_) =>
            out := [];
        }
      case Err(_) =>
        out := [];
    }
    return out;
  }

  function ErrorForReads(
    cmd: Schema.CommCmd,
    first: BenchWorld.Result<BenchWorld.Bytes>,
                             second: BenchWorld.Result<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match first
    case Err(err) => Spec.InputErrorMessageSpec(cmd.input1, err)
    case Ok(leftData) =>
      match second
      case Err(err) => Spec.InputErrorMessageSpec(cmd.input2, err)
      case Ok(rightData) =>
        if Render.DataSorted(leftData, cmd.zeroTerminated) &&
           Render.DataSorted(rightData, cmd.zeroTerminated) then [] else Spec.UnsortedInputMessageSpec()
  } by method {
    var err: BenchWorld.Bytes;
    match first {
      case Err(readErr) =>
        err := Spec.InputErrorMessageSpec(cmd.input1, readErr);
      case Ok(leftData) =>
        match second {
          case Err(readErr) =>
            err := Spec.InputErrorMessageSpec(cmd.input2, readErr);
          case Ok(rightData) =>
            var leftSorted := Render.DataSorted(leftData, cmd.zeroTerminated);
            var rightSorted := Render.DataSorted(rightData, cmd.zeroTerminated);
            if leftSorted && rightSorted {
              err := [];
            } else {
              err := Spec.UnsortedInputMessageSpec();
            }
        }
    }
    return err;
  }

  function HadRunError(
    cmd: Schema.CommCmd,
    first: BenchWorld.Result<BenchWorld.Bytes>,
                             second: BenchWorld.Result<BenchWorld.Bytes>
  ): bool
  {
    match first
    case Err(_) => true
    case Ok(leftData) =>
      match second
      case Err(_) => true
      case Ok(rightData) =>
        !Render.DataSorted(leftData, cmd.zeroTerminated) ||
        !Render.DataSorted(rightData, cmd.zeroTerminated)
  } by method {
    var hadError: bool;
    match first {
      case Err(_) =>
        hadError := true;
      case Ok(leftData) =>
        match second {
          case Err(_) =>
            hadError := true;
          case Ok(rightData) =>
            var leftSorted := Render.DataSorted(leftData, cmd.zeroTerminated);
            var rightSorted := Render.DataSorted(rightData, cmd.zeroTerminated);
            hadError := !leftSorted || !rightSorted;
        }
    }
    return hadError;
  }

  twostate predicate CoreSummary(raw: Schema.CommCmdRaw, io: BenchIO.IO, exit: int)
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
    case ModeMissingOperand =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MissingOperandMessageSpec() &&
      exit == 1
    case ModeMissingOperandAfter(operand) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MissingOperandAfterMessageSpec(operand) &&
      exit == 1
    case ModeExtraOperand(operand) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.ExtraOperandMessageSpec(operand) &&
      exit == 1
    case ModeMultipleOutputDelimiters =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MultipleOutputDelimitersMessageSpec() &&
      exit == 1
    case ModeRepeatedStdinOperand =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.RepeatedStdinOperandMessageSpec() &&
      exit == 1
    case ModeRun =>
      var first := ReadFirstResult(cmd, old(io.fs()), old(io.stdin()));
      match first
      case Err(_) =>
        io.stdin() == AfterFirstRead(cmd, old(io.stdin())) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + ErrorForReads(cmd, first, BenchWorld.Ok([])) &&
        exit == 1
      case Ok(_) =>
        var second := ReadSecondResult(cmd, old(io.fs()), old(io.stdin()));
        io.stdin() == AfterSecondRead(cmd, old(io.stdin())) &&
        io.stdout() == old(io.stdout()) + OutputForReads(cmd, first, second) &&
        io.stderr() == old(io.stderr()) + ErrorForReads(cmd, first, second) &&
        exit == (if HadRunError(cmd, first, second) then 1 else 0)
  }

  method ReadInputMethod(input: Schema.CommInput, io: BenchIO.IO) returns (result: BenchWorld.Result<BenchWorld.Bytes>)
    modifies io.stdinRegion
    ensures result == InputResult(old(io.fs()), old(io.stdin()), input)
    ensures io.stdin() == AfterInputRead(old(io.stdin()), input)
  {
    match input
    case Stdin =>
      var data := io.ReadStdinAll();
      result := BenchWorld.Ok(data);
    case File(path) =>
      result := io.ReadFile(path);
  }

  method RunCore(raw: Schema.CommCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStdin := io.stdin();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Command(raw);

    match cmd.mode {
      case ModeHelp =>
        var help := Spec.HelpTextSpec();
        io.AppendStdout(help);
        exit := 0;
        assert io.stdin() == preStdin;
        assert io.stderr() == preStderr;
        assert io.stdout() == preStdout + Spec.HelpTextSpec();
        return;
      case ModeVersion =>
        var version := Spec.VersionTextSpec();
        io.AppendStdout(version);
        exit := 0;
        assert io.stdin() == preStdin;
        assert io.stderr() == preStderr;
        assert io.stdout() == preStdout + Spec.VersionTextSpec();
        return;
      case ModeMissingOperand =>
        var msg := Spec.MissingOperandMessageSpec();
        io.AppendStderr(msg);
        exit := 1;
        assert io.stdin() == preStdin;
        assert io.stdout() == preStdout;
        assert io.stderr() == preStderr + Spec.MissingOperandMessageSpec();
        return;
      case ModeMissingOperandAfter(operand) =>
        var msg := Spec.MissingOperandAfterMessageSpec(operand);
        io.AppendStderr(msg);
        exit := 1;
        assert io.stdin() == preStdin;
        assert io.stdout() == preStdout;
        assert io.stderr() == preStderr + Spec.MissingOperandAfterMessageSpec(operand);
        return;
      case ModeExtraOperand(operand) =>
        var msg := Spec.ExtraOperandMessageSpec(operand);
        io.AppendStderr(msg);
        exit := 1;
        assert io.stdin() == preStdin;
        assert io.stdout() == preStdout;
        assert io.stderr() == preStderr + Spec.ExtraOperandMessageSpec(operand);
        return;
      case ModeMultipleOutputDelimiters =>
        var msg := Spec.MultipleOutputDelimitersMessageSpec();
        io.AppendStderr(msg);
        exit := 1;
        assert io.stdin() == preStdin;
        assert io.stdout() == preStdout;
        assert io.stderr() == preStderr + Spec.MultipleOutputDelimitersMessageSpec();
        return;
      case ModeRepeatedStdinOperand =>
        var msg := Spec.RepeatedStdinOperandMessageSpec();
        io.AppendStderr(msg);
        exit := 1;
        assert io.stdin() == preStdin;
        assert io.stdout() == preStdout;
        assert io.stderr() == preStderr + Spec.RepeatedStdinOperandMessageSpec();
        return;
      case ModeRun =>
        var first := ReadInputMethod(cmd.input1, io);
        assert first == ReadFirstResult(cmd, preFs, preStdin);
        assert io.stdin() == AfterFirstRead(cmd, preStdin);
        if first.Err? {
          var err := ErrorForReads(cmd, first, BenchWorld.Ok([]));
          io.AppendStderr(err);
          exit := 1;
          assert io.stdout() == preStdout;
          assert io.stderr() == preStderr + ErrorForReads(cmd, first, BenchWorld.Ok([]));
          return;
        } else {
          ghost var stdinAfterFirst := io.stdin();
          var second := ReadInputMethod(cmd.input2, io);
          assert stdinAfterFirst == AfterFirstRead(cmd, preStdin);
          assert second == InputResult(preFs, stdinAfterFirst, cmd.input2);
          assert second == ReadSecondResult(cmd, preFs, preStdin);
          assert io.stdin() == AfterInputRead(stdinAfterFirst, cmd.input2);
          assert io.stdin() == AfterSecondRead(cmd, preStdin);
          var out := OutputForReads(cmd, first, second);
          var err := ErrorForReads(cmd, first, second);
          var hadError := HadRunError(cmd, first, second);
          io.AppendStdout(out);
          io.AppendStderr(err);
          exit := if hadError then 1 else 0;
          assert io.stdout() == preStdout + OutputForReads(cmd, first, second);
          assert io.stderr() == preStderr + ErrorForReads(cmd, first, second);
          return;
        }
    }
  }
}
