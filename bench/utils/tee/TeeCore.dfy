include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "TeeSchema.dfy"
include "TeeSpec.dfy"

module TeeCore {
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = TeeSchema
  import Spec = TeeSpec

  ghost predicate WriteOneSummaryFields(
    append: bool,
    path: BenchWorld.Path,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  )
  {
    if append then
      match IOContract.ReadFileResultFields(preFs, path)
      case Err(err) =>
        if err == BenchWorld.NoSuchFile then
          exists ok: bool, writeErr: int ::
            IOContract.WriteFileContractFields(preFs, preNow, path, input, ok, writeErr, fs2) &&
            stderr == (if ok then [] else Spec.WriteErrorMessageSpec(path, writeErr)) &&
            exit == (if ok then 0 else 1)
        else
          fs2 == preFs && stderr == Spec.ReadErrorMessageSpec(path, err) && exit == 1
      case Ok(oldData) =>
        exists ok: bool, writeErr: int ::
          IOContract.WriteFileContractFields(preFs, preNow, path, oldData + input, ok, writeErr, fs2) &&
          stderr == (if ok then [] else Spec.WriteErrorMessageSpec(path, writeErr)) &&
          exit == (if ok then 0 else 1)
    else
      exists ok: bool, writeErr: int ::
        IOContract.WriteFileContractFields(preFs, preNow, path, input, ok, writeErr, fs2) &&
        stderr == (if ok then [] else Spec.WriteErrorMessageSpec(path, writeErr)) &&
        exit == (if ok then 0 else 1)
  }

  opaque ghost predicate WriteOutputsSummaryFields(
    append: bool,
    outputs: seq<BenchWorld.Path>,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  )
    decreases |outputs|
  {
    if |outputs| == 0 then
      fs2 == preFs && stderr == [] && exit == 0
    else
      exists prefixFs: BenchWorld.FileSystem, prefixErr: BenchWorld.Bytes, prefixExit: int,
        stepErr: BenchWorld.Bytes, stepExit: int
        {:trigger WriteOutputsSummaryFields(append, outputs[..|outputs| - 1], input, preFs, preNow, prefixFs, prefixErr, prefixExit),
        WriteOneSummaryFields(append, outputs[|outputs| - 1], input, prefixFs, preNow, fs2, stepErr, stepExit)} ::
        WriteOutputsSummaryFields(outputs := outputs[..|outputs| - 1], append := append,
                                  input := input, preFs := preFs, preNow := preNow,
                                  fs2 := prefixFs, stderr := prefixErr, exit := prefixExit) &&
        WriteOneSummaryFields(append, outputs[|outputs| - 1], input, prefixFs, preNow, fs2, stepErr, stepExit) &&
        stderr == prefixErr + stepErr &&
        exit == (if prefixExit == 0 && stepExit == 0 then 0 else 1)
  }

  function Command(raw: Schema.TeeCmdRaw): Schema.TeeCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        Schema.ModeHelp
      else if raw.seenVersion then
        Schema.ModeVersion
      else
        Schema.ModeRun;
    Schema.TeeCmd(mode, raw.seenAppend, raw.seenIgnoreInterrupts, raw.operands)
  } by method {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        Schema.ModeHelp
      else if raw.seenVersion then
        Schema.ModeVersion
      else
        Schema.ModeRun;
    return Schema.TeeCmd(mode, raw.seenAppend, raw.seenIgnoreInterrupts, raw.operands);
  }

  twostate predicate CoreSummary(raw: Schema.TeeCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      exists errOut: BenchWorld.Bytes, writeExit: int ::
        WriteOutputsSummaryFields(cmd.append, cmd.outputs, old(io.stdin()), old(io.fs()), old(io.now()), io.fs(), errOut, writeExit) &&
        io.stdin() == IOContract.AfterReadStdinFields(old(io.stdin())) &&
        io.stdout() == old(io.stdout()) + old(io.stdin()) &&
        io.stderr() == old(io.stderr()) + errOut &&
        exit == writeExit
  }

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpTextSpec()
  {
    out := Spec.HelpTextSpec();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionTextSpec()
  {
    out := Spec.VersionTextSpec();
  }

  method GetReadErrnoText(err: BenchWorld.IOError) returns (text: string)
    ensures text == Spec.ReadErrnoTextSpec(err)
  {
    text := Spec.ReadErrnoTextSpec(err);
  }

  method GetWriteErrnoText(err: int) returns (text: string)
    ensures text == Spec.WriteErrnoTextSpec(err)
  {
    text := Spec.WriteErrnoTextSpec(err);
  }

  method GetReadErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError) returns (msg: BenchWorld.Bytes)
    ensures msg == Spec.ReadErrorMessageSpec(path, err)
  {
    msg := Spec.ReadErrorMessageSpec(path, err);
  }

  method GetWriteErrorMessage(path: BenchWorld.Path, err: int) returns (msg: BenchWorld.Bytes)
    ensures msg == Spec.WriteErrorMessageSpec(path, err)
  {
    msg := Spec.WriteErrorMessageSpec(path, err);
  }

  method WriteOne(
    append: bool,
    path: BenchWorld.Path,
    input: BenchWorld.Bytes,
    io: BenchIO.IO
  ) returns (stderr: BenchWorld.Bytes, exit: int)
    modifies io.fsRegion
    ensures WriteOneSummaryFields(append, path, input, old(io.fs()), old(io.now()), io.fs(), stderr, exit)
  {
    if append {
      var read := io.ReadFile(path);
      match read
      case Ok(oldData) =>
        var ok, err := io.WriteFile(path, oldData + input);
        if ok {
          stderr := [];
          exit := 0;
        } else {
          stderr := GetWriteErrorMessage(path, err);
          exit := 1;
        }
      case Err(readErr) =>
        if readErr == BenchWorld.NoSuchFile {
          var ok, err := io.WriteFile(path, input);
          if ok {
            stderr := [];
            exit := 0;
          } else {
            stderr := GetWriteErrorMessage(path, err);
            exit := 1;
          }
        } else {
          stderr := GetReadErrorMessage(path, readErr);
          exit := 1;
        }
    } else {
      var ok, err := io.WriteFile(path, input);
      if ok {
        stderr := [];
        exit := 0;
      } else {
        stderr := GetWriteErrorMessage(path, err);
        exit := 1;
      }
    }
  }

  method WriteOutputs(
    append: bool,
    outputs: seq<BenchWorld.Path>,
    input: BenchWorld.Bytes,
    io: BenchIO.IO
  ) returns (stderr: BenchWorld.Bytes, exit: int)
    modifies io.fsRegion
    ensures WriteOutputsSummaryFields(append, outputs, input, old(io.fs()), old(io.now()), io.fs(), stderr, exit)
    decreases |outputs|
  {
    reveal WriteOutputsSummaryFields();
    if |outputs| == 0 {
      stderr := [];
      exit := 0;
    } else {
      var prefixErr, prefixExit := WriteOutputs(append, outputs[..|outputs| - 1], input, io);
      var stepErr, stepExit := WriteOne(append, outputs[|outputs| - 1], input, io);
      stderr := prefixErr + stepErr;
      exit := if prefixExit == 0 && stepExit == 0 then 0 else 1;
    }
  }

  method {:isolate_assertions} RunCore(raw: Schema.TeeCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStdin := io.stdin();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    ghost var preNow := io.now();
    var cmd := Command(raw);
    match cmd.mode
    case ModeHelp =>
      var out := GetHelpText();
      io.AppendStdout(out);
      exit := 0;
      assert io.fs() == preFs;
      assert io.stdin() == preStdin;
      assert io.stdout() == preStdout + Spec.HelpTextSpec();
      assert io.stderr() == preStderr;
      return;
    case ModeVersion =>
      var out := GetVersionText();
      io.AppendStdout(out);
      exit := 0;
      assert io.fs() == preFs;
      assert io.stdin() == preStdin;
      assert io.stdout() == preStdout + Spec.VersionTextSpec();
      assert io.stderr() == preStderr;
      return;
    case ModeRun =>
      var input := io.ReadStdinAll();
      assert IOContract.ReadStdinAllFields(preStdin, io.stdin(), input);
      assert input == preStdin;
      assert io.stdin() == IOContract.AfterReadStdinFields(preStdin);
      var errOut, writeExit := WriteOutputs(cmd.append, cmd.outputs, input, io);
      io.AppendStdout(input);
      io.AppendStderr(errOut);
      exit := writeExit;
      assert WriteOutputsSummaryFields(cmd.append, cmd.outputs, preStdin, preFs, preNow, io.fs(), errOut, writeExit);
      assert io.stdin() == IOContract.AfterReadStdinFields(preStdin);
      assert io.stdout() == preStdout + preStdin;
      assert io.stderr() == preStderr + errOut;
  }
}
