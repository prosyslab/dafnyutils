include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "TeeSchema.dfy"

module TeeSpec {
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = TeeSchema




  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: tee [OPTION]... [FILE]...\n"
    + "Copy standard input to each FILE, and also to standard output.\n"
    + "\n"
    + "  -a, --append              append to the given FILEs, do not overwrite\n"
    + "  -i, --ignore-interrupts   ignore interrupt signals\n"
    + "      --help     display this help and exit\n"
    + "      --version  output version information and exit\n"
    + "\n"
    + "Benchmark note: -i is parsed but has no effect because signal handling is\n"
    + "outside the modeled World. Pipe-error policy and special output devices are\n"
    + "not implemented in this benchmark slice.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/tee>\n"
    + "or available locally via: info '(coreutils) tee invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "tee (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Mike Parker, Richard M. Stallman, and David MacKenzie.\n"
  }

  function ReadErrnoTextSpec(err: BenchWorld.IOError): string
  {
    match err
    case NoSuchFile => "No such file or directory"
    case IsDirectory => "Is a directory"
    case NotDirectory => "Not a directory"
    case PermissionDenied => "Permission denied"
    case InvalidPath => "Too many levels of symbolic links"
    case Other(msg) => msg
  }

  function WriteErrnoTextSpec(err: int): string
  {
    if err == 2 then "No such file or directory"
    else if err == 13 then "Permission denied"
    else if err == 20 then "Not a directory"
    else if err == 21 then "Is a directory"
    else if err == 28 then "No space left on device"
    else if err == 40 then "Too many levels of symbolic links"
    else "unknown error"
  }

  function ReadErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    "tee: " + path + ": " + ReadErrnoTextSpec(err) + "\n"
  }

  function WriteErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    "tee: " + path + ": " + WriteErrnoTextSpec(err) + "\n"
  }

  function CommandSpec(raw: Schema.TeeCmdRaw): Schema.TeeCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        Schema.ModeHelp
      else if raw.seenVersion then
        Schema.ModeVersion
      else
        Schema.ModeRun;
    Schema.TeeCmd(mode, raw.seenAppend, raw.seenIgnoreInterrupts, raw.operands)
  }

  ghost predicate WriteOneSpecFields(
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
            stderr == (if ok then [] else WriteErrorMessageSpec(path, writeErr)) &&
            exit == (if ok then 0 else 1)
        else
          fs2 == preFs && stderr == ReadErrorMessageSpec(path, err) && exit == 1
      case Ok(oldData) =>
        exists ok: bool, writeErr: int ::
          IOContract.WriteFileContractFields(preFs, preNow, path, oldData + input, ok, writeErr, fs2) &&
          stderr == (if ok then [] else WriteErrorMessageSpec(path, writeErr)) &&
          exit == (if ok then 0 else 1)
    else
      exists ok: bool, writeErr: int ::
        IOContract.WriteFileContractFields(preFs, preNow, path, input, ok, writeErr, fs2) &&
        stderr == (if ok then [] else WriteErrorMessageSpec(path, writeErr)) &&
        exit == (if ok then 0 else 1)
  }

  datatype WriteState = WriteState(
    fs: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  )

  opaque ghost predicate WriteStepRelation(
    append: bool,
    path: BenchWorld.Path,
    input: BenchWorld.Bytes,
    preNow: int,
    before: WriteState,
    after: WriteState
  )
  {
    exists stepErr: BenchWorld.Bytes, stepExit: int ::
      WriteOneSpecFields(append, path, input, before.fs, preNow, after.fs, stepErr, stepExit) &&
      after.stderr == before.stderr + stepErr &&
      after.exit == (if before.exit == 0 && stepExit == 0 then 0 else 1)
  }

  opaque ghost predicate WriteOutputsSpecFields(
    append: bool,
    outputs: seq<BenchWorld.Path>,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  )
  {
    exists states: seq<WriteState> ::
      |states| == |outputs| + 1 &&
      states[0] == WriteState(preFs, [], 0) &&
      states[|outputs|] == WriteState(fs2, stderr, exit) &&
      forall i {:trigger WriteStepRelation(append, outputs[i], input, preNow, states[i], states[i + 1])} ::
        0 <= i < |outputs| ==>
          WriteStepRelation(append, outputs[i], input, preNow, states[i], states[i + 1])
  }

  twostate predicate Spec(raw: Schema.TeeCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := CommandSpec(raw);
    if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      exists errOut: BenchWorld.Bytes, writeExit: int ::
        WriteOutputsSpecFields(cmd.append, cmd.outputs, old(io.stdin()), old(io.fs()), old(io.now()), io.fs(), errOut, writeExit) &&
        io.stdin() == IOContract.AfterReadStdinFields(old(io.stdin())) &&
        io.stdout() == old(io.stdout()) + old(io.stdin()) &&
        io.stderr() == old(io.stderr()) + errOut &&
        exit == writeExit
  }
}
