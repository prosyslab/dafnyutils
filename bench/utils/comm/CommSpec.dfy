include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "CommSchema.dfy"
include "CommRenderSpec.dfy"

module CommSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = CommSchema
  import Render = CommRenderSpec




  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: comm [OPTION]... FILE1 FILE2\n"
    + "Compare sorted files FILE1 and FILE2 line by line.\n"
    + "\n"
    + "  -1                      suppress lines unique to FILE1\n"
    + "  -2                      suppress lines unique to FILE2\n"
    + "  -3                      suppress lines common to both files\n"
    + "      --output-delimiter=STR  separate columns with STR\n"
    + "      --total             output a summary row\n"
    + "  -z, --zero-terminated   line delimiter is NUL, not newline\n"
    + "      --help              display this help and exit\n"
    + "      --version           output version information and exit\n"
    + "\n"
    + "Benchmark note: sorted byte records, one optional stdin operand, and no locale collation.\n"
    + "Deferred: precise GNU sortedness diagnostics, repeated stdin operands, and locale.\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "comm (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Richard M. Stallman and David MacKenzie.\n"
  }

  function ErrnoText(err: BenchWorld.IOError): string
  {
    match err
    case NoSuchFile => "No such file or directory"
    case IsDirectory => "Is a directory"
    case NotDirectory => "Not a directory"
    case PermissionDenied => "Permission denied"
    case InvalidPath => "Too many levels of symbolic links"
    case Other(msg) => msg
  }

  function ContainsDiagnosticBlank(path: string): bool
    decreases |path|
  {
    if |path| == 0 then
      false
    else
      path[0] == ' ' || path[0] == '\t' || ContainsDiagnosticBlank(path[1..])
  }

  function QuoteIfNeeded(path: string): string
  {
    if ContainsDiagnosticBlank(path) then "'" + path + "'" else path
  }

  function FileErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    "comm: " + QuoteIfNeeded(path) + ": " + ErrnoText(err) + "\n"
  }

  function InputErrorMessageSpec(input: Schema.CommInput, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    match input
    case Stdin => "comm: -: " + Utf8.Encode(ErrnoText(err)) + "\n"
    case File(path) => FileErrorMessageSpec(path, err)
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "comm: missing operand\nTry 'comm --help' for more information.\n"
  }

  function MissingOperandAfterMessageSpec(operand: string): BenchWorld.Bytes
  {
    "comm: missing operand after '" + operand + "'\n" +
    "Try 'comm --help' for more information.\n"
  }

  function ExtraOperandMessageSpec(operand: string): BenchWorld.Bytes
  {
    "comm: extra operand '" + operand + "'\n" +
    "Try 'comm --help' for more information.\n"
  }

  function MultipleOutputDelimitersMessageSpec(): BenchWorld.Bytes
  {
    "comm: multiple output delimiters specified\n"
  }

  function UnsortedInputMessageSpec(): BenchWorld.Bytes
  {
    "comm: input is not sorted in the benchmark-supported byte order\n"
  }

  function RepeatedStdinOperandMessageSpec(): BenchWorld.Bytes
  {
    "comm: repeated standard input operands are not supported by this benchmark slice\n" +
    "Try 'comm --help' for more information.\n"
  }

  function FirstOperand(operands: seq<string>): string
  {
    if |operands| > 0 then operands[0] else ""
  }

  function SecondOperand(operands: seq<string>): string
  {
    if |operands| > 1 then operands[1] else ""
  }

  function InputFromOperand(operand: string): Schema.CommInput
  {
    if operand == "-" then Schema.Stdin else Schema.File(operand)
  }

  ghost function CommandRelation(raw: Schema.CommCmdRaw): Schema.CommCmd
  {
    var first := FirstOperand(raw.operands);
    var second := SecondOperand(raw.operands);
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        Schema.ModeHelp
      else if raw.seenVersion then
        Schema.ModeVersion
      else if Render.HasConflictingOutputDelimitersRelation(raw.outputDelimiters) then
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
  }

  function InputResult(
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    input: Schema.CommInput
  ): BenchWorld.Result<BenchWorld.Bytes>
  {
    match input
    case Stdin => BenchWorld.Ok(preStdin)
    case File(path) => IOContract.ReadFileResultFields(preFs, path)
  }

  function AfterInputRead(preStdin: BenchWorld.Bytes, input: Schema.CommInput): BenchWorld.Bytes
  {
    match input
    case Stdin => IOContract.AfterReadStdinFields(preStdin)
    case File(_) => preStdin
  }

  function ReadFirstResult(
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

  function AfterFirstRead(cmd: Schema.CommCmd, preStdin: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if cmd.mode == Schema.ModeRun then AfterInputRead(preStdin, cmd.input1) else preStdin
  }

  function ReadSecondResult(
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

  function AfterSecondRead(cmd: Schema.CommCmd, preStdin: BenchWorld.Bytes): BenchWorld.Bytes
  {
    if cmd.mode == Schema.ModeRun then AfterInputRead(AfterFirstRead(cmd, preStdin), cmd.input2) else preStdin
  }

  // Formal specification gap: this relation intentionally preserves the
  // benchmark's simple byte-order sortedness diagnostic and excludes locale
  // collation, --check-order/--nocheck-order partial-output behavior, and
  // repeated-stdin file-descriptor diagnostics.
  twostate predicate SpecCmd(cmd: Schema.CommCmd, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    match cmd.mode
    case ModeHelp =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    case ModeVersion =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    case ModeMissingOperand =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MissingOperandMessageSpec() &&
      exit == 1
    case ModeMissingOperandAfter(operand) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MissingOperandAfterMessageSpec(operand) &&
      exit == 1
    case ModeExtraOperand(operand) =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + ExtraOperandMessageSpec(operand) &&
      exit == 1
    case ModeMultipleOutputDelimiters =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MultipleOutputDelimitersMessageSpec() &&
      exit == 1
    case ModeRepeatedStdinOperand =>
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + RepeatedStdinOperandMessageSpec() &&
      exit == 1
    case ModeRun =>
      var first := ReadFirstResult(cmd, old(io.fs()), old(io.stdin()));
      match first
      case Err(err) =>
        io.stdin() == AfterFirstRead(cmd, old(io.stdin())) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + InputErrorMessageSpec(cmd.input1, err) &&
        exit == 1
      case Ok(leftData) =>
        var second := ReadSecondResult(cmd, old(io.fs()), old(io.stdin()));
        match second
        case Err(err) =>
          io.stdin() == AfterSecondRead(cmd, old(io.stdin())) &&
          io.stdout() == old(io.stdout()) &&
          io.stderr() == old(io.stderr()) + InputErrorMessageSpec(cmd.input2, err) &&
          exit == 1
        case Ok(rightData) =>
          io.stdin() == AfterSecondRead(cmd, old(io.stdin())) &&
          ((Render.DataSortedRelation(leftData, cmd.zeroTerminated) &&
            Render.DataSortedRelation(rightData, cmd.zeroTerminated) &&
            (exists stdoutPart: BenchWorld.Bytes ::
               Render.OutputRelation(cmd, leftData, rightData, stdoutPart) &&
               io.stdout() == old(io.stdout()) + stdoutPart) &&
            io.stderr() == old(io.stderr()) &&
            exit == 0) ||
           ((Render.DataUnsorted(leftData, cmd.zeroTerminated) ||
             Render.DataUnsorted(rightData, cmd.zeroTerminated)) &&
            io.stdout() == old(io.stdout()) &&
            io.stderr() == old(io.stderr()) + UnsortedInputMessageSpec() &&
            exit == 1))
  }

  twostate predicate Spec(raw: Schema.CommCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    SpecCmd(CommandRelation(raw), io, exit)
  }
}
