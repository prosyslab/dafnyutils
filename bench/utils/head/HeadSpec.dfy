include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "HeadSchema.dfy"
include "HeadRecordSpec.dfy"

module HeadSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import HeadSchema
  import HeadRecordSpec





  function HelpText(): BenchWorld.Bytes
  {
    "Usage: head [OPTION]... [FILE]...\n"
    + "Print the first 10 lines of each FILE to standard output.\n"
    + "With more than one FILE, precede each with a header giving the file name.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "  -c, --bytes=[-]NUM       print the first NUM bytes of each file;\n"
    + "                             with '-', print all but the last NUM bytes\n"
    + "  -n, --lines=[-]NUM       print the first NUM lines instead of 10;\n"
    + "                             with '-', print all but the last NUM lines\n"
    + "  -z, --zero-terminated    line delimiter is NUL, not newline\n"
    + "  -q, --quiet, --silent    never print headers giving file names\n"
    + "  -v, --verbose            always print headers giving file names\n"
    + "      --help               display this help and exit\n"
    + "      --version            output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/head>\n"
    + "or available locally via: info '(coreutils) head invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "head (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie and Jim Meyering.\n"
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

  function QuotedPath(path: BenchWorld.Path): string
  {
    "'" + path + "'"
  }

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    if err == BenchWorld.IsDirectory then
      Utf8.Encode("head: error reading " + QuotedPath(path) + ": " + ErrnoText(err) + "\n")
    else
      Utf8.Encode("head: cannot open " + QuotedPath(path) + " for reading: " + ErrnoText(err) + "\n")
  }

  function InvalidCountMessage(unit: HeadSchema.CountUnit, value: string): BenchWorld.Bytes
  {
    var displayValue := if |value| > 0 && value[0] == '-' then value[1..] else value;
    Utf8.Encode("head: invalid number of " +
    (if unit == HeadSchema.CountLines then "lines" else "bytes") +
    ": '" + displayValue + "'\n")
  }

  function InputsFromOperands(operands: seq<string>): seq<HeadSchema.Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then HeadSchema.Stdin("standard input") else HeadSchema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  }

  function HelpBeforeOther(raw: HeadSchema.HeadCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) &&
    (raw.invalidCountTokenIndex == -1 || raw.helpTokenIndex <= raw.invalidCountTokenIndex)
  }

  function VersionBeforeInvalid(raw: HeadSchema.HeadCmdRaw): bool
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
  }

  function IsStdinInput(input: HeadSchema.Input): bool
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
  }

  ghost predicate ReadResultRelation(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    result: BenchWorld.Result<BenchWorld.Bytes>
  )
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin(_) =>
      result == BenchWorld.Ok(
        if exists j: nat :: j < i && IsStdinInput(cmd.inputs[j])
        then []
        else preStdin
      )
    case File(path) =>
      result == IOContract.ReadFileResultFields(preFs, path)
  }

  ghost predicate ByteSelectionRelation(
    data: BenchWorld.Bytes,
    count: nat,
    fromEnd: bool,
    output: BenchWorld.Bytes
  )
  {
    var cut :=
      if fromEnd
      then if |data| <= count then 0 else |data| - count
      else if |data| <= count then |data| else count;
    output == data[..cut]
  }

  // HeadSchema decodes modern and obsolete GNU count syntaxes, including
  // deterministic multiplier suffixes, into this shared finite selection model.
  ghost predicate DataSelectionRelation(
    cmd: HeadSchema.HeadCmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    if cmd.selection.unit == HeadSchema.CountBytes then
      ByteSelectionRelation(
        data, cmd.selection.amount, cmd.selection.fromEnd, output
      )
    else
      HeadRecordSpec.RecordSelectionRelation(
        data,
        cmd.selection.amount,
        HeadRecordSpec.RecordDelimiter(cmd.zeroTerminated),
        cmd.selection.fromEnd,
        output
      )
  }

  function ShouldPrintHeaders(cmd: HeadSchema.HeadCmd): bool
  {
    cmd.headerMode == HeadSchema.HeadersAlways ||
    (cmd.headerMode == HeadSchema.HeadersMultiple && |cmd.inputs| > 1)
  }

  function HeaderForInput(cmd: HeadSchema.HeadCmd, input: HeadSchema.Input, printedHeaders: int): BenchWorld.Bytes
  {
    if ShouldPrintHeaders(cmd) then
      (if printedHeaders == 0 then [] else ['\n']) +
      "==> " + Utf8.Encode(InputName(input)) + " <==\n"
    else
      []
  }

  ghost predicate InputObservationRelation(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    result: BenchWorld.Result<BenchWorld.Bytes>,
                              printedHeaders: nat,
                              output: BenchWorld.Bytes,
                              errorOutput: BenchWorld.Bytes,
                              successful: bool,
                              failed: bool
  )
    requires i < |cmd.inputs|
  {
    ReadResultRelation(cmd, preFs, preStdin, i, result) &&
    (match cmd.inputs[i]
     case Stdin(_) =>
       (match result
        case Ok(data) =>
          exists selected: BenchWorld.Bytes ::
            DataSelectionRelation(cmd, data, selected) &&
            output == HeaderForInput(cmd, cmd.inputs[i], printedHeaders) + selected &&
            errorOutput == [] &&
            successful &&
            !failed
        case Err(_) => false)
     case File(path) =>
       (match result
        case Ok(data) =>
          exists selected: BenchWorld.Bytes ::
            DataSelectionRelation(cmd, data, selected) &&
            output == HeaderForInput(cmd, cmd.inputs[i], printedHeaders) + selected &&
            errorOutput == [] &&
            successful &&
            !failed
        case Err(err) =>
          output == [] &&
          errorOutput == ErrorMessage(path, err) &&
          !successful &&
          failed))
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
    forall i: nat {:trigger cuts[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] &&
      cuts[i + 1] <= |combined| &&
      cuts[i + 1] == cuts[i] + |fragments[i]| &&
      combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  opaque ghost predicate InputTraceWitnessRelation(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool,
    results: seq<BenchWorld.Result<BenchWorld.Bytes>>,
    outputFragments: seq<BenchWorld.Bytes>,
    errorFragments: seq<BenchWorld.Bytes>,
    successful: seq<bool>,
    failed: seq<bool>,
    outputCuts: seq<nat>,
    errorCuts: seq<nat>
  )
  {
    |results| == |cmd.inputs| &&
    |outputFragments| == |cmd.inputs| &&
    |errorFragments| == |cmd.inputs| &&
    |successful| == |cmd.inputs| &&
    |failed| == |cmd.inputs| &&
    (forall i: nat | i < |cmd.inputs| ::
       InputObservationRelation(
         cmd, preFs, preStdin, i, results[i],
         |set j: nat | j < i && successful[j]|,
         outputFragments[i], errorFragments[i], successful[i], failed[i]
       )) &&
    FragmentsConcatenate(outputFragments, output, outputCuts) &&
    FragmentsConcatenate(errorFragments, errorOutput, errorCuts) &&
    hadError == (true in failed) &&
    postStdin ==
    (if exists i: nat :: i < |cmd.inputs| && IsStdinInput(cmd.inputs[i])
     then []
     else preStdin)
  }

  opaque ghost predicate InputTraceRelation(
    cmd: HeadSchema.HeadCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool
  )
  {
    exists results: seq<BenchWorld.Result<BenchWorld.Bytes>>,
      outputFragments: seq<BenchWorld.Bytes>,
      errorFragments: seq<BenchWorld.Bytes>,
      successful: seq<bool>,
      failed: seq<bool>,
      outputCuts: seq<nat>,
      errorCuts: seq<nat> ::
      InputTraceWitnessRelation(
        cmd, preFs, preStdin, postStdin, output, errorOutput, hadError,
        results, outputFragments, errorFragments, successful, failed,
        outputCuts, errorCuts
      )
  }

  twostate predicate Spec(raw: HeadSchema.HeadCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    if cmd.mode == HeadSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == HeadSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == HeadSchema.ModeInvalidCount then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue) &&
      exit == 1
    else
      exists output: BenchWorld.Bytes,
        errorOutput: BenchWorld.Bytes,
        hadError: bool ::
        InputTraceRelation(
          cmd, old(io.fs()), old(io.stdin()), io.stdin(),
          output, errorOutput, hadError
        ) &&
        io.stdout() == old(io.stdout()) + output &&
        io.stderr() == old(io.stderr()) + errorOutput &&
        exit == (if hadError then 1 else 0)
  }
}
