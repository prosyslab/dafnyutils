include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "TailSchema.dfy"
include "TailRecordSpec.dfy"

module TailSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import TailSchema
  import TailRecordSpec



  datatype InputObservation = InputObservation(
    result: BenchWorld.Result<BenchWorld.Bytes>,
    stdoutFragment: BenchWorld.Bytes,
    stderrFragment: BenchWorld.Bytes,
    failed: bool,
    hasHeader: bool
  )

  function HelpText(): BenchWorld.Bytes
  {
    "Usage: tail [OPTION]... [FILE]...\n"
    + "Print the last 10 lines of each FILE to standard output.\n"
    + "With more than one FILE, precede each with a header giving the file name.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "  -c, --bytes=[+]NUM       output the last NUM bytes; or use -c +NUM to\n"
    + "                             output starting with byte NUM of each file\n"
    + "  -n, --lines=[+]NUM       output the last NUM lines, instead of the last 10;\n"
    + "                             or use -n +NUM to output starting with line NUM\n"
    + "  -z, --zero-terminated    line delimiter is NUL, not newline\n"
    + "  -q, --quiet, --silent    never print headers giving file names\n"
    + "  -v, --verbose            always print headers giving file names\n"
    + "      --help               display this help and exit\n"
    + "      --version            output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/tail>\n"
    + "or available locally via: info '(coreutils) tail invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "tail (GNU coreutils) 9.10.13-2cf49\n"
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
      Utf8.Encode("tail: error reading " + QuotedPath(path) + ": " + ErrnoText(err) + "\n")
    else
      Utf8.Encode("tail: cannot open " + QuotedPath(path) + " for reading: " + ErrnoText(err) + "\n")
  }

  function InvalidCountMessage(unit: TailSchema.CountUnit, value: string): BenchWorld.Bytes
  {
    var displayValue := if |value| > 0 && value[0] == '-' then value[1..] else value;
    Utf8.Encode("tail: invalid number of " +
    (if unit == TailSchema.CountLines then "lines" else "bytes") +
    ": '" + displayValue + "'\n")
  }

  function StandardInputName(): string
  {
    "standard input"
  }

  function HeaderText(name: string): BenchWorld.Bytes
  {
    "==> " + name + " <==\n"
  }

  function InputsFromOperands(operands: seq<string>): seq<TailSchema.Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then TailSchema.Stdin(StandardInputName()) else TailSchema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  }

  function HelpBeforeOther(raw: TailSchema.TailCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) &&
    (raw.invalidCountTokenIndex == -1 || raw.helpTokenIndex <= raw.invalidCountTokenIndex)
  }

  function VersionBeforeInvalid(raw: TailSchema.TailCmdRaw): bool
  {
    raw.seenVersion &&
    (raw.invalidCountTokenIndex == -1 || raw.versionTokenIndex <= raw.invalidCountTokenIndex)
  }

  function Command(raw: TailSchema.TailCmdRaw): TailSchema.TailCmd
  {
    var mode :=
      if HelpBeforeOther(raw) then
        TailSchema.ModeHelp
      else if VersionBeforeInvalid(raw) then
        TailSchema.ModeVersion
      else if raw.invalidCountTokenIndex != -1 then
        TailSchema.ModeInvalidCount
      else
        TailSchema.ModeRun;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs :=
      if mode == TailSchema.ModeRun && |inputs| == 0
      then [TailSchema.Stdin(StandardInputName())]
      else inputs;
    TailSchema.TailCmd(
      mode,
      raw.selection,
      raw.headerMode,
      raw.zeroTerminated,
      raw.invalidCountUnit,
      raw.invalidCountValue,
      runInputs
    )
  }

  function IsStdinInput(input: TailSchema.Input): bool
  {
    match input
    case Stdin(_) => true
    case File(_) => false
  }

  function InputName(input: TailSchema.Input): string
  {
    match input
    case Stdin(displayName) => displayName
    case File(path) => path
  }

  ghost predicate ReadResultRelation(
    cmd: TailSchema.TailCmd,
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
        if exists j: nat :: j < i && cmd.inputs[j].Stdin? then [] else preStdin
      )
    case File(path) => result == IOContract.ReadFileResultFields(preFs, path)
  }

  ghost predicate DropFirstBytesRelation(
    data: BenchWorld.Bytes,
    count: nat,
    out: BenchWorld.Bytes
  )
  {
    out == data[(if count < |data| then count else |data|)..]
  }

  ghost predicate TakeLastBytesRelation(
    data: BenchWorld.Bytes,
    count: nat,
    out: BenchWorld.Bytes
  )
  {
    out == data[(if |data| <= count then 0 else |data| - count)..]
  }

  // Deferred GNU behavior: follow mode, PID waiting, retry, inotify,
  // overflow-sensitive suffix families beyond the finite exa-scale model, and
  // huge sparse/device cases are outside this benchmark slice.  The World
  // relation models finite decoded byte/record counts supplied by TailSchema,
  // including GNU-compatible leading obsolete count tokens.
  ghost predicate RenderDataRelation(
    cmd: TailSchema.TailCmd,
    data: BenchWorld.Bytes,
    out: BenchWorld.Bytes
  )
  {
    if cmd.selection.unit == TailSchema.CountBytes then
      if cmd.selection.fromStart then
        DropFirstBytesRelation(
          data,
          if cmd.selection.amount == 0 then 0 else cmd.selection.amount - 1,
          out
        )
      else
        TakeLastBytesRelation(data, cmd.selection.amount, out)
    else
      var delimiter := TailRecordSpec.RecordDelimiter(cmd.zeroTerminated);
      if cmd.selection.fromStart then
        TailRecordSpec.DropFirstRecordsRelation(
          data,
          if cmd.selection.amount == 0 then 0 else cmd.selection.amount - 1,
          delimiter,
          out
        )
      else
        TailRecordSpec.TakeLastRecordsRelation(
          data,
          cmd.selection.amount,
          delimiter,
          out
        )
  }

  function ShouldPrintHeaders(cmd: TailSchema.TailCmd): bool
  {
    cmd.headerMode == TailSchema.HeadersAlways ||
    (cmd.headerMode == TailSchema.HeadersMultiple && |cmd.inputs| > 1)
  }

  function SuppressZeroTrailingSelection(cmd: TailSchema.TailCmd): bool
  {
    !cmd.selection.fromStart && cmd.selection.amount == 0
  }

  function HeaderForInput(cmd: TailSchema.TailCmd, input: TailSchema.Input, printedHeaders: int): BenchWorld.Bytes
  {
    if ShouldPrintHeaders(cmd) then
      (if printedHeaders == 0 then [] else ['\n']) +
      HeaderText(InputName(input))
    else
      []
  }

  function ResultHasHeader(cmd: TailSchema.TailCmd, result: BenchWorld.Result<BenchWorld.Bytes>): bool
  {
    match result
    case Ok(_) => !SuppressZeroTrailingSelection(cmd)
    case Err(err) => err == BenchWorld.IsDirectory
  }

  ghost predicate OutputFragmentRelation(
    cmd: TailSchema.TailCmd,
    input: TailSchema.Input,
    result: BenchWorld.Result<BenchWorld.Bytes>,
                              printedHeaders: nat,
                              fragment: BenchWorld.Bytes
  )
  {
    match result
    case Ok(data) =>
      if SuppressZeroTrailingSelection(cmd) then
        fragment == []
      else
        exists rendered: BenchWorld.Bytes ::
          RenderDataRelation(cmd, data, rendered) &&
          fragment == HeaderForInput(cmd, input, printedHeaders) + rendered
    case Err(err) =>
      fragment ==
      (if err == BenchWorld.IsDirectory
       then HeaderForInput(cmd, input, printedHeaders)
       else [])
  }

  function ErrorPiece(input: TailSchema.Input, result: BenchWorld.Result<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match input
    case Stdin(_) => []
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => ErrorMessage(path, err)
  }

  function HadErrorPiece(input: TailSchema.Input, result: BenchWorld.Result<BenchWorld.Bytes>): bool
  {
    match input
    case Stdin(_) => false
    case File(_) =>
      match result
      case Ok(_) => false
      case Err(_) => true
  }

  ghost predicate InputObservationRelation(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    observation: InputObservation,
    priorHeaderCount: nat
  )
    requires i < |cmd.inputs|
  {
    ReadResultRelation(cmd, preFs, preStdin, i, observation.result) &&
    OutputFragmentRelation(
      cmd,
      cmd.inputs[i],
      observation.result,
      priorHeaderCount,
      observation.stdoutFragment
    ) &&
    observation.stderrFragment == ErrorPiece(cmd.inputs[i], observation.result) &&
    observation.failed == HadErrorPiece(cmd.inputs[i], observation.result) &&
    observation.hasHeader == ResultHasHeader(cmd, observation.result)
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
    forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] <= |combined| &&
      cuts[i + 1] == cuts[i] + |fragments[i]| &&
      combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost function ObservationStdoutFragments(
    observations: seq<InputObservation>
  ): seq<BenchWorld.Bytes>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| => observations[i].stdoutFragment
      )
  }

  ghost function ObservationStderrFragments(
    observations: seq<InputObservation>
  ): seq<BenchWorld.Bytes>
  {
    seq(
    |observations|,
    i requires 0 <= i < |observations| => observations[i].stderrFragment
      )
  }

  ghost predicate InputTraceWitnessRelation(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    stdoutPart: BenchWorld.Bytes,
    stderrPart: BenchWorld.Bytes,
    hadError: bool,
    observations: seq<InputObservation>,
    headerCounts: seq<nat>,
    stdoutCuts: seq<nat>,
    stderrCuts: seq<nat>
  )
  {
    |observations| == |cmd.inputs| &&
    |headerCounts| == |observations| + 1 &&
    headerCounts[0] == 0 &&
    (forall i: nat {:trigger headerCounts[i], headerCounts[i + 1]} |
       i < |observations| ::
       headerCounts[i + 1] ==
       headerCounts[i] + (if observations[i].hasHeader then 1 else 0)) &&
    (forall i: nat {:trigger observations[i]} | i < |observations| ::
       InputObservationRelation(
         cmd,
         preFs,
         preStdin,
         i,
         observations[i],
         headerCounts[i]
       )) &&
    FragmentsConcatenate(
      ObservationStdoutFragments(observations),
      stdoutPart,
      stdoutCuts
    ) &&
    FragmentsConcatenate(
      ObservationStderrFragments(observations),
      stderrPart,
      stderrCuts
    ) &&
    hadError == (exists i: nat :: i < |observations| && observations[i].failed) &&
    postStdin ==
    (if exists i: nat :: i < |cmd.inputs| && cmd.inputs[i].Stdin? then [] else preStdin)
  }

  ghost predicate InputTraceRelation(
    cmd: TailSchema.TailCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    stdoutPart: BenchWorld.Bytes,
    stderrPart: BenchWorld.Bytes,
    hadError: bool
  )
  {
    exists observations: seq<InputObservation>,
      headerCounts: seq<nat>,
      stdoutCuts: seq<nat>,
      stderrCuts: seq<nat> ::
      InputTraceWitnessRelation(
        cmd,
        preFs,
        preStdin,
        postStdin,
        stdoutPart,
        stderrPart,
        hadError,
        observations,
        headerCounts,
        stdoutCuts,
        stderrCuts
      )
  }

  twostate predicate Spec(raw: TailSchema.TailCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    if cmd.mode == TailSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == TailSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == TailSchema.ModeInvalidCount then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + InvalidCountMessage(cmd.invalidCountUnit, cmd.invalidCountValue) &&
      exit == 1
    else if SuppressZeroTrailingSelection(cmd) then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      exists stdoutPart: BenchWorld.Bytes, stderrPart: BenchWorld.Bytes, hadError: bool ::
        InputTraceRelation(
          cmd,
          old(io.fs()),
          old(io.stdin()),
          io.stdin(),
          stdoutPart,
          stderrPart,
          hadError
        ) &&
        io.stdout() == old(io.stdout()) + stdoutPart &&
        io.stderr() == old(io.stderr()) + stderrPart &&
        exit == (if hadError then 1 else 0)
  }
}
