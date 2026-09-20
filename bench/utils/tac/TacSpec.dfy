include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "../../core/CliTypes.dfy"
include "TacSchema.dfy"

module TacSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes
  import IOContract
  import TacSchema




  datatype InputObservation = InputObservation(
    result: BenchWorld.Result<BenchWorld.Bytes>,
    stdoutFragment: BenchWorld.Bytes,
    stderrFragment: BenchWorld.Bytes,
    failed: bool
  )

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: tac [OPTION]... [FILE]...\n"
    + "Write each FILE to standard output, last line first.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "This benchmark supports literal separators and before mode.\n"
    + "  -b, --before             attach the separator before instead of after\n"
    + "  -s, --separator=STRING   use STRING as the separator\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/tac>\n"
    + "or available locally via: info '(coreutils) tac invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "tac (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Jay Lepreau and David MacKenzie.\n"
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

  function ErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    match err
    case IsDirectory =>
      var displayPath :=
        if ' ' in path then "'" + path + "'"
        else path;
      Utf8.Encode("tac: " + displayPath + ": read error: " + ErrnoText(err) + "\n")
    case _ =>
      Utf8.Encode("tac: failed to open '" + path + "' for reading: " + ErrnoText(err) + "\n")
  }

  function InputsFromOperands(operands: seq<string>): seq<TacSchema.Input>
    decreases |operands|
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then TacSchema.Stdin else TacSchema.File(operands[0]))] +
      InputsFromOperands(operands[1..])
  }

  function Command(raw: TacSchema.TacCmdRaw): TacSchema.TacCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        TacSchema.ModeHelp
      else if raw.seenVersion then
        TacSchema.ModeVersion
      else
        TacSchema.ModeRun;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == TacSchema.ModeRun && |inputs| == 0 then [TacSchema.Stdin] else inputs;
    TacSchema.TacCmd(mode, raw.seenBefore, SeparatorValue(raw.separator), runInputs)
  }

  function SeparatorValue(raw: CliTypes.OptionalString): BenchWorld.Bytes
  {
    match raw
    case Some(value) => if value == "" then ['\0'] else Utf8.Encode(value)
    case None => ['\n']
  }

  ghost predicate ReadResultRelation(
    cmd: TacSchema.TacCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    result: BenchWorld.Result<BenchWorld.Bytes>
  )
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin =>
      result == BenchWorld.Ok(
        if TacSchema.Stdin in cmd.inputs[..i] then [] else preStdin
      )
    case File(path) => result == IOContract.ReadFileResultFields(preFs, path)
  }

  ghost function SeparatorStartSet(
    data: BenchWorld.Bytes,
    sep: BenchWorld.Bytes
  ): set<nat>
  {
    set start: nat {:trigger data[start..start + |sep|]} |
    start + |sep| <= |data| &&
    data[start..start + |sep|] == sep
  }

  ghost predicate SeparatorCutColumn(
    data: BenchWorld.Bytes,
    sep: BenchWorld.Bytes,
    starts: seq<nat>
  )
    requires |sep| > 0
  {
    (forall i: nat {:trigger starts[i]} | i < |starts| ::
       starts[i] + |sep| <= |data| &&
       data[starts[i]..starts[i] + |sep|] == sep) &&
    (forall i: nat {:trigger starts[i], starts[i + 1]} | i + 1 < |starts| ::
       starts[i] + |sep| <= starts[i + 1]) &&
    (forall start: nat
       {:trigger start in SeparatorStartSet(data, sep)} |
                                    start in SeparatorStartSet(data, sep) ::
       start in starts ||
       exists i: nat ::
         i < |starts| &&
         start < starts[i] < start + |sep|)
  }

  ghost predicate ReverseIntervalOrder(
    data: BenchWorld.Bytes,
    out: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    |inputCuts| == |outputCuts| &&
    0 < |inputCuts| &&
    inputCuts[0] == 0 &&
    inputCuts[|inputCuts| - 1] == |data| &&
    outputCuts[0] == 0 &&
    outputCuts[|outputCuts| - 1] == |out| &&
    (forall i: nat
       {:trigger inputCuts[i], inputCuts[i + 1]}
       {:trigger outputCuts[i], outputCuts[i + 1]} |
       i + 2 <= |inputCuts| ::
       inputCuts[|inputCuts| - i - 2] <=
       inputCuts[|inputCuts| - i - 1] <= |data| &&
       outputCuts[i] <= outputCuts[i + 1] <= |out| &&
       out[outputCuts[i]..outputCuts[i + 1]] ==
       data[inputCuts[|inputCuts| - i - 2]..inputCuts[|inputCuts| - i - 1]])
  }

  ghost predicate ReverseRecordsRelation(
    data: BenchWorld.Bytes,
    sep: BenchWorld.Bytes,
    before: bool,
    out: BenchWorld.Bytes
  )
    requires |sep| > 0
  {
    exists starts: seq<nat>, inputCuts: seq<nat>, outputCuts: seq<nat> ::
      SeparatorCutColumn(data, sep, starts) &&
      |inputCuts| == |starts| + 2 &&
      inputCuts ==
      [0] +
      seq(
      |starts|,
      i requires 0 <= i < |starts| =>
        starts[i] + (if before then 0 else |sep|)
        ) +
      [|data|] &&
      ReverseIntervalOrder(data, out, inputCuts, outputCuts)
  }

  ghost predicate OutputFragmentRelation(
    cmd: TacSchema.TacCmd,
    result: BenchWorld.Result<BenchWorld.Bytes>,
                              fragment: BenchWorld.Bytes
  )
    requires |cmd.separator| > 0
  {
    match result
    case Ok(data) => ReverseRecordsRelation(data, cmd.separator, cmd.before, fragment)
    case Err(_) => fragment == []
  }

  function ErrorPiece(input: TacSchema.Input, result: BenchWorld.Result<BenchWorld.Bytes>): BenchWorld.Bytes
  {
    match input
    case Stdin => []
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => ErrorMessageSpec(path, err)
  }

  function HadErrorPiece(input: TacSchema.Input, result: BenchWorld.Result<BenchWorld.Bytes>): bool
  {
    match input
    case Stdin => false
    case File(_) =>
      match result
      case Ok(_) => false
      case Err(_) => true
  }

  ghost predicate InputObservationRelation(
    cmd: TacSchema.TacCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    i: nat,
    observation: InputObservation
  )
    requires i < |cmd.inputs|
    requires |cmd.separator| > 0
  {
    ReadResultRelation(cmd, preFs, preStdin, i, observation.result) &&
    OutputFragmentRelation(cmd, observation.result, observation.stdoutFragment) &&
    observation.stderrFragment == ErrorPiece(cmd.inputs[i], observation.result) &&
    observation.failed == HadErrorPiece(cmd.inputs[i], observation.result)
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
    cmd: TacSchema.TacCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    stdoutPart: BenchWorld.Bytes,
    stderrPart: BenchWorld.Bytes,
    hadError: bool,
    observations: seq<InputObservation>,
    stdoutCuts: seq<nat>,
    stderrCuts: seq<nat>
  )
    requires |cmd.separator| > 0
  {
    |observations| == |cmd.inputs| &&
    (forall i: nat {:trigger observations[i]} | i < |observations| ::
       InputObservationRelation(cmd, preFs, preStdin, i, observations[i])) &&
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
    (if TacSchema.Stdin in cmd.inputs then [] else preStdin)
  }

  ghost predicate InputTraceRelation(
    cmd: TacSchema.TacCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    stdoutPart: BenchWorld.Bytes,
    stderrPart: BenchWorld.Bytes,
    hadError: bool
  )
    requires |cmd.separator| > 0
  {
    exists observations: seq<InputObservation>,
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
        stdoutCuts,
        stderrCuts
      )
  }

  twostate predicate Spec(raw: TacSchema.TacCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Command(raw);
    if cmd.mode == TacSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == TacSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
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
