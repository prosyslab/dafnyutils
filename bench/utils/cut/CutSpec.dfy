include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "CutSchema.dfy"

module CutSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import CutSchema

  function HelpText(): BenchWorld.Bytes
  {
    "Usage: cut OPTION... [FILE]...\n"
    + "Print selected bytes or characters from each line of each FILE.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "  -b, --bytes=LIST        select only these bytes\n"
    + "  -c, --characters=LIST   select only these characters\n"
    + "      --complement        complement the set of selected bytes or characters\n"
    + "  -n                      parsed for compatibility; no effect in byte mode\n"
    + "      --output-delimiter=STRING  use STRING between selected byte/character ranges\n"
    + "  -z, --zero-terminated   line delimiter is NUL, not newline\n"
    + "      --help              display this help and exit\n"
    + "      --version           output version information and exit\n"
    + "\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/cut>\n"
    + "or available locally via: info '(coreutils) cut invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "cut (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David M. Ihnat, David MacKenzie, and Jim Meyering.\n"
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

  function PathQuoteChar(ch: char): bool
  {
    ch == ' ' || ch == '=' || ch == ':' || ch == '|' || ch == ';'
  }

  function PathNeedsQuotes(path: BenchWorld.Path): bool
    decreases |path|
  {
    |path| > 0 && (PathQuoteChar(path[0]) || PathNeedsQuotes(path[1..]))
  }

  function DisplayPath(path: BenchWorld.Path): string
  {
    if PathNeedsQuotes(path) then "'" + path + "'" else path
  }

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    "cut: " + DisplayPath(path) + ": " + ErrnoText(err) + "\n"
  }

  function RangeContains(range: CutSchema.Range, pos: int): bool
  {
    if range.openEnd then
      range.first <= pos
    else
      range.first <= pos <= range.last
  }

  function RecordDelimiter(zeroTerminated: bool): BenchWorld.RawByte
  {
    if zeroTerminated then '\0' else '\n'
  }

  function OutputDelimiterBytes(delimiter: CutSchema.OutputDelimiter): BenchWorld.Bytes
  {
    match delimiter
    case OutputDefault => []
    case OutputCustom(text) => if |text| == 0 then ['\0'] else Utf8.Encode(text)
  }

  ghost predicate StrictlyIncreasing(indices: seq<nat>)
  {
    forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
  }

  ghost predicate PositionSelected(selection: CutSchema.Selection, position: int)
  {
    1 <= position &&
    selection.complement !=
    (exists i :: 0 <= i < |selection.ranges| &&
                 RangeContains(selection.ranges[i], position))
  }

  ghost predicate DelimiterBeforeSelected(
    command: CutSchema.CutCmdRaw,
    position: int
  )
  {
    command.outputDelimiter.OutputCustom? &&
    1 < position &&
    if command.selection.complement then
      !PositionSelected(command.selection, position - 1)
    else
      (!(exists i :: 0 <= i < |command.selection.ranges| &&
                     RangeContains(command.selection.ranges[i], position - 1) &&
                     RangeContains(command.selection.ranges[i], position)))
  }

  ghost predicate SelectedIndexSequence(
    selection: CutSchema.Selection,
    recordLength: nat,
    selectedIndices: seq<nat>
  )
  {
    StrictlyIncreasing(selectedIndices) &&
    (forall k {:trigger selectedIndices[k]} ::
       0 <= k < |selectedIndices| ==>
         selectedIndices[k] < recordLength &&
         PositionSelected(selection, selectedIndices[k] + 1)) &&
    (forall i {:trigger PositionSelected(selection, i + 1)} ::
       0 <= i < recordLength ==>
         PositionSelected(selection, i + 1) ==
         (i in selectedIndices))
  }

  ghost predicate RecordSelectionWitnessRelation(
    command: CutSchema.CutCmdRaw,
    record: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    selectedIndices: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    SelectedIndexSequence(
      command.selection, |record|, selectedIndices
    ) &&
    exists fragments: seq<BenchWorld.Bytes> ::
      |fragments| == |selectedIndices| &&
      (forall k :: 0 <= k < |selectedIndices| ==>
                     fragments[k] ==
                     (if k > 0 && DelimiterBeforeSelected(
                           command, selectedIndices[k] + 1
                         )
                      then OutputDelimiterBytes(command.outputDelimiter)
                      else []) +
                     [record[selectedIndices[k]]]) &&
      FragmentsConcatenate(fragments, output, outputCuts)
  }

  ghost predicate RecordSelectionRelation(
    command: CutSchema.CutCmdRaw,
    record: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists selectedIndices: seq<nat>, outputCuts: seq<nat> ::
      RecordSelectionWitnessRelation(
        command, record, output, selectedIndices, outputCuts
      )
  }

  ghost predicate RecordPartitionWitnessRelation(
    data: BenchWorld.Bytes,
    delimiter: BenchWorld.RawByte,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    |records| == |terminated| == |fragments| &&
    (|data| == 0) == (|records| == 0) &&
    (forall i :: 0 <= i < |records| ==>
                   |fragments[i]| > 0 &&
                   fragments[i] ==
                   records[i] + (if terminated[i] then [delimiter] else []) &&
                   delimiter !in records[i] &&
                   (i + 1 < |records| ==> terminated[i])) &&
    FragmentsConcatenate(fragments, data, cuts)
  }

  ghost predicate RecordPartitionRelation(
    data: BenchWorld.Bytes,
    delimiter: BenchWorld.RawByte,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>
  )
  {
    exists fragments: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
      RecordPartitionWitnessRelation(
        data, delimiter, records, terminated, fragments, cuts
      )
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
    forall i {:trigger cuts[i]} :: 0 <= i < |fragments| ==>
                                     cuts[i] <= cuts[i + 1] &&
                                     cuts[i + 1] <= |combined| &&
                                     cuts[i + 1] == cuts[i] + |fragments[i]| &&
                                     combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate DataSelectionWitnessRelation(
    command: CutSchema.CutCmdRaw,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    records: seq<BenchWorld.Bytes>,
    terminated: seq<bool>,
    fragments: seq<BenchWorld.Bytes>,
    renderedFragments: seq<BenchWorld.Bytes>,
    outputCuts: seq<nat>
  )
  {
    RecordPartitionRelation(
      data, RecordDelimiter(command.zeroTerminated), records, terminated
    ) &&
    |fragments| == |records| &&
    |renderedFragments| == |fragments| &&
    (forall i :: 0 <= i < |records| ==>
                   RecordSelectionRelation(command, records[i], fragments[i]) &&
                   renderedFragments[i] ==
                   fragments[i] + [RecordDelimiter(command.zeroTerminated)]) &&
    FragmentsConcatenate(renderedFragments, output, outputCuts)
  }

  ghost predicate DataSelectionRelation(
    command: CutSchema.CutCmdRaw,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists records: seq<BenchWorld.Bytes>,
      terminated: seq<bool>,
      fragments: seq<BenchWorld.Bytes>,
      renderedFragments: seq<BenchWorld.Bytes>,
      outputCuts: seq<nat> ::
      DataSelectionWitnessRelation(
        command, data, output, records, terminated, fragments,
        renderedFragments, outputCuts
      )
  }

  ghost predicate InputReadRelation(
    command: CutSchema.CutCmdRaw,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    index: nat,
    result: BenchWorld.Result<BenchWorld.Bytes>
  )
    requires index < |command.inputs|
  {
    match command.inputs[index]
    case Stdin =>
      result == BenchWorld.Ok(
        if CutSchema.Stdin in command.inputs[..index]
        then []
        else preStdin
      )
    case File(path) =>
      result == IOContract.ReadFileResultFields(preFs, path)
  }

  twostate predicate InputTraceRelation(
    command: CutSchema.CutCmdRaw,
    io: BenchIO.IO,
    new readResults: seq<BenchWorld.Result<BenchWorld.Bytes>>,
    new stdoutPart: BenchWorld.Bytes,
    new stderrPart: BenchWorld.Bytes,
    hadError: bool
  )
    reads io.Footprint()
  {
    exists stdoutFragments: seq<BenchWorld.Bytes>,
      stderrFragments: seq<BenchWorld.Bytes>,
      stdoutCuts: seq<nat>,
      stderrCuts: seq<nat> ::
      |readResults| == |command.inputs| &&
      |stdoutFragments| == |command.inputs| &&
      |stderrFragments| == |command.inputs| &&
      (forall i :: 0 <= i < |command.inputs| ==>
                     InputReadRelation(
                       command, old(io.fs()), old(io.stdin()), i, readResults[i]
                     ) &&
                     match command.inputs[i]
                     case Stdin =>
                       (match readResults[i]
                        case Ok(data) =>
                          DataSelectionRelation(command, data, stdoutFragments[i]) &&
                          stderrFragments[i] == []
                        case Err(_) => false)
                     case File(path) =>
                       (match readResults[i]
                        case Ok(data) =>
                          DataSelectionRelation(command, data, stdoutFragments[i]) &&
                          stderrFragments[i] == []
                        case Err(err) =>
                          stdoutFragments[i] == [] &&
                          stderrFragments[i] == ErrorMessage(path, err))) &&
      FragmentsConcatenate(stdoutFragments, stdoutPart, stdoutCuts) &&
      FragmentsConcatenate(stderrFragments, stderrPart, stderrCuts) &&
      hadError ==
      (exists i :: 0 <= i < |command.inputs| &&
                   command.inputs[i].File? && readResults[i].Err?)
  }

  twostate predicate Spec(raw: CutSchema.CutCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if raw.mode == CutSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if raw.mode == CutSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      exists readResults: seq<BenchWorld.Result<BenchWorld.Bytes>>,
        stdoutPart: BenchWorld.Bytes,
        stderrPart: BenchWorld.Bytes,
        hadError: bool ::
        InputTraceRelation(
          raw, io, readResults, stdoutPart, stderrPart, hadError
        ) &&
        io.stdin() ==
        (if CutSchema.Stdin in raw.inputs
         then []
         else old(io.stdin())) &&
        io.stdout() == old(io.stdout()) + stdoutPart &&
        io.stderr() == old(io.stderr()) + stderrPart &&
        exit == (if hadError then 1 else 0)
  }
}
