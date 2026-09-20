include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "TrSchema.dfy"

module TrSpec {
  import BenchIO
  import BenchWorld
  import IOContract
  import TrSchema




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
    squeezeSet: BenchWorld.Bytes
  )

  datatype SetDecode = SetOk(bytes: BenchWorld.Bytes) | SetUnsupported(operand: string)

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: tr [OPTION]... SET1 [SET2]\n"
    + "Translate, squeeze, and/or delete characters from standard input,\n"
    + "writing to standard output.\n"
    + "\n"
    + "  -d, --delete          delete characters in SET1\n"
    + "  -s, --squeeze-repeats replace repeated characters listed in the last SET\n"
    + "      --help            display this help and exit\n"
    + "      --version         output version information and exit\n"
    + "\n"
    + "Benchmark note: only literal ASCII bytes and ordered ASCII ranges like a-z\n"
    + "are implemented; character classes, escapes, repeats, complements,\n"
    + "truncate mode, locale behavior, and multibyte characters are deferred.\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "tr (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Jim Meyering.\n"
  }

  function MissingOperandMessageSpec(): BenchWorld.Bytes
  {
    "tr: missing operand\nTry 'tr --help' for more information.\n"
  }

  function MissingSet2MessageSpec(): BenchWorld.Bytes
  {
    "tr: missing operand after set1\nTry 'tr --help' for more information.\n"
  }

  function ExtraOperandMessageSpec(operand: string): BenchWorld.Bytes
  {
    "tr: extra operand '" + operand + "'\nTry 'tr --help' for more information.\n"
  }

  function UnsupportedSetMessageSpec(operand: string): BenchWorld.Bytes
  {
    "tr: unsupported set syntax '" + operand + "' in this benchmark\n"
  }

  function EmptySet2MessageSpec(): BenchWorld.Bytes
  {
    "tr: when not deleting, string2 must be non-empty in this benchmark\n"
  }

  function IsAscii(ch: char): bool
  {
    0 <= ch as int < 128
  }

  function IsSetSyntaxMarker(ch: char): bool
  {
    ch == '\\'
  }

  // Ghost, so the adjacent-pair test can be the existential it actually is and
  // the single-character test can be plain membership. `ContainsCharFrom` is
  // gone entirely: it was sequence membership written as index recursion.
  ghost predicate ContainsPair(text: string, first: char, second: char)
  {
    exists k :: 0 <= k < |text| - 1 && text[k] == first && text[k + 1] == second
  }

  ghost predicate StartsUnsupportedConstruct(text: string)
  {
    |text| > 0 && text[0] == '[' && (
      (1 < |text| && text[1] == ':' && ContainsPair(text[2..], ':', ']')) ||
      (1 < |text| && text[1] == '=' && ContainsPair(text[2..], '=', ']')) ||
      (2 < |text| && text[2] == '*' && ']' in text[3..])
    )
  }

  // Formal specification gap: GNU bracket classes, escapes, repeats,
  // complement/truncate modes, locale behavior, and multibyte characters are
  // intentionally rejected by this relation until modeled explicitly.
  ghost predicate RangeExpansion(lo: char, hi: char, bytes: BenchWorld.Bytes)
  {
    IsAscii(lo) &&
    IsAscii(hi) &&
    lo as int <= hi as int &&
    |bytes| == (hi as int) - (lo as int) + 1 &&
    forall i :: 0 <= i < |bytes| ==>
                  bytes[i] as int == lo as int + i
  }

  ghost predicate SetUnitRelation(
    text: string,
    lo: nat,
    hi: nat,
    bytes: BenchWorld.Bytes
  )
  {
    lo < |text| &&
    !StartsUnsupportedConstruct(text[lo..]) &&
    !IsSetSyntaxMarker(text[lo]) &&
    if lo + 2 < |text| && text[lo + 1] == '-' then
      hi == lo + 3 &&
      RangeExpansion(text[lo], text[lo + 2], bytes)
    else
      hi == lo + 1 &&
      IsAscii(text[lo]) &&
      bytes == [text[lo]]
  }

  ghost predicate SetPartitionFrom(
    text: string,
    start: nat,
    bytes: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    |inputCuts| == |outputCuts| &&
    0 < |inputCuts| &&
    start <= |text| &&
    inputCuts[0] == start &&
    outputCuts[0] == 0 &&
    inputCuts[|inputCuts| - 1] == |text| &&
    outputCuts[|outputCuts| - 1] == |bytes| &&
    forall i
      {:trigger inputCuts[i], inputCuts[i + 1]}
      {:trigger bytes[outputCuts[i]..outputCuts[i + 1]]} ::
      0 <= i && i + 1 < |inputCuts| ==>
        inputCuts[i] < inputCuts[i + 1] <= |text| &&
        outputCuts[i] <= outputCuts[i + 1] <= |bytes| &&
        SetUnitRelation(
          text,
          inputCuts[i],
          inputCuts[i + 1],
          bytes[outputCuts[i]..outputCuts[i + 1]]
        )
  }

  ghost predicate SetPartition(
    text: string,
    bytes: BenchWorld.Bytes,
    inputCuts: seq<nat>,
    outputCuts: seq<nat>
  )
  {
    SetPartitionFrom(text, 0, bytes, inputCuts, outputCuts)
  }

  ghost predicate SetBytesRelation(text: string, bytes: BenchWorld.Bytes)
  {
    exists inputCuts: seq<nat>, outputCuts: seq<nat> ::
      SetPartition(text, bytes, inputCuts, outputCuts)
  }

  ghost predicate SetDecodeRelation(text: string, decoded: SetDecode)
  {
    (exists bytes: BenchWorld.Bytes ::
       SetBytesRelation(text, bytes) &&
       decoded == SetOk(bytes)) ||
    ((forall bytes: BenchWorld.Bytes :: !SetBytesRelation(text, bytes)) &&
     decoded == SetUnsupported(text))
  }

  ghost predicate DecodedOperandsRelation(
    operands: seq<string>,
    decoded: seq<SetDecode>
  )
  {
    |decoded| == |operands| &&
    forall i :: 0 <= i < |operands| ==>
                  SetDecodeRelation(operands[i], decoded[i])
  }

  function DecodedBytes(decoded: SetDecode): BenchWorld.Bytes
  {
    match decoded
    case SetOk(bytes) => bytes
    case SetUnsupported(_) => []
  }

  ghost predicate FirstUnsupportedOperandRelation(
    operands: seq<string>,
    decoded: seq<SetDecode>,
    operand: string
  )
  {
    |decoded| == |operands| &&
    exists i ::
      0 <= i < |operands| &&
      decoded[i] == SetUnsupported(operands[i]) &&
      operand == operands[i] &&
      forall j :: 0 <= j < i ==> decoded[j].SetOk?
  }

  ghost predicate CommandDecodedRelation(
    raw: TrSchema.TrCmdRaw,
    decoded: seq<SetDecode>,
    cmd: TrCmd
  )
  {
    DecodedOperandsRelation(raw.operands, decoded) &&
    cmd.deleteSet == raw.seenDelete &&
    cmd.squeeze == raw.seenSqueeze &&
    cmd.set1 ==
    (if |raw.operands| > 0 then DecodedBytes(decoded[0]) else []) &&
    cmd.set2 ==
    (if |raw.operands| > 1 then DecodedBytes(decoded[1]) else []) &&
    cmd.squeezeSet ==
    (if raw.seenSqueeze && |raw.operands| > 1 then
       DecodedBytes(decoded[1])
     else if |raw.operands| > 0 then
       DecodedBytes(decoded[0])
     else
       []) &&
    if raw.seenHelp &&
       (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
      cmd.mode == ModeHelp
    else if raw.seenVersion then
      cmd.mode == ModeVersion
    else if |raw.operands| == 0 then
      cmd.mode == ModeMissingOperand(MissingOperandMessageSpec())
    else if !raw.seenDelete && !raw.seenSqueeze &&
            |raw.operands| == 1 then
      cmd.mode == ModeMissingOperand(MissingSet2MessageSpec())
    else if raw.seenDelete && raw.seenSqueeze &&
            |raw.operands| == 1 then
      cmd.mode == ModeMissingOperand(MissingSet2MessageSpec())
    else if raw.seenDelete && !raw.seenSqueeze &&
            |raw.operands| > 1 then
      cmd.mode == ModeExtraOperand(raw.operands[1])
    else if |raw.operands| > 2 then
      cmd.mode == ModeExtraOperand(raw.operands[2])
    else if exists operand ::
              FirstUnsupportedOperandRelation(raw.operands, decoded, operand) then
      exists operand ::
        FirstUnsupportedOperandRelation(raw.operands, decoded, operand) &&
        cmd.mode == ModeUnsupportedSet(operand)
    else if !raw.seenDelete && |raw.operands| == 2 &&
            |DecodedBytes(decoded[1])| == 0 then
      cmd.mode == ModeEmptySet2
    else
      cmd.mode == ModeRun
  }

  ghost predicate CommandRelation(raw: TrSchema.TrCmdRaw, cmd: TrCmd)
  {
    exists decoded: seq<SetDecode> ::
      CommandDecodedRelation(raw, decoded, cmd)
  }

  ghost predicate StrictlyIncreasing(indices: seq<nat>)
  {
    forall i, j :: 0 <= i < j < |indices| ==>
                     indices[i] < indices[j]
  }

  ghost predicate TranslationRelation(
    set1: BenchWorld.Bytes,
    set2: BenchWorld.Bytes,
    inputByte: char,
    outputByte: char
  )
  {
    if inputByte !in set1 then
      outputByte == inputByte
    else
      |set2| > 0 &&
      exists i ::
        0 <= i < |set1| &&
        set1[i] == inputByte &&
        (forall j :: i < j < |set1| ==> set1[j] != inputByte) &&
        outputByte == set2[if i < |set2| then i else |set2| - 1]
  }

  ghost predicate DeleteTranslateRelation(
    cmd: TrCmd,
    input: BenchWorld.Bytes,
    transformed: BenchWorld.Bytes
  )
  {
    exists kept: seq<nat> ::
      StrictlyIncreasing(kept) &&
      (forall k :: 0 <= k < |kept| ==> kept[k] < |input|) &&
      (forall i :: 0 <= i < |input| ==>
                     (i in kept) ==
                     (!cmd.deleteSet || input[i] !in cmd.set1)) &&
      |transformed| == |kept| &&
      (forall k :: 0 <= k < |kept| ==>
                     (if cmd.deleteSet || |cmd.set2| == 0 then
                        transformed[k] == input[kept[k]]
                      else
                        TranslationRelation(
                          cmd.set1,
                          cmd.set2,
                          input[kept[k]],
                          transformed[k]
                        )))
  }

  ghost predicate SqueezeStateRelation(
    input: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes,
    hasPrevious: bool,
    previous: char,
    output: BenchWorld.Bytes
  )
  {
    exists emitted: seq<nat> ::
      StrictlyIncreasing(emitted) &&
      (forall k :: 0 <= k < |emitted| ==> emitted[k] < |input|) &&
      (forall i :: 0 <= i < |input| ==>
                     (i in emitted) ==
                     SqueezeEmittedAt(
                       input, squeezeSet, hasPrevious, previous, i
                     )) &&
      |output| == |emitted| &&
      (forall k :: 0 <= k < |emitted| ==>
                     output[k] == input[emitted[k]])
  }

  ghost predicate SqueezeEmittedAt(
    input: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes,
    hasPrevious: bool,
    previous: char,
    i: nat
  )
    requires i < |input|
  {
    input[i] !in squeezeSet ||
    (if i == 0 then
       !hasPrevious || input[i] != previous
     else
       input[i] != input[i - 1])
  }

  ghost predicate SqueezeRelation(
    input: BenchWorld.Bytes,
    squeezeSet: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    SqueezeStateRelation(input, squeezeSet, false, '\0', output)
  }

  ghost predicate OutputRelation(
    cmd: TrCmd,
    input: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
  {
    exists transformed: BenchWorld.Bytes ::
      DeleteTranslateRelation(cmd, input, transformed) &&
      if cmd.squeeze then
        SqueezeRelation(transformed, cmd.squeezeSet, output)
      else
        output == transformed
  }

  twostate predicate Spec(raw: TrSchema.TrCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists cmd: TrCmd ::
      CommandRelation(raw, cmd) &&
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
      case ModeMissingOperand(message) =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + message &&
        exit == 1
      case ModeExtraOperand(operand) =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + ExtraOperandMessageSpec(operand) &&
        exit == 1
      case ModeUnsupportedSet(operand) =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + UnsupportedSetMessageSpec(operand) &&
        exit == 1
      case ModeEmptySet2 =>
        io.stdin() == old(io.stdin()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + EmptySet2MessageSpec() &&
        exit == 1
      case ModeRun =>
        io.stdin() == IOContract.AfterReadStdinFields(old(io.stdin())) &&
        (exists output: BenchWorld.Bytes ::
           OutputRelation(cmd, old(io.stdin()), output) &&
           io.stdout() == old(io.stdout()) + output) &&
        io.stderr() == old(io.stderr()) &&
        exit == 0
  }
}
