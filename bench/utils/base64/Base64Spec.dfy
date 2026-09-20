include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "Base64Schema.dfy"

module Base64Spec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = Base64Schema

  function HelpText(): BenchWorld.Bytes
  {
    "Usage: base64 [OPTION]... [FILE]...\n"
    + "Base64 encode or decode FILEs or standard input.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "  -d, --decode         decode data\n"
    + "  -i, --ignore-garbage  when decoding, ignore non-alphabet characters\n"
    + "  -w, --wrap=COLS      wrap encoded lines after COLS characters\n"
    + "      --help           display this help and exit\n"
    + "      --version        output version information and exit\n"
    + "\n"
    + "Benchmark note: this slice models the standard base64 alphabet only.\n"
    + "Other basenc alphabets and large bounded-memory stress tests are deferred.\n"
    + "\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/base64>\n"
    + "or available locally via: info '(coreutils) base64 invocation'\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "base64 (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Simon Josefsson.\n"
  }

  function InvalidWrapMessage(value: string): BenchWorld.Bytes
  {
    "base64: invalid wrap size: '" + value + "'\n"
  }

  function InvalidInputMessage(): BenchWorld.Bytes
  {
    "base64: invalid input\n"
  }

  function ExtraOperandMessage(operand: string): BenchWorld.Bytes
  {
    "base64: extra operand '" + operand + "'\nTry 'base64 --help' for more information.\n"
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

  function ErrorMessage(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    if err.IsDirectory? then
      "base64: read error: Is a directory\n"
    else
      Utf8.Encode("base64: " + path + ": " + ErrnoText(err) + "\n")
  }

  function Alphabet(index: nat): char
    requires index < 64
  {
    if index < 26 then
      (('A' as int) + index as int) as char
    else if index < 52 then
      (('a' as int) + (index - 26) as int) as char
    else if index < 62 then
      (('0' as int) + (index - 52) as int) as char
    else if index == 62 then
      '+'
    else
      '/'
  }

  function ByteValue(ch: char): nat
    ensures ByteValue(ch) < 256
  {
    ((ch as int) as nat) % 256
  }

  function ByteChar(value: nat): char
  {
    (value % 256) as char
  }

  function DecodeValue(ch: char): int
  {
    if 'A' <= ch <= 'Z' then
      (ch as int) - ('A' as int)
    else if 'a' <= ch <= 'z' then
      26 + (ch as int) - ('a' as int)
    else if '0' <= ch <= '9' then
      52 + (ch as int) - ('0' as int)
    else if ch == '+' then
      62
    else if ch == '/' then
      63
    else
      -1
  }

  function Valid64(ch: char): bool
  {
    DecodeValue(ch) >= 0
  }

  ghost predicate StrictlyIncreasing(indices: seq<nat>)
  {
    forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
  }

  ghost predicate KeptInputRelation(
    data: BenchWorld.Bytes,
    ignoreGarbage: bool,
    kept: BenchWorld.Bytes,
    indices: seq<nat>
  )
  {
    |indices| == |kept| &&
    StrictlyIncreasing(indices) &&
    (forall k :: 0 <= k < |indices| ==>
                   indices[k] < |data| && kept[k] == data[indices[k]]) &&
    (forall i :: 0 <= i < |data| ==>
                   ((i in indices) ==
                    (if ignoreGarbage
                     then Valid64(data[i]) || data[i] == '='
                     else data[i] != '\n')))
  }

  ghost predicate EncodeBlockRelation(
    data: BenchWorld.Bytes,
    encoded: BenchWorld.Bytes,
    block: nat
  )
    requires block < (|data| + 2) / 3
    requires |encoded| == 4 * ((|data| + 2) / 3)
  {
    var input := 3 * block;
    var output := 4 * block;
    var b0 := ByteValue(data[input]);
    encoded[output] == Alphabet(b0 / 4) &&
    encoded[output + 1] ==
    Alphabet(
      (b0 % 4) * 16 +
      (if input + 1 < |data| then ByteValue(data[input + 1]) / 16 else 0)
    ) &&
    encoded[output + 2] ==
    (if input + 1 < |data|
     then Alphabet(
               (ByteValue(data[input + 1]) % 16) * 4 +
               (if input + 2 < |data| then ByteValue(data[input + 2]) / 64 else 0)
             )
     else '=') &&
    encoded[output + 3] ==
    (if input + 2 < |data|
     then Alphabet(ByteValue(data[input + 2]) % 64)
     else '=')
  }

  ghost predicate EncodeRelation(
    data: BenchWorld.Bytes,
    encoded: BenchWorld.Bytes
  )
  {
    |encoded| == 4 * ((|data| + 2) / 3) &&
    forall block :: 0 <= block < (|data| + 2) / 3 ==>
                      EncodeBlockRelation(data, encoded, block)
  }

  ghost predicate WrappedWitnessRelation(
    encoded: BenchWorld.Bytes,
    width: nat,
    output: BenchWorld.Bytes,
    chunks: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
    requires width > 0
  {
    ((|encoded| == 0) == (|chunks| == 0)) &&
    (forall line {:trigger chunks[line]} ::
       0 <= line < |chunks| ==>
         var start := line * width;
         var end :=
           if (line + 1) * width < |encoded|
           then (line + 1) * width
           else |encoded|;
         start < |encoded| &&
         start < end <= |encoded| &&
         chunks[line] == encoded[start..end] + ['\n'] &&
         (line + 1 < |chunks| ==>
            (line + 1) * width < |encoded|) &&
         (line + 1 == |chunks| ==>
            (line + 1) * width >= |encoded|)) &&
    FragmentsConcatenate(chunks, output, cuts)
  }

  ghost predicate WrappedRelation(
    encoded: BenchWorld.Bytes,
    width: nat,
    output: BenchWorld.Bytes
  )
  {
    if width == 0 then
      output == encoded
    else
      exists chunks: seq<BenchWorld.Bytes>, cuts: seq<nat> ::
        WrappedWitnessRelation(
          encoded, width, output, chunks, cuts
        )
  }

  ghost predicate DecodeFullBlockRelation(
    data: BenchWorld.Bytes,
    start: nat,
    output: BenchWorld.Bytes
  )
    requires start + 4 <= |data|
  {
    var c0 := data[start];
    var c1 := data[start + 1];
    var c2 := data[start + 2];
    var c3 := data[start + 3];
    Valid64(c0) && Valid64(c1) &&
    ((Valid64(c2) && Valid64(c3) &&
      output == [
        ByteChar((DecodeValue(c0) * 4 + DecodeValue(c1) / 16) as nat),
        ByteChar((((DecodeValue(c1) % 16) * 16 + DecodeValue(c2) / 4) as nat)),
        ByteChar(((((DecodeValue(c2) % 4) * 64) + DecodeValue(c3)) as nat))
      ]) ||
     (c2 == '=' && c3 == '=' && DecodeValue(c1) % 16 == 0 &&
      output == [
        ByteChar((DecodeValue(c0) * 4 + DecodeValue(c1) / 16) as nat)
      ]) ||
     (Valid64(c2) && c3 == '=' && DecodeValue(c2) % 4 == 0 &&
      output == [
        ByteChar((DecodeValue(c0) * 4 + DecodeValue(c1) / 16) as nat),
        ByteChar((((DecodeValue(c1) % 16) * 16 + DecodeValue(c2) / 4) as nat))
      ]))
  }

  ghost predicate DecodeTerminalRelation(
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    ok: bool
  )
  {
    var remaining := |data|;
    (remaining >= 4 ==>
       !(exists fullOutput: BenchWorld.Bytes ::
           DecodeFullBlockRelation(data, 0, fullOutput))) &&
    if remaining == 0 then
      output == [] && ok
    else if remaining == 1 then
      output == [] && !ok
    else
      var c0 := data[0];
      var c1 := data[1];
      if !Valid64(c0) || !Valid64(c1) then
        output == [] && !ok
      else if remaining == 2 then
        output == [
          ByteChar((DecodeValue(c0) * 4 + DecodeValue(c1) / 16) as nat)
        ] &&
        (ok == (DecodeValue(c1) % 16 == 0))
      else
        var c2 := data[2];
        if c2 == '=' then
          output == [
            ByteChar((DecodeValue(c0) * 4 + DecodeValue(c1) / 16) as nat)
          ] &&
          !ok
        else if !Valid64(c2) then
          output == [] && !ok
        else if remaining == 3 then
          output == [
            ByteChar((DecodeValue(c0) * 4 + DecodeValue(c1) / 16) as nat),
            ByteChar((((DecodeValue(c1) % 16) * 16 + DecodeValue(c2) / 4) as nat))
          ] &&
          (ok == (DecodeValue(c2) % 4 == 0))
        else
          var c3 := data[3];
          if c3 == '=' then
            output == [
              ByteChar((DecodeValue(c0) * 4 + DecodeValue(c1) / 16) as nat),
              ByteChar((((DecodeValue(c1) % 16) * 16 + DecodeValue(c2) / 4) as nat))
            ] &&
            !ok
          else
            output == [] && !ok
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

  ghost predicate DecodeWitnessRelation(
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    ok: bool,
    blocks: nat,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
  {
    4 * blocks <= |data| &&
    |fragments| == blocks + 1 &&
    (forall block :: 0 <= block < blocks ==>
                       DecodeFullBlockRelation(data, 4 * block, fragments[block])) &&
    DecodeTerminalRelation(
      data[4 * blocks..], fragments[blocks], ok
    ) &&
    FragmentsConcatenate(fragments, output, cuts)
  }

  ghost predicate DecodeRelation(
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    ok: bool
  )
  {
    exists blocks: nat,
      fragments: seq<BenchWorld.Bytes>,
      cuts: seq<nat> ::
      DecodeWitnessRelation(data, output, ok, blocks, fragments, cuts)
  }

  ghost predicate TransformRelation(
    cmd: Schema.Base64Cmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    ok: bool
  )
  {
    if cmd.decode then
      exists kept: BenchWorld.Bytes, indices: seq<nat> ::
        KeptInputRelation(data, cmd.ignoreGarbage, kept, indices) &&
        DecodeRelation(kept, output, ok)
    else
      exists encoded: BenchWorld.Bytes ::
        EncodeRelation(data, encoded) &&
        WrappedRelation(encoded, cmd.wrapWidth, output) &&
        ok
  }

  ghost predicate DecimalValueFromRelation(
    text: string,
    i: nat,
    acc: nat,
    value: nat
  )
    requires i <= |text|
    decreases |text| - i
  {
    if i == |text| then
      value == acc
    else
      '0' <= text[i] <= '9' &&
      DecimalValueFromRelation(
        text,
        i + 1,
        acc * 10 +
        (((text[i] as int) - ('0' as int)) as nat),
        value
      )
  }

  ghost predicate DecimalValueRelation(text: string, value: nat)
  {
    |text| > 0 &&
    DecimalValueFromRelation(text, 0, 0, value)
  }

  ghost predicate FirstInvalidWrap(
    args: seq<Schema.WidthArg>,
    i: nat
  )
    decreases |args|
  {
    i < |args| &&
    if i == 0 then
      !(exists value: nat ::
          DecimalValueRelation(args[0].text, value))
    else
      exists value: nat ::
        DecimalValueRelation(args[0].text, value) &&
        FirstInvalidWrap(args[1..], i - 1)
  }

  ghost predicate AllWrapsValid(args: seq<Schema.WidthArg>)
    decreases |args|
  {
    |args| == 0 ||
    exists value: nat ::
      DecimalValueRelation(args[0].text, value) &&
      AllWrapsValid(args[1..])
  }

  ghost predicate InputsRelation(
    operands: seq<string>,
    inputs: seq<Schema.Input>
  )
  {
    if |operands| == 0 then
      |inputs| == 0
    else
      |inputs| > 0 &&
      inputs[0] ==
      (if operands[0] == "-"
       then Schema.Stdin
       else Schema.File(operands[0])) &&
      InputsRelation(operands[1..], inputs[1..])
  }

  ghost predicate RunInputsRelation(
    operands: seq<string>,
    inputs: seq<Schema.Input>
  )
  {
    if |operands| == 0 then
      inputs == [Schema.Stdin]
    else
      InputsRelation(operands, inputs)
  }

  ghost predicate HelpSelected(raw: Schema.Base64CmdRaw)
  {
    raw.seenHelp &&
    (!raw.seenVersion ||
     raw.helpTokenIndex <= raw.versionTokenIndex) &&
    forall i: nat | FirstInvalidWrap(raw.wrapArgs, i) ::
      raw.helpTokenIndex <= raw.wrapArgs[i].tokenIndex
  }

  ghost predicate VersionSelected(raw: Schema.Base64CmdRaw)
  {
    raw.seenVersion &&
    forall i: nat | FirstInvalidWrap(raw.wrapArgs, i) ::
      raw.versionTokenIndex <= raw.wrapArgs[i].tokenIndex
  }

  ghost predicate RunOrExtraAtWidth(
    raw: Schema.Base64CmdRaw,
    width: nat,
    cmd: Schema.Base64Cmd
  )
  {
    if |raw.operands| > 1 then
      cmd == Schema.Base64Cmd(
        Schema.ModeExtraOperand(raw.operands[1]),
        raw.seenDecode,
        false,
        width,
        "",
        []
      )
    else
      exists inputs: seq<Schema.Input> ::
        RunInputsRelation(raw.operands, inputs) &&
        cmd == Schema.Base64Cmd(
          Schema.ModeRun,
          raw.seenDecode,
          raw.seenIgnoreGarbage,
          width,
          "",
          inputs
        )
  }

  ghost predicate CommandRelation(
    raw: Schema.Base64CmdRaw,
    cmd: Schema.Base64Cmd
  )
  {
    if HelpSelected(raw) then
      cmd == Schema.Base64Cmd(
        Schema.ModeHelp,
        raw.seenDecode,
        false,
        76,
        "",
        []
      )
    else if VersionSelected(raw) then
      cmd == Schema.Base64Cmd(
        Schema.ModeVersion,
        raw.seenDecode,
        false,
        76,
        "",
        []
      )
    else if |raw.wrapArgs| == 0 then
      RunOrExtraAtWidth(raw, 76, cmd)
    else if exists i: nat ::
              FirstInvalidWrap(raw.wrapArgs, i) then
      exists i: nat ::
        FirstInvalidWrap(raw.wrapArgs, i) &&
        cmd == Schema.Base64Cmd(
          Schema.ModeInvalidWrap,
          raw.seenDecode,
          false,
          76,
          raw.wrapArgs[i].text,
          []
        )
    else
      exists width: nat ::
        AllWrapsValid(raw.wrapArgs) &&
        DecimalValueRelation(
          raw.wrapArgs[|raw.wrapArgs| - 1].text,
          width
        ) &&
        RunOrExtraAtWidth(raw, width, cmd)
  }

  twostate predicate InputTraceRelation(
    cmd: Schema.Base64Cmd,
    io: BenchIO.IO,
    data: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadReadError: bool
  )
    reads io.Footprint()
  {
    |cmd.inputs| == 1 &&
    match cmd.inputs[0]
    case Stdin =>
      data == old(io.stdin()) &&
      errorOutput == [] &&
      !hadReadError
    case File(path) =>
      match IOContract.ReadFileResultFields(old(io.fs()), path)
      case Ok(fileData) =>
        data == fileData &&
        errorOutput == [] &&
        !hadReadError
      case Err(err) =>
        data == [] &&
        errorOutput == ErrorMessage(path, err) &&
        hadReadError
  }

  twostate predicate Spec(raw: Schema.Base64CmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists cmd: Schema.Base64Cmd ::
      CommandRelation(raw, cmd) &&
      (if cmd.mode == Schema.ModeHelp then
         io.stdin() == old(io.stdin()) &&
         io.stdout() == old(io.stdout()) + HelpText() &&
         io.stderr() == old(io.stderr()) &&
         exit == 0
       else if cmd.mode == Schema.ModeVersion then
         io.stdin() == old(io.stdin()) &&
         io.stdout() == old(io.stdout()) + VersionText() &&
         io.stderr() == old(io.stderr()) &&
         exit == 0
       else if cmd.mode == Schema.ModeInvalidWrap then
         io.stdin() == old(io.stdin()) &&
         io.stdout() == old(io.stdout()) &&
         io.stderr() ==
         old(io.stderr()) +
         InvalidWrapMessage(cmd.invalidWrapValue) &&
         exit == 1
       else if cmd.mode != Schema.ModeRun then
         match cmd.mode
         case ModeExtraOperand(operand) =>
           io.stdin() == old(io.stdin()) &&
           io.stdout() == old(io.stdout()) &&
           io.stderr() ==
           old(io.stderr()) + ExtraOperandMessage(operand) &&
           exit == 1
         case _ =>
           false
       else
         exists data: BenchWorld.Bytes,
           errorOutput: BenchWorld.Bytes,
           hadReadError: bool,
           output: BenchWorld.Bytes,
           ok: bool ::
           InputTraceRelation(
             cmd, io, data, errorOutput, hadReadError
           ) &&
           TransformRelation(
             cmd, data, output, ok
           ) &&
           io.stdin() ==
           (if cmd.inputs[0].Stdin?
            then []
            else old(io.stdin())) &&
           io.stdout() == old(io.stdout()) + output &&
           io.stderr() ==
           old(io.stderr()) + errorOutput +
           (if ok then [] else InvalidInputMessage()) &&
           exit ==
           (if hadReadError || !ok
            then 1
            else 0))
  }
}
