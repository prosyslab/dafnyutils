include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "CatQuoteSpec.dfy"
include "CatSchema.dfy"

module CatSpec {
  import BenchIO
  import BenchWorld
  import IOContract
  import Utf8 = Utf8Semantics
  import Quote = CatQuoteSpec
  import CatSchema




  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: cat [OPTION]... [FILE]...\n"
    + "Concatenate FILE(s) to standard output.\n"
    + "\n"
    + "With no FILE, or when FILE is -, read standard input.\n"
    + "  -A, --show-all           equivalent to -vET\n"
    + "  -b, --number-nonblank    number nonempty output lines, overrides -n\n"
    + "  -e                       equivalent to -vE\n"
    + "  -E, --show-ends          display $ or ^M$ at end of each line\n"
    + "  -n, --number             number all output lines\n"
    + "  -s, --squeeze-blank      suppress repeated empty output lines\n"
    + "  -t                       equivalent to -vT\n"
    + "  -T, --show-tabs          display TAB characters as ^I\n"
    + "  -u                       (ignored)\n"
    + "  -v, --show-nonprinting   use ^ and M- notation, except for LFD and TAB\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Examples:\n"
    + "  cat f - g  Output f's contents, then standard input, then g's contents.\n"
    + "  cat        Copy standard input to standard output.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/cat>\n"
    + "or available locally via: info '(coreutils) cat invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    Utf8.Encode("cat (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Torbjorn Granlund and Richard M. Stallman.\n")
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
    "cat: " + Quote.SpecQuoteFBytes(Utf8.Encode(path)) + ": " + Utf8.Encode(ErrnoText(err)) + "\n"
  }

  function InputsFromOperands(operands: seq<string>): seq<CatSchema.Input>
  {
    if |operands| == 0 then
      []
    else
      [(if operands[0] == "-" then CatSchema.Stdin else CatSchema.File(operands[0]))] + InputsFromOperands(operands[1..])
  }

  function Command(raw: CatSchema.CatCmdRaw): CatSchema.CatCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        CatSchema.ModeHelp
      else if raw.seenVersion then
        CatSchema.ModeVersion
      else
        CatSchema.ModeRun;
    var number :=
      if raw.seenB then CatSchema.NumberNonBlank
      else if raw.seenN then CatSchema.NumberAll
      else CatSchema.NoNumber;
    var inputs := InputsFromOperands(raw.operands);
    var runInputs := if mode == CatSchema.ModeRun && |inputs| == 0 then [CatSchema.Stdin] else inputs;
    CatSchema.CatCmd(
      mode,
      number,
      raw.seenS,
      raw.seenA || raw.seenE || raw.seenShowEnds,
      raw.seenA || raw.seenT || raw.seenShowTabs,
      raw.seenA || raw.seenE || raw.seenT || raw.seenV,
      runInputs
    )
  }

  function DigitChar(d: int): BenchWorld.RawByte
  {
    if 0 <= d < 10 then
      (d + ('0' as int)) as char
    else
      '0'
  }

  function Digits(n: int): BenchWorld.Bytes
    decreases n
  {
    if n < 10 then
      [DigitChar(n)]
    else
      Digits(n / 10) + [DigitChar(n % 10)]
  }

  function PadLeft(text: BenchWorld.Bytes, width: int): BenchWorld.Bytes
    decreases width - |text|
  {
    if |text| >= width then
      text
    else
      PadLeft([' '] + text, width)
  }

  function LineNumberText(n: int): BenchWorld.Bytes
  {
    PadLeft(Digits(n), 6) + ['\t']
  }

  function ShowNonPrintingChar(ch: BenchWorld.RawByte, showTabs: bool): BenchWorld.Bytes
  {
    var code := ch as int;
    if code >= 32 then
      if code < 127 then
        [ch]
      else if code == 127 then
        ['^', '?']
      else
        var base := code - 128;
        if base >= 32 then
          if base < 127 then
            ['M', '-', (base as char)]
          else
            ['M', '-', '^', '?']
        else
          ['M', '-', '^', ((base + 64) as char)]
    else if ch == '\t' && !showTabs then
      ['\t']
    else
      ['^', ((code + 64) as char)]
  }

  function TransformChar(cmd: CatSchema.CatCmd, ch: BenchWorld.RawByte, nextIsNewline: bool): BenchWorld.Bytes
  {
    if cmd.showNonPrinting then
      ShowNonPrintingChar(ch, cmd.showTabs)
    else if ch == '\t' && cmd.showTabs then
      ['^', ((ch as int) + 64) as char]
    else if ch == '\r' && cmd.showEnds && nextIsNewline then
      ['^', 'M']
    else
      [ch]
  }

  ghost predicate LineStartAt(data: BenchWorld.Bytes, p: nat)
    requires p < |data|
  {
    p == 0 || data[p - 1] == '\n'
  }

  ghost predicate KeptAt(cmd: CatSchema.CatCmd, data: BenchWorld.Bytes, p: nat)
    requires p < |data|
  {
    !(cmd.squeezeBlank &&
      data[p] == '\n' &&
      LineStartAt(data, p) &&
      0 < p &&
      (p == 1 || data[p - 2] == '\n'))
  }

  ghost predicate NumberedAt(cmd: CatSchema.CatCmd, data: BenchWorld.Bytes, p: nat)
    requires p < |data|
  {
    KeptAt(cmd, data, p) &&
    LineStartAt(data, p) &&
    (cmd.number == CatSchema.NumberAll ||
     (cmd.number == CatSchema.NumberNonBlank && data[p] != '\n'))
  }

  ghost function RenderFragment(
    cmd: CatSchema.CatCmd,
    data: BenchWorld.Bytes,
    p: nat,
    number: nat
  ): BenchWorld.Bytes
    requires p < |data|
  {
    if !KeptAt(cmd, data, p) then
      []
    else if data[p] == '\n' then
      (if NumberedAt(cmd, data, p) then
         LineNumberText(number as int)
       else
         []) +
      (if cmd.showEnds then ['$'] else []) +
      ['\n']
    else
      (if NumberedAt(cmd, data, p) then
         LineNumberText(number as int)
       else
         []) +
      TransformChar(
        cmd,
        data[p],
        p + 1 < |data| && data[p + 1] == '\n'
      )
  }

  ghost predicate LineNumberRelation(
    cmd: CatSchema.CatCmd,
    data: BenchWorld.Bytes,
    numbers: seq<nat>
  )
  {
    |numbers| == |data| &&
    forall p: nat | p < |data| ::
      numbers[p] ==
      (if NumberedAt(cmd, data, p) then
         1 + |set q: nat | q < p && NumberedAt(cmd, data, q)|
       else
         0)
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

  ghost predicate RenderRelation(
    cmd: CatSchema.CatCmd,
    data: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>,
    numbers: seq<nat>
  )
  {
    LineNumberRelation(cmd, data, numbers) &&
    |fragments| == |data| &&
    (forall p: nat | p < |data| ::
       fragments[p] == RenderFragment(cmd, data, p, numbers[p])) &&
    FragmentsConcatenate(fragments, output, cuts)
  }

  ghost predicate ReadResultRelation(
    cmd: CatSchema.CatCmd,
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
        if CatSchema.Stdin in cmd.inputs[..i]
        then []
        else preStdin
      )
    case File(path) =>
      result == IOContract.ReadFileResultFields(preFs, path)
  }

  ghost function InputDataPiece(
    result: BenchWorld.Result<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match result
    case Ok(data) => data
    case Err(_) => []
  }

  ghost function InputErrorPiece(
    input: CatSchema.Input,
    result: BenchWorld.Result<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match input
    case Stdin => []
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => ErrorMessageSpec(path, err)
  }

  ghost predicate InputFailed(
    input: CatSchema.Input,
    result: BenchWorld.Result<BenchWorld.Bytes>
  )
  {
    input.File? && result.Err?
  }

  ghost predicate InputTraceRelation(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    data: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool,
    readResults: seq<BenchWorld.Result<BenchWorld.Bytes>>,
    dataFragments: seq<BenchWorld.Bytes>,
    dataCuts: seq<nat>,
    errorFragments: seq<BenchWorld.Bytes>,
    errorCuts: seq<nat>
  )
  {
    |readResults| == |cmd.inputs| &&
    |dataFragments| == |cmd.inputs| &&
    |errorFragments| == |cmd.inputs| &&
    (forall i: nat | i < |cmd.inputs| ::
       ReadResultRelation(cmd, preFs, preStdin, i, readResults[i]) &&
       dataFragments[i] == InputDataPiece(readResults[i]) &&
       errorFragments[i] == InputErrorPiece(cmd.inputs[i], readResults[i])) &&
    FragmentsConcatenate(dataFragments, data, dataCuts) &&
    FragmentsConcatenate(errorFragments, errors, errorCuts) &&
    postStdin ==
    (if CatSchema.Stdin in cmd.inputs
     then []
     else preStdin) &&
    hadError ==
    (exists i: nat ::
       i < |cmd.inputs| && InputFailed(cmd.inputs[i], readResults[i]))
  }

  lemma EmptyInputWitnesses(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes
  )
    requires forall i: nat | i < |cmd.inputs| ::
      ReadResultRelation(cmd, preFs, preStdin, i, BenchWorld.Ok([]))
    ensures InputTraceRelation(
      cmd, preFs, preStdin,
      if CatSchema.Stdin in cmd.inputs then [] else preStdin,
      [], [], false,
      seq(|cmd.inputs|, i => BenchWorld.Ok([])),
      seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0),
      seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0))
    ensures RenderRelation(cmd, [], [], [], [0], [])
  {
    var results: seq<BenchWorld.Result<BenchWorld.Bytes>> :=
      seq(|cmd.inputs|, i => BenchWorld.Ok([]));
    forall i: nat | i < |cmd.inputs|
      ensures ReadResultRelation(cmd, preFs, preStdin, i, results[i])
      ensures InputDataPiece(results[i]) == []
      ensures InputErrorPiece(cmd.inputs[i], results[i]) == []
      ensures !InputFailed(cmd.inputs[i], results[i])
    {
    }
  }

  ghost predicate PlainStdinCommand(cmd: CatSchema.CatCmd)
  {
    cmd.number == CatSchema.NoNumber && !cmd.squeezeBlank &&
    !cmd.showEnds && !cmd.showTabs && !cmd.showNonPrinting &&
    |cmd.inputs| > 0 && forall i: nat | i < |cmd.inputs| :: cmd.inputs[i] == CatSchema.Stdin
  }

  lemma PlainStdinWitnesses(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem,
    data: BenchWorld.Bytes
  )
    requires PlainStdinCommand(cmd)
    ensures InputTraceRelation(cmd, preFs, data, [], data, [], false,
      seq(|cmd.inputs|, i => BenchWorld.Ok(if i == 0 then data else [])),
      seq(|cmd.inputs|, i => if i == 0 then data else []),
      seq(|cmd.inputs| + 1, i => if i == 0 then 0 else |data|),
      seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0))
    ensures RenderRelation(cmd, data, data,
      seq(|data|, i requires 0 <= i < |data| => [data[i]]),
      seq(|data| + 1, i => i), seq(|data|, i => 0))
  {
    forall i: nat {:trigger cmd.inputs[i]} | i < |cmd.inputs|
      ensures ReadResultRelation(cmd, preFs, data, i,
        BenchWorld.Ok(if i == 0 then data else []))
    {
      if i > 0 { assert cmd.inputs[0] == CatSchema.Stdin; }
    }
    forall p: nat | p < |data|
      ensures !NumberedAt(cmd, data, p)
      ensures RenderFragment(cmd, data, p, 0) == [data[p]]
      ensures data[p..p + 1] == [data[p]]
    {
    }
  }

  lemma SingleFragmentCuts(
    fragments: seq<BenchWorld.Bytes>, combined: BenchWorld.Bytes,
    cuts: seq<nat>, i: nat
  )
    requires FragmentsConcatenate(fragments, combined, cuts)
    requires 0 < |fragments|
    requires forall j: nat | 0 < j < |fragments| :: fragments[j] == []
    requires i <= |fragments|
    ensures cuts[i] == (if i == 0 then 0 else |fragments[0]|)
    decreases i
  {
    if i > 1 { SingleFragmentCuts(fragments, combined, cuts, i - 1); }
  }

  lemma UnitFragmentCuts(
    fragments: seq<BenchWorld.Bytes>, combined: BenchWorld.Bytes,
    cuts: seq<nat>, i: nat
  )
    requires FragmentsConcatenate(fragments, combined, cuts)
    requires forall j: nat | j < |fragments| :: |fragments[j]| == 1
    requires i <= |fragments|
    ensures cuts[i] == i
    decreases i
  {
    if i > 0 { UnitFragmentCuts(fragments, combined, cuts, i - 1); }
  }

  lemma PlainStdinTraceIdentity(
    cmd: CatSchema.CatCmd, preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes, postStdin: BenchWorld.Bytes,
    data: BenchWorld.Bytes, errors: BenchWorld.Bytes, hadError: bool,
    readResults: seq<BenchWorld.Result<BenchWorld.Bytes>>,
    dataFragments: seq<BenchWorld.Bytes>, dataCuts: seq<nat>,
    errorFragments: seq<BenchWorld.Bytes>, errorCuts: seq<nat>
  )
    requires PlainStdinCommand(cmd)
    requires InputTraceRelation(cmd, preFs, preStdin, postStdin, data, errors,
      hadError, readResults, dataFragments, dataCuts, errorFragments, errorCuts)
    ensures postStdin == [] && data == preStdin && errors == [] && !hadError
  {
    forall i: nat | i < |cmd.inputs|
      ensures readResults[i] == BenchWorld.Ok(if i == 0 then preStdin else [])
      ensures dataFragments[i] == (if i == 0 then preStdin else [])
      ensures errorFragments[i] == []
      ensures !InputFailed(cmd.inputs[i], readResults[i])
    {
      if i > 0 { assert cmd.inputs[0] == CatSchema.Stdin; }
    }
    SingleFragmentCuts(dataFragments, data, dataCuts, |dataFragments|);
    SingleFragmentCuts(errorFragments, errors, errorCuts, |errorFragments|);
    assert data[0..|preStdin|] == preStdin;
  }

  lemma PlainRenderIdentity(
    cmd: CatSchema.CatCmd, data: BenchWorld.Bytes, output: BenchWorld.Bytes,
    fragments: seq<BenchWorld.Bytes>, cuts: seq<nat>, numbers: seq<nat>
  )
    requires PlainStdinCommand(cmd)
    requires RenderRelation(cmd, data, output, fragments, cuts, numbers)
    ensures output == data
  {
    forall p: nat | p < |data|
      ensures fragments[p] == [data[p]]
    {
    }
    forall i: nat | i <= |fragments|
      ensures cuts[i] == i
    {
      UnitFragmentCuts(fragments, output, cuts, i);
    }
    assert |output| == |data|;
    forall p: nat | p < |data|
      ensures output[p] == data[p]
    {
      assert cuts[p] == p && cuts[p + 1] == p + 1;
      assert output[cuts[p]..cuts[p + 1]] == fragments[p];
      assert output[p..p + 1] == [data[p]];
    }
  }

  ghost predicate RunRelation(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    exit: int
  )
    ensures
      (forall i: nat | i < |cmd.inputs| ::
        ReadResultRelation(cmd, preFs, preStdin, i, BenchWorld.Ok([]))) &&
      postStdin == (if CatSchema.Stdin in cmd.inputs then [] else preStdin) &&
      output == [] && errors == [] && exit == 0 ==>
      RunRelation(cmd, preFs, preStdin, postStdin, output, errors, exit)
    ensures (PlainStdinCommand(cmd) && postStdin == [] && output == preStdin &&
      errors == [] && exit == 0) ==>
      RunRelation(cmd, preFs, preStdin, postStdin, output, errors, exit)
    ensures (PlainStdinCommand(cmd) &&
      RunRelation(cmd, preFs, preStdin, postStdin, output, errors, exit)) ==>
      postStdin == [] && output == preStdin && errors == [] && exit == 0
  {
    assert PlainStdinCommand(cmd) ==>
      InputTraceRelation(cmd, preFs, preStdin, [], preStdin, [], false,
        seq(|cmd.inputs|, i => BenchWorld.Ok(if i == 0 then preStdin else [])),
        seq(|cmd.inputs|, i => if i == 0 then preStdin else []),
        seq(|cmd.inputs| + 1, i => if i == 0 then 0 else |preStdin|),
        seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0)) &&
      RenderRelation(cmd, preStdin, preStdin,
        seq(|preStdin|, i requires 0 <= i < |preStdin| => [preStdin[i]]),
        seq(|preStdin| + 1, i => i), seq(|preStdin|, i => 0)) by {
      if PlainStdinCommand(cmd) { PlainStdinWitnesses(cmd, preFs, preStdin); }
    }
    assert (forall i: nat | i < |cmd.inputs| ::
      ReadResultRelation(cmd, preFs, preStdin, i, BenchWorld.Ok([]))) ==>
      InputTraceRelation(
        cmd, preFs, preStdin,
        if CatSchema.Stdin in cmd.inputs then [] else preStdin,
        [], [], false,
        seq(|cmd.inputs|, i => BenchWorld.Ok([])),
        seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0),
        seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0)) &&
      RenderRelation(cmd, [], [], [], [0], []) by {
      if forall i: nat | i < |cmd.inputs| ::
          ReadResultRelation(cmd, preFs, preStdin, i, BenchWorld.Ok([])) {
        EmptyInputWitnesses(cmd, preFs, preStdin);
      }
    }
    var valid := exists readResults: seq<BenchWorld.Result<BenchWorld.Bytes>>,
      data: BenchWorld.Bytes,
      dataFragments: seq<BenchWorld.Bytes>,
      dataCuts: seq<nat>,
      errorFragments: seq<BenchWorld.Bytes>,
      errorCuts: seq<nat>,
      hadError: bool,
      byteFragments: seq<BenchWorld.Bytes>,
      outputCuts: seq<nat>,
      numbers: seq<nat> ::
      InputTraceRelation(
        cmd,
        preFs,
        preStdin,
        postStdin,
        data,
        errors,
        hadError,
        readResults,
        dataFragments,
        dataCuts,
        errorFragments,
        errorCuts
      ) &&
      RenderRelation(
        cmd,
        data,
        output,
        byteFragments,
        outputCuts,
        numbers
      ) &&
      exit == (if hadError then 1 else 0);
    assert (PlainStdinCommand(cmd) && valid) ==>
      postStdin == [] && output == preStdin && errors == [] && exit == 0 by {
      if PlainStdinCommand(cmd) && valid {
        var readResults: seq<BenchWorld.Result<BenchWorld.Bytes>>,
            data: BenchWorld.Bytes, dataFragments: seq<BenchWorld.Bytes>,
            dataCuts: seq<nat>, errorFragments: seq<BenchWorld.Bytes>,
            errorCuts: seq<nat>, hadError: bool,
            byteFragments: seq<BenchWorld.Bytes>, outputCuts: seq<nat>,
            numbers: seq<nat> :|
          InputTraceRelation(cmd, preFs, preStdin, postStdin, data, errors,
            hadError, readResults, dataFragments, dataCuts, errorFragments, errorCuts) &&
          RenderRelation(cmd, data, output, byteFragments, outputCuts, numbers) &&
          exit == (if hadError then 1 else 0);
        PlainStdinTraceIdentity(cmd, preFs, preStdin, postStdin, data, errors,
          hadError, readResults, dataFragments, dataCuts, errorFragments, errorCuts);
        PlainRenderIdentity(cmd, data, output, byteFragments, outputCuts, numbers);
      }
    }
    valid
  }

  twostate predicate Spec(raw: CatSchema.CatCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
    ensures
      Command(raw).mode == CatSchema.ModeRun &&
      (forall i: nat | i < |Command(raw).inputs| ::
        ReadResultRelation(Command(raw), old(io.fs()), old(io.stdin()), i, BenchWorld.Ok([]))) &&
      io.stdin() == (if CatSchema.Stdin in Command(raw).inputs then [] else old(io.stdin())) &&
      io.stdout() == old(io.stdout()) && io.stderr() == old(io.stderr()) && exit == 0 ==>
      Spec(raw, io, exit)
    ensures (Command(raw).mode == CatSchema.ModeRun && PlainStdinCommand(Command(raw)) &&
      io.stdin() == [] && io.stdout() == old(io.stdout()) + old(io.stdin()) &&
      io.stderr() == old(io.stderr()) && exit == 0) ==> Spec(raw, io, exit)
    ensures (Command(raw).mode == CatSchema.ModeRun && PlainStdinCommand(Command(raw)) &&
      Spec(raw, io, exit)) ==> (io.stdin() == [] &&
      io.stdout() == old(io.stdout()) + old(io.stdin()) &&
      io.stderr() == old(io.stderr()) && exit == 0)
  {
    var cmd := Command(raw);
    assert PlainStdinCommand(cmd) ==>
      RunRelation(cmd, old(io.fs()), old(io.stdin()), [], old(io.stdin()), [], 0);
    assert
      (forall i: nat | i < |cmd.inputs| ::
        ReadResultRelation(cmd, old(io.fs()), old(io.stdin()), i, BenchWorld.Ok([]))) ==>
      RunRelation(cmd, old(io.fs()), old(io.stdin()),
        if CatSchema.Stdin in cmd.inputs then [] else old(io.stdin()), [], [], 0);
    if cmd.mode == CatSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == CatSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      exists output: BenchWorld.Bytes, errors: BenchWorld.Bytes ::
        RunRelation(
          cmd,
          old(io.fs()),
          old(io.stdin()),
          io.stdin(),
          output,
          errors,
          exit
        ) &&
        io.stdout() == old(io.stdout()) + output &&
        io.stderr() == old(io.stderr()) + errors
  }
}
