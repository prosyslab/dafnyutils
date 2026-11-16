include "../../../core/StringEscaping.dfy"
include "../../../core/World.dfy"
include "../../../core/Utf8.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "CatSchema.dfy"

module CatSpec {
  import StreamContract = IOContract
  import StreamUtf8 = Utf8Semantics

  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import Utf8 = Utf8Semantics
  import Quote = StringEscaping
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
    Utf8.Encode(VersionTextValue())
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
    case ReadFailure(_, message, _, _) => message
    case NativeFailure(_, message) => message
    case WriteFailure(_, message, _, _) => message
    case StreamFailure(_, message, _, _) => message
    case TimeParseFailure(message, _, _) => message
  }

  function ErrorMessageSpec(path: BenchWorld.Path, err: BenchWorld.IOError): BenchWorld.Bytes
  {
    ErrorPrefix() + Quote.SpecQuoteFBytes(Utf8.Encode(path)) + ErrorSeparator() +
    Utf8.Encode(ErrnoText(err)) + DiagnosticSuffix()
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

  predicate LineStartAt(data: BenchWorld.Bytes, p: nat)
    requires p < |data|
  {
    p == 0 || data[p - 1] == '\n'
  }

  predicate KeptAt(cmd: CatSchema.CatCmd, data: BenchWorld.Bytes, p: nat)
    requires p < |data|
  {
    !(cmd.squeezeBlank &&
      data[p] == '\n' &&
      LineStartAt(data, p) &&
      0 < p &&
      (p == 1 || data[p - 2] == '\n'))
  }

  predicate NumberedAt(cmd: CatSchema.CatCmd, data: BenchWorld.Bytes, p: nat)
    requires p < |data|
  {
    KeptAt(cmd, data, p) &&
    LineStartAt(data, p) &&
    (cmd.number == CatSchema.NumberAll ||
     (cmd.number == CatSchema.NumberNonBlank && data[p] != '\n'))
  }

  function RenderFragment(
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

  ghost predicate CompleteReadResultRelation(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    i: nat,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  )
    requires i < |cmd.inputs|
  {
    match cmd.inputs[i]
    case Stdin =>
      result == Result.Ok(
        if CatSchema.Stdin in cmd.inputs[..i]
        then []
        else preStdin
      )
    case File(path) =>
      result == IOContract.ObservedReadFileResultFields(preFs, preStreams, path)
  }

  function InputDataPiece(
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match result
    case Ok(data) => data
    case Err(error) => IOContract.ReadResultData(result)
  }

  function InputErrorPiece(
    input: CatSchema.Input,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  ): BenchWorld.Bytes
  {
    match input
    case Stdin => if result.Err? then ErrorMessageSpec("-", result.e) else []
    case File(path) =>
      match result
      case Ok(_) => []
      case Err(err) => ErrorMessageSpec(path, err)
  }

  predicate InputFailed(
    input: CatSchema.Input,
    result: BenchWorld.IOResult<BenchWorld.Bytes>
  )
  {
    result.Err?
  }

  ghost predicate NormalStdinObservations(before: BenchWorld.Bytes,
                                          observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult)
  {
    IOContract.ObservedReadStdinResultFields(before, observations) == Result.Ok(before) &&
    IOContract.ObservedReadStdinRemainingFields(before, observations) == [] &&
    IOContract.ObservedReadStdinResultFields([], observations) == Result.Ok([]) &&
    IOContract.ObservedReadStdinRemainingFields([], observations) == []
  }

  ghost predicate InputReadOutcomeRelation(cmd: CatSchema.CatCmd,
                                           preFs: BenchWorld.FileSystem,
                                           observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                           before: BenchWorld.Bytes, index: nat, result: BenchWorld.IOResult<BenchWorld.Bytes>)
    requires index < |cmd.inputs|
  {
    result == (if cmd.inputs[index].Stdin? then IOContract.ObservedReadStdinResultFields(before, observations)
               else IOContract.ObservedReadFileResultFields(preFs, observations, cmd.inputs[index].path))
  }

  ghost predicate StdinTraceRelation(cmd: CatSchema.CatCmd, before: BenchWorld.Bytes,
                                     after: BenchWorld.Bytes, observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                     states: seq<BenchWorld.Bytes>)
  {
    |states| == |cmd.inputs| + 1 && states[0] == before && states[|cmd.inputs|] == after &&
    forall i: nat | i < |cmd.inputs| ::
      states[i + 1] == (if cmd.inputs[i].Stdin? then
                          IOContract.ObservedReadStdinRemainingFields(states[i], observations) else states[i])
  }

  lemma StdinStatePrefixFunctional(cmd: CatSchema.CatCmd, before: BenchWorld.Bytes,
                                   observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                                   first: seq<BenchWorld.Bytes>, second: seq<BenchWorld.Bytes>, index: nat)
    requires |first| == |cmd.inputs| + 1 && |second| == |cmd.inputs| + 1
    requires StdinTraceRelation(cmd, before, first[|cmd.inputs|], observations, first)
    requires StdinTraceRelation(cmd, before, second[|cmd.inputs|], observations, second)
    requires index <= |cmd.inputs|
    ensures first[index] == second[index]
    decreases index
  {
    if index > 0 { StdinStatePrefixFunctional(cmd, before, observations, first, second, index - 1); }
  }

  // Check the initializer's domain outside the IO-heavy lemma context.
  ghost function CompleteStdinStates(inputs: seq<CatSchema.Input>, before: BenchWorld.Bytes): seq<BenchWorld.Bytes>
  {
    seq(|inputs| + 1, i requires 0 <= i <= |inputs| => if CatSchema.Stdin in inputs[..i] then [] else before)
  }

  lemma CompleteStdinTrace(cmd: CatSchema.CatCmd, preFs: BenchWorld.FileSystem,
                           observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
                           before: BenchWorld.Bytes, results: seq<BenchWorld.IOResult<BenchWorld.Bytes>>)
    requires NormalStdinObservations(before, observations)
    requires |results| == |cmd.inputs|
    requires forall i: nat | i < |cmd.inputs| :: CompleteReadResultRelation(cmd, preFs, observations, before, i, results[i])
    ensures StdinTraceRelation(cmd, before, if CatSchema.Stdin in cmd.inputs then [] else before, observations,
                               CompleteStdinStates(cmd.inputs, before))
    ensures forall i: nat | i < |cmd.inputs| :: InputReadOutcomeRelation(cmd, preFs, observations,
                                                                         if CatSchema.Stdin in cmd.inputs[..i] then [] else before, i, results[i])
  {
    hide IOContract.ObservedReadStdinResultFields(), IOContract.ObservedReadStdinRemainingFields();
    forall i: nat | i < |cmd.inputs|
      ensures (CatSchema.Stdin in cmd.inputs[..i + 1]) ==
              (CatSchema.Stdin in cmd.inputs[..i] || cmd.inputs[i].Stdin?)
    {
      assert cmd.inputs[..i + 1] == cmd.inputs[..i] + [cmd.inputs[i]];
    }
  }

  ghost predicate InputTraceRelation(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    data: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool,
    readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    dataFragments: seq<BenchWorld.Bytes>,
    dataCuts: seq<nat>,
    errorFragments: seq<BenchWorld.Bytes>,
    errorCuts: seq<nat>
  )
  {
    exists stdinStates: seq<BenchWorld.Bytes> ::
      StdinTraceRelation(cmd, preStdin, postStdin, preStreams, stdinStates) &&
      |readResults| == |cmd.inputs| &&
      |dataFragments| == |cmd.inputs| &&
      |errorFragments| == |cmd.inputs| &&
      (forall i: nat | i < |cmd.inputs| ::
         InputReadOutcomeRelation(cmd, preFs, preStreams, stdinStates[i], i, readResults[i]) &&
         dataFragments[i] == InputDataPiece(readResults[i]) &&
         errorFragments[i] == InputErrorPiece(cmd.inputs[i], readResults[i])) &&
      FragmentsConcatenate(dataFragments, data, dataCuts) &&
      FragmentsConcatenate(errorFragments, errors, errorCuts) &&
      hadError ==
      (exists i: nat ::
         i < |cmd.inputs| && InputFailed(cmd.inputs[i], readResults[i]))
  }

  lemma EmptyInputWitnesses(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes
  )
    requires NormalStdinObservations(preStdin, preStreams)
    requires forall i: nat | i < |cmd.inputs| ::
               CompleteReadResultRelation(cmd, preFs, preStreams, preStdin, i, Result.Ok([]))
    ensures InputTraceRelation(
              cmd, preFs, preStreams, preStdin,
              if CatSchema.Stdin in cmd.inputs then [] else preStdin,
              [], [], false,
              seq(|cmd.inputs|, i => Result.Ok([])),
              seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0),
              seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0))
    ensures RenderRelation(cmd, [], [], [], [0], [])
  {
    hide IOContract.ObservedReadStdinResultFields(), IOContract.ObservedReadStdinRemainingFields();
    var results: seq<BenchWorld.IOResult<BenchWorld.Bytes>> :=
      seq(|cmd.inputs|, i => Result.Ok([]));
    forall i: nat | i < |cmd.inputs|
      ensures CompleteReadResultRelation(cmd, preFs, preStreams, preStdin, i, results[i])
      ensures InputDataPiece(results[i]) == []
      ensures InputErrorPiece(cmd.inputs[i], results[i]) == []
      ensures !InputFailed(cmd.inputs[i], results[i])
    {
    }
    CompleteStdinTrace(cmd, preFs, preStreams, preStdin, results);
  }

  predicate PlainStdinCommand(cmd: CatSchema.CatCmd)
  {
    cmd.number == CatSchema.NoNumber && !cmd.squeezeBlank &&
    !cmd.showEnds && !cmd.showTabs && !cmd.showNonPrinting &&
    |cmd.inputs| > 0 && forall i: nat | i < |cmd.inputs| :: cmd.inputs[i] == CatSchema.Stdin
  }

  lemma PlainStdinWitnesses(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    data: BenchWorld.Bytes
  )
    requires NormalStdinObservations(data, preStreams)
    requires PlainStdinCommand(cmd)
    ensures InputTraceRelation(cmd, preFs, preStreams, data, [], data, [], false,
                               seq(|cmd.inputs|, i => Result.Ok(if i == 0 then data else [])),
                               seq(|cmd.inputs|, i => if i == 0 then data else []),
                               seq(|cmd.inputs| + 1, i => (if i == 0 then 0 else |data|) as nat),
                               seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0))
    ensures RenderRelation(cmd, data, data,
                           seq(|data|, i requires 0 <= i < |data| => [data[i]]),
                           seq(|data| + 1, i => i), seq(|data|, i => 0))
  {
    hide IOContract.ObservedReadStdinResultFields(), IOContract.ObservedReadStdinRemainingFields();
    var results: seq<BenchWorld.IOResult<BenchWorld.Bytes>> :=
      seq(|cmd.inputs|, i => Result.Ok(if i == 0 then data else []));
    forall i: nat {:trigger cmd.inputs[i]} | i < |cmd.inputs|
      ensures CompleteReadResultRelation(cmd, preFs, preStreams, data, i, results[i])
      ensures InputDataPiece(results[i]) == (if i == 0 then data else [])
      ensures InputErrorPiece(cmd.inputs[i], results[i]) == []
      ensures !InputFailed(cmd.inputs[i], results[i])
    {
      if i > 0 { assert cmd.inputs[0] == CatSchema.Stdin; }
    }
    assert FragmentsConcatenate(
        seq(|cmd.inputs|, i => if i == 0 then data else []), data,
        seq(|cmd.inputs| + 1, i => if i == 0 then 0 else |data|));
    assert FragmentsConcatenate(
        seq(|cmd.inputs|, i => []), [], seq(|cmd.inputs| + 1, i => 0));
    assert InputTraceRelation(cmd, preFs, preStreams, data, [], data, [], false,
                              seq(|cmd.inputs|, i => Result.Ok(if i == 0 then data else [])),
                              seq(|cmd.inputs|, i => if i == 0 then data else []),
                              seq(|cmd.inputs| + 1, i => if i == 0 then 0 else |data|),
                              seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0)) by {
      CompleteStdinTrace(cmd, preFs, preStreams, data, results);
    }
    forall p: nat | p < |data|
      ensures !NumberedAt(cmd, data, p)
      ensures RenderFragment(cmd, data, p, 0) == [data[p]]
      ensures data[p..p + 1] == [data[p]]
    {
    }
    assert RenderRelation(cmd, data, data,
                          seq(|data|, i requires 0 <= i < |data| => [data[i]]),
                          seq(|data| + 1, i => i), seq(|data|, i => 0));
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
    cmd: CatSchema.CatCmd, preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes, postStdin: BenchWorld.Bytes,
    data: BenchWorld.Bytes, errors: BenchWorld.Bytes, hadError: bool,
    readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
    dataFragments: seq<BenchWorld.Bytes>, dataCuts: seq<nat>,
    errorFragments: seq<BenchWorld.Bytes>, errorCuts: seq<nat>
  )
    requires NormalStdinObservations(preStdin, preStreams)
    requires PlainStdinCommand(cmd)
    requires InputTraceRelation(cmd, preFs, preStreams, preStdin, postStdin, data, errors,
                                hadError, readResults, dataFragments, dataCuts, errorFragments, errorCuts)
    ensures postStdin == [] && data == preStdin && errors == [] && !hadError
  {
    hide IOContract.ObservedReadStdinResultFields(), IOContract.ObservedReadStdinRemainingFields();
    var states: seq<BenchWorld.Bytes> :| StdinTraceRelation(cmd, preStdin, postStdin, preStreams, states) &&
                                         forall i: nat | i < |cmd.inputs| :: InputReadOutcomeRelation(cmd, preFs, preStreams, states[i], i, readResults[i]);
    var normalStates := seq(|cmd.inputs| + 1, i requires 0 <= i <= |cmd.inputs| => if i == 0 then preStdin else []);
    assert StdinTraceRelation(cmd, preStdin, [], preStreams, normalStates);
    forall i: nat | i <= |cmd.inputs|
      ensures states[i] == normalStates[i]
    { StdinStatePrefixFunctional(cmd, preStdin, preStreams, states, normalStates, i); }

    forall i: nat | i < |cmd.inputs|
      ensures readResults[i] == Result.Ok(if i == 0 then preStdin else [])
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
      assert output[p..p + 1][0] == output[p];
      assert output[p..p + 1][0] == data[p];
    }
  }

  ghost predicate RunRelation(
    cmd: CatSchema.CatCmd,
    preFs: BenchWorld.FileSystem, preStreams: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    preStdin: BenchWorld.Bytes,
    postStdin: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    exit: int
  )
    ensures
      (NormalStdinObservations(preStdin, preStreams) && (forall i: nat | i < |cmd.inputs| ::
                                                           CompleteReadResultRelation(cmd, preFs, preStreams, preStdin, i, Result.Ok([])))) &&
      postStdin == (if CatSchema.Stdin in cmd.inputs then [] else preStdin) &&
      output == [] && errors == [] && exit == 0 ==>
        RunRelation(cmd, preFs, preStreams, preStdin, postStdin, output, errors, exit)
    ensures ((NormalStdinObservations(preStdin, preStreams) && PlainStdinCommand(cmd)) && postStdin == [] && output == preStdin &&
             errors == [] && exit == 0) ==>
              RunRelation(cmd, preFs, preStreams, preStdin, postStdin, output, errors, exit)
    ensures ((NormalStdinObservations(preStdin, preStreams) && PlainStdinCommand(cmd)) &&
             RunRelation(cmd, preFs, preStreams, preStdin, postStdin, output, errors, exit)) ==>
              postStdin == [] && output == preStdin && errors == [] && exit == 0
  {
    hide IOContract.ObservedReadStdinResultFields(), IOContract.ObservedReadStdinRemainingFields();
    assert (NormalStdinObservations(preStdin, preStreams) && PlainStdinCommand(cmd)) ==>
        InputTraceRelation(cmd, preFs, preStreams, preStdin, [], preStdin, [], false,
                           seq(|cmd.inputs|, i => Result.Ok(if i == 0 then preStdin else [])),
                           seq(|cmd.inputs|, i => if i == 0 then preStdin else []),
                           seq(|cmd.inputs| + 1, i => if i == 0 then 0 else |preStdin|),
                           seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0)) &&
        RenderRelation(cmd, preStdin, preStdin,
                       seq(|preStdin|, i requires 0 <= i < |preStdin| => [preStdin[i]]),
                       seq(|preStdin| + 1, i => i), seq(|preStdin|, i => 0)) by {
      if (NormalStdinObservations(preStdin, preStreams) && PlainStdinCommand(cmd)) { PlainStdinWitnesses(cmd, preFs, preStreams, preStdin); }
    }
    assert (NormalStdinObservations(preStdin, preStreams) && (forall i: nat | i < |cmd.inputs| ::
                                                                CompleteReadResultRelation(cmd, preFs, preStreams, preStdin, i, Result.Ok([])))) ==>
        InputTraceRelation(
          cmd, preFs, preStreams, preStdin,
          if CatSchema.Stdin in cmd.inputs then [] else preStdin,
          [], [], false,
          seq(|cmd.inputs|, i => Result.Ok([])),
          seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0),
          seq(|cmd.inputs|, i => []), seq(|cmd.inputs| + 1, i => 0)) &&
        RenderRelation(cmd, [], [], [], [0], []) by {
      if NormalStdinObservations(preStdin, preStreams) && forall i: nat | i < |cmd.inputs| ::
           CompleteReadResultRelation(cmd, preFs, preStreams, preStdin, i, Result.Ok([])) {
        EmptyInputWitnesses(cmd, preFs, preStreams, preStdin);
      }
    }
    hide InputTraceRelation(), RenderRelation();
    var valid := exists readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
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
                     preFs, preStreams,
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
    assert ((NormalStdinObservations(preStdin, preStreams) && PlainStdinCommand(cmd)) && valid) ==>
        postStdin == [] && output == preStdin && errors == [] && exit == 0 by {
      if (NormalStdinObservations(preStdin, preStreams) && PlainStdinCommand(cmd)) && valid {
        var readResults: seq<BenchWorld.IOResult<BenchWorld.Bytes>>,
            data: BenchWorld.Bytes, dataFragments: seq<BenchWorld.Bytes>,
            dataCuts: seq<nat>, errorFragments: seq<BenchWorld.Bytes>,
            errorCuts: seq<nat>, hadError: bool,
            byteFragments: seq<BenchWorld.Bytes>, outputCuts: seq<nat>,
            numbers: seq<nat> :|
          InputTraceRelation(cmd, preFs, preStreams, preStdin, postStdin, data, errors,
                             hadError, readResults, dataFragments, dataCuts, errorFragments, errorCuts) &&
          RenderRelation(cmd, data, output, byteFragments, outputCuts, numbers) &&
          exit == (if hadError then 1 else 0);
        PlainStdinTraceIdentity(cmd, preFs, preStreams, preStdin, postStdin, data, errors,
                                hadError, readResults, dataFragments, dataCuts, errorFragments, errorCuts);
        PlainRenderIdentity(cmd, data, output, byteFragments, outputCuts, numbers);
      }
    }
    valid
  }

  twostate predicate PreparedSpec(raw: CatSchema.CatCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes)
    reads io.stdinRegion
    ensures
      Command(raw).mode == CatSchema.ModeRun &&
      (NormalStdinObservations(old(io.stdin()), old(io.trustedStreams())) && (forall i: nat | i < |Command(raw).inputs| ::
                                                                                CompleteReadResultRelation(Command(raw), old(io.fs()), old(io.trustedStreams()), old(io.stdin()), i, Result.Ok([])))) &&
      io.stdin() == (if CatSchema.Stdin in Command(raw).inputs then [] else old(io.stdin())) &&
      plannedStdout == [] && plannedStderr == [] && exit == 0 ==>
        PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
    ensures (Command(raw).mode == CatSchema.ModeRun && (NormalStdinObservations(old(io.stdin()), old(io.trustedStreams())) && PlainStdinCommand(Command(raw))) &&
             io.stdin() == [] && plannedStdout == old(io.stdin()) &&
             plannedStderr == [] && exit == 0) ==> PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
    ensures (Command(raw).mode == CatSchema.ModeRun && (NormalStdinObservations(old(io.stdin()), old(io.trustedStreams())) && PlainStdinCommand(Command(raw))) &&
             PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)) ==> (io.stdin() == [] &&
                                                                             plannedStdout == old(io.stdin()) &&
                                                                             plannedStderr == [] && exit == 0)
  {
    hide IOContract.ObservedReadStdinResultFields(), IOContract.ObservedReadStdinRemainingFields();
    var cmd := Command(raw);
    assert (NormalStdinObservations(old(io.stdin()), old(io.trustedStreams())) && PlainStdinCommand(cmd)) ==>
        RunRelation(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), [], old(io.stdin()), [], 0);
    assert
      (NormalStdinObservations(old(io.stdin()), old(io.trustedStreams())) && (forall i: nat | i < |cmd.inputs| ::
                                                                                CompleteReadResultRelation(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()), i, Result.Ok([])))) ==>
        RunRelation(cmd, old(io.fs()), old(io.trustedStreams()), old(io.stdin()),
                    if CatSchema.Stdin in cmd.inputs then [] else old(io.stdin()), [], [], 0);
    if cmd.mode == CatSchema.ModeHelp then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == HelpTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else if cmd.mode == CatSchema.ModeVersion then
      io.stdin() == old(io.stdin()) &&
      plannedStdout == VersionTextSpec() &&
      plannedStderr == [] &&
      exit == 0
    else
      exists output: BenchWorld.Bytes, errors: BenchWorld.Bytes ::
        RunRelation(
          cmd,
          old(io.fs()), old(io.trustedStreams()),
          old(io.stdin()),
          io.stdin(),
          output,
          errors,
          exit
        ) &&
        plannedStdout == output &&
        plannedStderr == errors
  }

  function Emits(raw: CatSchema.CatCmdRaw): bool
  {
    true
  }

  function StreamWriteErrorMessage(message: string): BenchWorld.Bytes
  {
    StreamUtf8.Encode(StreamWriteErrorText(message))
  }


  twostate predicate Emit(io: BenchIO.IO,
                         out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
                         normalExit: int, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    var observations := old(io.trustedStreams());
    var stdoutResult := if out == [] then BenchWorld.StreamWriteResult(0, old(io.stdout()), 0)
                        else observations(BenchWorld.StreamWriteStdout(old(io.stdout()), out));
    stdoutResult.StreamWriteResult? &&
    var errors := diagnostics + (if stdoutResult.err == 0 then [] else
                                 StreamWriteErrorMessage(StreamContract.CLocaleErrnoTextResult(stdoutResult.err)));
    var stderrResult := if errors == [] then BenchWorld.StreamWriteResult(0, old(io.stderr()), 0)
                        else observations(BenchWorld.StreamWriteStderr(old(io.stderr()), errors));
    stderrResult.StreamWriteResult? &&
    (if out == [] then io.stdout() == old(io.stdout()) else StreamContract.WriteStdoutSpec(
       old(io.stdout()), observations, io.stdout(), out, stdoutResult.committed, stdoutResult.err)) &&
    (if errors == [] then io.stderr() == old(io.stderr()) else StreamContract.WriteStderrSpec(
       old(io.stderr()), observations, io.stderr(), errors, stderrResult.committed, stderrResult.err)) &&
    exit == (if stdoutResult.err != 0 || stderrResult.err != 0 then 1 else normalExit)
  }

  twostate predicate Emission(raw: CatSchema.CatCmdRaw, io: BenchIO.IO,
                              out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
                              normalExit: int, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    if Emits(raw) then
      Emit(io, out, diagnostics, normalExit, exit)
    else
      io.stdout() == old(io.stdout()) && io.stderr() == old(io.stderr()) &&
      exit == normalExit
  }

  twostate predicate Spec(raw: CatSchema.CatCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    exists out: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit,
                   out, diagnostics) &&
      Emission(raw, io, out, diagnostics, normalExit, exit)
  }
  function VersionTextValue(): string
  {
    "cat (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Torbjorn Granlund and Richard M. Stallman.\n"
  }

  function ErrorPrefix(): BenchWorld.Bytes { "cat: " }
  function ErrorSeparator(): BenchWorld.Bytes { ": " }
  function DiagnosticSuffix(): BenchWorld.Bytes { "\n" }
  function StreamWriteErrorText(message: string): string { "cat: write error: " + message + "\n" }

}
