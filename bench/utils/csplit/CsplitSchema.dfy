include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module CsplitSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype CsplitMode = ModeRun | ModeHelp | ModeVersion
  datatype Input = Stdin | File(path: BenchWorld.Path)
  datatype CsplitCmdRaw = CsplitCmdRaw(
    mode: CsplitMode,
    input: Input,
    lineNumbers: seq<nat>
  )

  datatype LineParse = LineOk(value: nat) | LineErr
  datatype PatternError =
    InvalidPattern(token: string) |
    UnsupportedPattern(token: string)
  datatype PatternParse =
    PatternsOk(lines: seq<nat>) |
    PatternsErr(error: PatternError)

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("csplit.prefix", ['f'], ["prefix"], CliTypes.ReqArg),
        CliTypes.OptionDecl("csplit.suffix_format", ['b'], ["suffix-format"], CliTypes.ReqArg),
        CliTypes.OptionDecl("csplit.digits", ['n'], ["digits"], CliTypes.ReqArg),
        CliTypes.OptionDecl("csplit.keep_files", ['k'], ["keep-files"], CliTypes.NoArg),
        CliTypes.OptionDecl("csplit.suppress_matched", [], ["suppress-matched"], CliTypes.NoArg),
        CliTypes.OptionDecl("csplit.elide_empty_files", ['z'], ["elide-empty-files"], CliTypes.NoArg),
        CliTypes.OptionDecl("csplit.silent", ['s', 'q'], ["silent", "quiet"], CliTypes.NoArg),
        CliTypes.OptionDecl("csplit.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("csplit.version", [], ["version"], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  function IsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function IsDeferredPattern(token: string): bool
  {
    |token| > 0 && (token[0] == '/' || token[0] == '%' || token[0] == '{')
  }

  method ParseLineNumber(text: string) returns (res: LineParse)
  {
    if |text| == 0 {
      res := LineErr;
      return;
    }

    var value: nat := 0;
    var i := 0;
    while i < |text|
      invariant 0 <= i <= |text|
      decreases |text| - i
    {
      if !IsDigit(text[i]) {
        res := LineErr;
        return;
      }
      var digit := ((text[i] as int) - ('0' as int)) as nat;
      value := value * 10 + digit;
      i := i + 1;
    }

    res := LineOk(value);
  }

  method ParseLinePatterns(patterns: seq<string>) returns (result: PatternParse)
    decreases |patterns|
  {
    var lines: seq<nat> := [];

    var i := 0;
    while i < |patterns|
      invariant 0 <= i <= |patterns|
      invariant |lines| == i
      decreases |patterns| - i
    {
      var token := patterns[i];
      var parsed := ParseLineNumber(token);
      match parsed {
        case LineOk(line) =>
          lines := lines + [line];
        case LineErr =>
          if IsDeferredPattern(token) {
            result := PatternsErr(UnsupportedPattern(token));
          } else {
            result := PatternsErr(InvalidPattern(token));
          }
          return;
      }
      i := i + 1;
    }
    result := PatternsOk(lines);
  }

  method DefaultRaw() returns (raw: CsplitCmdRaw)
  {
    raw := CsplitCmdRaw(ModeRun, Stdin, []);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: CsplitCmdRaw)
  {
    raw := DefaultRaw();
  }

  function TryHelpText(): string
  {
    "Try 'csplit --help' for more information.\n"
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption || e.kind == CliTypes.UnexpectedValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "csplit: unrecognized option '" + e.rawToken + "'\n" + TryHelpText()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "csplit: invalid option -- '" + [e.rawToken[1]] + "'\n" + TryHelpText()
      else
        "csplit: invalid option\n" + TryHelpText()
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "csplit: option '" + e.rawToken + "' requires an argument\n" + TryHelpText()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "csplit: option requires an argument -- '" +
        [e.rawToken[|e.rawToken| - 1]] + "'\n" + TryHelpText()
      else
        "csplit: option requires an argument\n" + TryHelpText()
    else if e.kind == CliTypes.Ambiguous then
      "csplit: option '" + e.rawToken + "' is ambiguous\n" + TryHelpText()
    else
      "csplit: parse error at token '" + e.rawToken + "'\n"
  }

  function MissingInputMessage(): string
  {
    "csplit: missing operand\n" + TryHelpText()
  }

  function MissingPatternMessage(input: string): string
  {
    "csplit: missing operand after '" + input + "'\n" + TryHelpText()
  }

  function UnsupportedOptionMessage(rawToken: string): string
  {
    "csplit: option '" + rawToken +
    "' is not supported by this benchmark slice\n" + TryHelpText()
  }

  function InvalidPatternMessage(token: string): string
  {
    "csplit: '" + token + "': invalid pattern\n"
  }

  function UnsupportedPatternMessage(token: string): string
  {
    "csplit: pattern '" + token +
    "' is not supported by this benchmark slice\n" + TryHelpText()
  }

  function PatternErrorMessage(error: PatternError): string
  {
    match error
    case InvalidPattern(token) => InvalidPatternMessage(token)
    case UnsupportedPattern(token) => UnsupportedPatternMessage(token)
  }

  function DigitChar(d: nat): char
    requires d < 10
  {
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
  }

  function DigitsNat(n: nat): BenchWorld.Bytes
    decreases n
  {
    if n < 10 then [DigitChar(n)] else DigitsNat(n / 10) + [DigitChar(n % 10)]
  }

  method CsplitFormatParseError(
    e: CliTypes.ParseError
  ) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<CsplitCmdRaw>)
    decreases *
  {
    var msg := CsplitFormatParseError(e);
    plan := CliTypes.CliEarlyExit(1, [], msg);
  }

  method PlanParsed(
    p: CliTypes.ParsedArgs
  ) returns (plan: CliTypes.CliPlan<CsplitCmdRaw>)
    decreases *
  {
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var unsupportedSeen := false;
    var unsupportedToken := "";
    var unsupportedTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      invariant 0 <= i <= |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "csplit.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      } else if occ.key == "csplit.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      } else if !unsupportedSeen || occ.tokenIndex < unsupportedTokenIndex {
        unsupportedSeen := true;
        unsupportedToken := occ.rawToken;
        unsupportedTokenIndex := occ.tokenIndex;
      }
      i := i + 1;
    }

    if seenHelp && (!seenVersion || helpTokenIndex <= versionTokenIndex) {
      plan := CliTypes.CliRun(
        CsplitCmdRaw(ModeHelp, Stdin, [])
      );
      return;
    }

    if seenVersion {
      plan := CliTypes.CliRun(
        CsplitCmdRaw(ModeVersion, Stdin, [])
      );
      return;
    }

    if unsupportedSeen {
      var msg := Utf8.Encode(
        UnsupportedOptionMessage(unsupportedToken)
      );
      plan := CliTypes.CliEarlyExit(1, [], msg);
      return;
    }

    if |p.positionals| == 0 {
      var msg := Utf8.Encode(MissingInputMessage());
      plan := CliTypes.CliEarlyExit(1, [], msg);
      return;
    }

    if |p.positionals| == 1 {
      var msg := Utf8.Encode(
        MissingPatternMessage(p.positionals[0])
      );
      plan := CliTypes.CliEarlyExit(1, [], msg);
      return;
    }

    var parsed := ParseLinePatterns(p.positionals[1..]);
    match parsed
    case PatternsErr(error) =>
      var msg := Utf8.Encode(PatternErrorMessage(error));
      plan := CliTypes.CliEarlyExit(1, [], msg);
    case PatternsOk(lines) =>
      var input :=
        if p.positionals[0] == "-"
        then Stdin
        else File(p.positionals[0]);
      plan := CliTypes.CliRun(
        CsplitCmdRaw(ModeRun, input, lines)
      );
  }
}
