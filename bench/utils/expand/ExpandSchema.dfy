include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module ExpandSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype ExpandMode = ModeRun | ModeHelp | ModeVersion | ModeInvalidTabs
  datatype Input = Stdin | File(path: BenchWorld.Path)
  datatype TabArg = TabArg(text: string, tokenIndex: int)
  datatype RepeatMode = RepeatNone | RepeatFixed(width: nat) | RepeatIncremental(width: nat)
  datatype TabStops = TabStops(stops: seq<nat>, repeat: RepeatMode)
  datatype MarkerKind = MarkerNone | MarkerSlash | MarkerPlus
  datatype MarkerScan = MarkerScan(index: nat, marker: MarkerKind, hasMarker: bool)
  datatype TabAccum = TabAccum(
    stops: seq<nat>,
    extendSize: nat,
    incrementSize: nat,
    activeMarker: MarkerKind
  )
  datatype NatParse = NatOk(value: nat) | NatErr
  datatype TabAccumParse = TabAccumOk(acc: TabAccum) | TabAccumErr(value: string)
  datatype TabParse = TabOk(tabs: TabStops) | TabErr(value: string)
  datatype OptionScan =
    | ScanContinue(acc: TabAccum)
    | ScanHelp
    | ScanVersion
    | ScanInvalidTabs(value: string)

  datatype ExpandCmdRaw = ExpandCmdRaw(
    tabArgs: seq<TabArg>,
    seenInitial: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>
  )

  datatype ExpandCmd = ExpandCmd(
    mode: ExpandMode,
    tabs: TabStops,
    initialOnly: bool,
    invalidTabsValue: string,
    inputs: seq<Input>
  )

  function NumericShortTabText(ch: char, value: CliTypes.OptionalString): string
  {
    match value
    case None => [ch]
    case Some(suffix) => [ch] + suffix
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("expand.tabs", ['t'], ["tabs"], CliTypes.ReqArg),
        CliTypes.OptionDecl("expand.initial", ['i'], ["initial"], CliTypes.NoArg),
        CliTypes.OptionDecl("expand.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("expand.version", [], ["version"], CliTypes.NoArg),
        CliTypes.OptionDecl(
          "expand.numeric-tabs",
          ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'],
          [],
          CliTypes.OptArg
        )
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: ExpandCmdRaw)
  {
    var tabArgs: seq<TabArg> := [];
    var seenInitial := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "expand.tabs" {
        match occ.value
        case Some(value) =>
          tabArgs := tabArgs + [TabArg(value, occ.tokenIndex)];
        case None =>
      }
      if occ.key == "expand.numeric-tabs" {
        match occ.src
        case Short(ch) =>
          tabArgs := tabArgs + [TabArg(
                                  NumericShortTabText(ch, occ.value), occ.tokenIndex
                                )];
        case Long(_) =>
      }
      if occ.key == "expand.initial" {
        seenInitial := true;
      }
      if occ.key == "expand.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "expand.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    raw := ExpandCmdRaw(tabArgs, seenInitial, seenHelp, seenVersion, helpTokenIndex, versionTokenIndex, p.positionals);
  }

  function TryHelpText(): BenchWorld.Bytes
  {
    "Try 'expand --help' for more information.\n"
  }

  function HasPrefix(text: string, prefix: string): bool
  {
    |prefix| <= |text| && text[..|prefix|] == prefix
  }

  function BeforeEquals(text: string): string
    decreases |text|
  {
    if |text| == 0 || text[0] == '=' then
      ""
    else
      [text[0]] + BeforeEquals(text[1..])
  }

  function CanonicalLongName(rawToken: string): string
  {
    var name := if |rawToken| > 2 then BeforeEquals(rawToken[2..]) else "";
    if HasPrefix("tabs", name) then "tabs"
    else if HasPrefix("initial", name) then "initial"
    else if HasPrefix("help", name) then "help"
    else if HasPrefix("version", name) then "version"
    else name
  }

  function ShortErrorCharFrom(rawToken: string, i: nat): char
    requires i <= |rawToken|
    decreases |rawToken| - i
  {
    if i == |rawToken| then
      '?'
    else if rawToken[i] == 'i' then
      ShortErrorCharFrom(rawToken, i + 1)
    else
      rawToken[i]
  }

  function ShortErrorChar(rawToken: string): char
  {
    if |rawToken| > 1 then ShortErrorCharFrom(rawToken, 1) else '?'
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "expand: unrecognized option '" + e.rawToken + "'\n" + TryHelpText()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        var option: string := [ShortErrorChar(e.rawToken)];
        "expand: invalid option -- '" + option + "'\n" + TryHelpText()
      else
        "expand: invalid option\n" + TryHelpText()
    else if e.kind == CliTypes.UnexpectedValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "expand: option '--" + CanonicalLongName(e.rawToken) +
        "' doesn't allow an argument\n" + TryHelpText()
      else
        var option: string := [ShortErrorChar(e.rawToken)];
        "expand: invalid option -- '" + option + "'\n" + TryHelpText()
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "expand: option '--" + CanonicalLongName(e.rawToken) +
        "' requires an argument\n" + TryHelpText()
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        var option: string := [ShortErrorChar(e.rawToken)];
        "expand: option requires an argument -- '" +
        option + "'\n" + TryHelpText()
      else
        "expand: option requires an argument\n" + TryHelpText()
    else
      "expand: option '" + e.rawToken + "' is ambiguous\n" + TryHelpText()
  }

  method ExpandFormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }
}
