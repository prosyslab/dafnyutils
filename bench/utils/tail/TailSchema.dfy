include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module TailSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype TailMode = ModeRun | ModeHelp | ModeVersion | ModeInvalidCount
  datatype CountUnit = CountLines | CountBytes
  datatype HeaderMode = HeadersMultiple | HeadersNever | HeadersAlways
  datatype Input = Stdin(displayName: string) | File(path: BenchWorld.Path)

  datatype CountSelection = CountSelection(unit: CountUnit, fromStart: bool, amount: nat)

  datatype TailCmdRaw = TailCmdRaw(
    selection: CountSelection,
    headerMode: HeaderMode,
    zeroTerminated: bool,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    invalidCountUnit: CountUnit,
    invalidCountValue: string,
    invalidCountTokenIndex: int,
    operands: seq<string>
  )

  datatype TailCmd = TailCmd(
    mode: TailMode,
    selection: CountSelection,
    headerMode: HeaderMode,
    zeroTerminated: bool,
    invalidCountUnit: CountUnit,
    invalidCountValue: string,
    inputs: seq<Input>
  )

  datatype TailParseFailurePlan =
    | TailRun(raw: TailCmdRaw)
    | TailParseError(error: CliTypes.ParseError)

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema(
      [
        CliTypes.OptionDecl("tail.bytes", ['c'], ["bytes"], CliTypes.ReqArg),
        CliTypes.OptionDecl("tail.lines", ['n'], ["lines"], CliTypes.ReqArg),
        CliTypes.OptionDecl("tail.zero_terminated", ['z'], ["zero-terminated"], CliTypes.NoArg),
        CliTypes.OptionDecl("tail.quiet", ['q'], ["quiet", "silent"], CliTypes.NoArg),
        CliTypes.OptionDecl("tail.verbose", ['v'], ["verbose"], CliTypes.NoArg),
        CliTypes.OptionDecl("tail.help", [], ["help"], CliTypes.NoArg),
        CliTypes.OptionDecl("tail.version", [], ["version"], CliTypes.NoArg),
        CliTypes.OptionDecl("tail.legacy_digit", ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'], [], CliTypes.OptArg),
        CliTypes.OptionDecl("tail.legacy_lines", ['l'], [], CliTypes.NoArg),
        CliTypes.OptionDecl("tail.legacy_blocks", ['b'], [], CliTypes.NoArg)
      ],
      true
    );
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true);
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: TailParseFailurePlan)
    decreases *
  {
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var invalidUnit := CountLines;
    var invalidValue := "";
    var invalidTokenIndex := -1;

    var i := 0;
    while i < |argv| && i < e.tokenIndex
      decreases |argv| - i
    {
      var token := argv[i];
      if token == "--help" {
        seenHelp := true;
        if helpTokenIndex == -1 {
          helpTokenIndex := i;
        }
      } else if token == "--version" {
        seenVersion := true;
        if versionTokenIndex == -1 {
          versionTokenIndex := i;
        }
      }

      var countUnit := CountLines;
      var countValue := "";
      var hasCountValue := false;
      var consumedNext := false;

      if token == "-n" || token == "--lines" {
        countUnit := CountLines;
        if i + 1 < |argv| && i + 1 < e.tokenIndex {
          countValue := argv[i + 1];
          hasCountValue := true;
          consumedNext := true;
        }
      } else if token == "-c" || token == "--bytes" {
        countUnit := CountBytes;
        if i + 1 < |argv| && i + 1 < e.tokenIndex {
          countValue := argv[i + 1];
          hasCountValue := true;
          consumedNext := true;
        }
      } else if 8 <= |token| && token[..8] == "--lines=" {
        countUnit := CountLines;
        countValue := token[8..];
        hasCountValue := true;
      } else if 8 <= |token| && token[..8] == "--bytes=" {
        countUnit := CountBytes;
        countValue := token[8..];
        hasCountValue := true;
      } else if |token| > 2 && token[0] == '-' && token[1] == 'n' {
        countUnit := CountLines;
        countValue := token[2..];
        hasCountValue := true;
      } else if |token| > 2 && token[0] == '-' && token[1] == 'c' {
        countUnit := CountBytes;
        countValue := token[2..];
        hasCountValue := true;
      }

      if hasCountValue && invalidTokenIndex == -1 {
        var ok, fromStart, amount := ParseCountArg(countValue);
        if !ok {
          invalidUnit := countUnit;
          invalidValue := countValue;
          invalidTokenIndex := i;
        }
      }

      if consumedNext {
        i := i + 2;
      } else {
        i := i + 1;
      }
    }

    if seenHelp &&
       (!seenVersion || helpTokenIndex <= versionTokenIndex) &&
       (invalidTokenIndex == -1 || helpTokenIndex <= invalidTokenIndex) {
      plan := TailRun(TailCmdRaw(
                        CountSelection(CountLines, false, 10),
                        HeadersMultiple,
                        false,
                        true,
                        false,
                        0,
                        -1,
                        CountLines,
                        "",
                        -1,
                        []
                      ));
      return;
    }

    if seenVersion &&
       (invalidTokenIndex == -1 || versionTokenIndex <= invalidTokenIndex) {
      plan := TailRun(TailCmdRaw(
                        CountSelection(CountLines, false, 10),
                        HeadersMultiple,
                        false,
                        false,
                        true,
                        -1,
                        0,
                        CountLines,
                        "",
                        -1,
                        []
                      ));
      return;
    }

    if invalidTokenIndex != -1 {
      plan := TailRun(TailCmdRaw(
                        CountSelection(CountLines, false, 10),
                        HeadersMultiple,
                        false,
                        false,
                        false,
                        -1,
                        -1,
                        invalidUnit,
                        invalidValue,
                        invalidTokenIndex,
                        []
                      ));
      return;
    }

    plan := TailParseError(e);
  }

  function IsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function CountSuffixMultiplier(suffix: string): nat
  {
    if suffix == "" then
      1
    else if suffix == "b" then
      512
    else if suffix == "k" || suffix == "K" || suffix == "KiB" then
      1024
    else if suffix == "kB" || suffix == "KB" then
      1000
    else if suffix == "m" || suffix == "M" || suffix == "MiB" then
      1048576
    else if suffix == "MB" then
      1000000
    else if suffix == "G" || suffix == "GiB" then
      1073741824
    else if suffix == "GB" then
      1000000000
    else if suffix == "T" || suffix == "TiB" then
      1099511627776
    else if suffix == "TB" then
      1000000000000
    else if suffix == "P" || suffix == "PiB" then
      1125899906842624
    else if suffix == "PB" then
      1000000000000000
    else if suffix == "E" || suffix == "EiB" then
      1152921504606846976
    else if suffix == "EB" then
      1000000000000000000
    else
      0
  }

  method ParseCountArg(text: string) returns (ok: bool, fromStart: bool, amount: nat)
  {
    ok := false;
    fromStart := false;
    amount := 0;

    var i := 0;
    if |text| > 0 && text[0] == '-' {
      i := 1;
    } else if |text| > 0 && text[0] == '+' {
      fromStart := true;
      i := 1;
    }

    var sawDigits := false;
    while i < |text| && IsDigit(text[i])
      invariant 0 <= i <= |text|
      decreases |text| - i
    {
      sawDigits := true;
      var digit := ((text[i] as int) - ('0' as int)) as nat;
      amount := amount * 10 + digit;
      i := i + 1;
    }

    var multiplier := CountSuffixMultiplier(text[i..]);
    if multiplier == 0 || (!sawDigits && multiplier == 1) {
      amount := 0;
      return;
    }
    if !sawDigits {
      amount := 1;
    }
    amount := amount * multiplier;
    ok := true;
  }

  method ParseLegacyCountToken(text: string) returns (ok: bool, selection: CountSelection)
  {
    ok := false;
    selection := CountSelection(CountLines, false, 10);
    if |text| <= 1 {
      return;
    }
    if text[0] != '-' && text[0] != '+' {
      return;
    }

    var fromStart := text[0] == '+';
    var amount: nat := 0;
    var sawDigits := false;
    var i := 1;
    while i < |text| && IsDigit(text[i])
      invariant 1 <= i <= |text|
      decreases |text| - i
    {
      sawDigits := true;
      var digit := ((text[i] as int) - ('0' as int)) as nat;
      amount := amount * 10 + digit;
      i := i + 1;
    }
    if !sawDigits {
      amount := 10;
    }

    if i == |text| {
      if sawDigits {
        selection := CountSelection(CountLines, fromStart, amount);
        ok := true;
      }
      return;
    }

    if i + 1 != |text| {
      return;
    }

    if text[i] == 'c' {
      selection := CountSelection(CountBytes, fromStart, amount);
      ok := true;
    } else if text[i] == 'l' {
      selection := CountSelection(CountLines, fromStart, amount);
      ok := true;
    } else if text[i] == 'b' {
      selection := CountSelection(CountBytes, fromStart, amount * 512);
      ok := true;
    }
  }

  method DecodeCountOption(
    occ: CliTypes.OptOccurrence,
    unit: CountUnit,
    current: CountSelection,
    invalidUnit: CountUnit,
    invalidValue: string,
    invalidTokenIndex: int
  ) returns (
      next: CountSelection,
      nextInvalidUnit: CountUnit,
      nextInvalidValue: string,
      nextInvalidTokenIndex: int
    )
  {
    next := current;
    nextInvalidUnit := invalidUnit;
    nextInvalidValue := invalidValue;
    nextInvalidTokenIndex := invalidTokenIndex;

    match occ.value
    case Some(value) =>
      var ok, fromStart, amount := ParseCountArg(value);
      if ok {
        next := CountSelection(unit, fromStart, amount);
      } else if nextInvalidTokenIndex == -1 || occ.tokenIndex < nextInvalidTokenIndex {
        nextInvalidUnit := unit;
        nextInvalidValue := value;
        nextInvalidTokenIndex := occ.tokenIndex;
      }
    case None =>
      if nextInvalidTokenIndex == -1 || occ.tokenIndex < nextInvalidTokenIndex {
        nextInvalidUnit := unit;
        nextInvalidValue := "";
        nextInvalidTokenIndex := occ.tokenIndex;
      }
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: TailCmdRaw)
  {
    var selection := CountSelection(CountLines, false, 10);
    var headerMode := HeadersMultiple;
    var zeroTerminated := false;
    var seenHelp := false;
    var seenVersion := false;
    var helpTokenIndex := -1;
    var versionTokenIndex := -1;
    var invalidCountUnit := CountLines;
    var invalidCountValue := "";
    var invalidCountTokenIndex := -1;

    var i := 0;
    while i < |p.options|
      decreases |p.options| - i
    {
      var occ := p.options[i];
      if occ.key == "tail.lines" {
        selection, invalidCountUnit, invalidCountValue, invalidCountTokenIndex :=
          DecodeCountOption(
            occ,
            CountLines,
            selection,
            invalidCountUnit,
            invalidCountValue,
            invalidCountTokenIndex
          );
      }
      if occ.key == "tail.bytes" {
        selection, invalidCountUnit, invalidCountValue, invalidCountTokenIndex :=
          DecodeCountOption(
            occ,
            CountBytes,
            selection,
            invalidCountUnit,
            invalidCountValue,
            invalidCountTokenIndex
          );
      }
      if occ.key == "tail.quiet" {
        headerMode := HeadersNever;
      }
      if occ.key == "tail.verbose" {
        headerMode := HeadersAlways;
      }
      if occ.key == "tail.zero_terminated" {
        zeroTerminated := true;
      }
      if occ.key == "tail.help" {
        seenHelp := true;
        if helpTokenIndex == -1 || occ.tokenIndex < helpTokenIndex {
          helpTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "tail.version" {
        seenVersion := true;
        if versionTokenIndex == -1 || occ.tokenIndex < versionTokenIndex {
          versionTokenIndex := occ.tokenIndex;
        }
      }
      if occ.key == "tail.legacy_digit" || occ.key == "tail.legacy_lines" || occ.key == "tail.legacy_blocks" {
        var legacyOk, legacySelection := ParseLegacyCountToken(occ.rawToken);
        if legacyOk && |p.options| == 1 && |p.positionals| <= 1 {
          selection := legacySelection;
        } else if invalidCountTokenIndex == -1 || occ.tokenIndex < invalidCountTokenIndex {
          invalidCountUnit := CountLines;
          invalidCountValue := occ.rawToken;
          invalidCountTokenIndex := occ.tokenIndex;
        }
      }
      i := i + 1;
    }

    var operands := p.positionals;
    if |p.options| == 0 && |p.positionals| <= 2 && |p.positionals| > 0 {
      var legacyOk, legacySelection := ParseLegacyCountToken(p.positionals[0]);
      if legacyOk && legacySelection.fromStart {
        selection := legacySelection;
        operands := p.positionals[1..];
      }
    }

    raw := TailCmdRaw(
      selection,
      headerMode,
      zeroTerminated,
      seenHelp,
      seenVersion,
      helpTokenIndex,
      versionTokenIndex,
      invalidCountUnit,
      invalidCountValue,
      invalidCountTokenIndex,
      operands
    );
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    if e.kind == CliTypes.UnknownOption || e.kind == CliTypes.UnexpectedValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "tail: unrecognized option '" + e.rawToken + "'\n" +
        "Try 'tail --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "tail: invalid option -- '" + [e.rawToken[1]] + "'\n" +
        "Try 'tail --help' for more information.\n"
      else
        "tail: invalid option\nTry 'tail --help' for more information.\n"
    else if e.kind == CliTypes.MissingValue then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' && e.rawToken[1] == '-' then
        "tail: option '" + e.rawToken + "' requires an argument\n" +
        "Try 'tail --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        "tail: option requires an argument -- '" + [e.rawToken[|e.rawToken| - 1]] + "'\n" +
        "Try 'tail --help' for more information.\n"
      else
        "tail: option requires an argument\nTry 'tail --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "tail: option '" + e.rawToken + "' is ambiguous\n" +
      "Try 'tail --help' for more information.\n"
    else
      "tail: parse error at token '" + e.rawToken + "'\n"
  }

  method FormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }
}
