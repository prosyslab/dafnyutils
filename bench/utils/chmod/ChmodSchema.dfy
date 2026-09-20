include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/CliTypes.dfy"
include "../../core/CliModel.dfy"

module ChmodSchema {
  import BenchWorld
  import Utf8 = Utf8Semantics
  import CliTypes
  import CliModel

  datatype ChmodMode = ModeRun | ModeHelp | ModeVersion

  datatype ChmodCmdRaw = ChmodCmdRaw(
    seenRecursive: bool,
    seenVerbose: bool,
    seenChanges: bool,
    seenSilent: bool,
    preserveRoot: bool,
    dereferenceMode: int,
    traversalMode: int,
    seenReference: bool,
    referenceFile: string,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>,
    diagnoseSurprises: bool
  )

  datatype ChmodCmd = ChmodCmd(
    mode: ChmodMode,
    modeExpr: string,
    files: seq<string>,
    recursive: bool,
    verbose: bool,
    changes: bool,
    silent: bool,
    preserveRoot: bool,
    dereferenceMode: int,
    traversalMode: int,
    seenReference: bool,
    referenceFile: string,
    diagnoseSurprises: bool
  )

  datatype ChmodCliParse = ChmodCliParse(
    recursive: bool,
    verbose: bool,
    changes: bool,
    silent: bool,
    preserveRoot: bool,
    dereferenceMode: int,
    traversalMode: int,
    seenReference: bool,
    referenceFile: string,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    operands: seq<string>,
    diagnoseSurprises: bool
  )

  datatype ChmodDecodeState = ChmodDecodeState(
    recursive: bool,
    verbose: bool,
    changes: bool,
    silent: bool,
    preserveRoot: bool,
    dereferenceMode: int,
    traversalMode: int,
    seenReference: bool,
    referenceFile: string,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int,
    modeOptionParts: seq<string>
  )

  datatype ParseRecovery = ParseNotRecovered | ParseRecovered(raw: ChmodCmdRaw)

  function Options(): seq<CliTypes.OptionDecl>
  {
    [
      CliTypes.OptionDecl("chmod.changes", ['c'], ["changes"], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.dereference", [], ["dereference"], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.recursive", ['R'], ["recursive"], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.no_dereference", ['h'], ["no-dereference"], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.no_preserve_root", [], ["no-preserve-root"], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.preserve_root", [], ["preserve-root"], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.silent", [], ["quiet"], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.reference", [], ["reference"], CliTypes.ReqArg),
      CliTypes.OptionDecl("chmod.silent", ['f'], ["silent"], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.verbose", ['v'], ["verbose"], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.help", [], ["help"], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.version", [], ["version"], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.traverse_H", ['H'], [], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.traverse_L", ['L'], [], CliTypes.NoArg),
      CliTypes.OptionDecl("chmod.traverse_P", ['P'], [], CliTypes.NoArg),
      CliTypes.OptionDecl(
        "chmod.mode_option",
        ['r', 'w', 'x', 'X', 's', 't', 'u', 'g', 'o', 'a', ',', '+', '=',
         '0', '1', '2', '3', '4', '5', '6', '7'],
        [],
        CliTypes.OptArg
      )
    ]
  }

  function SchemaValue(): CliTypes.CliSchema
  {
    CliTypes.CliSchema(Options(), true)
  }

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := SchemaValue();
  }

  function ParserConfigValue(): CliTypes.ParseConfig
  {
    CliTypes.ParseConfig(CliTypes.GNU_Permute, true, true, true)
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := ParserConfigValue();
  }

  function DefaultRawValue(): ChmodCmdRaw
  {
    ChmodCmdRaw(
      false,
      false,
      false,
      false,
      false,
      -1,
      1,
      false,
      "",
      false,
      false,
      -1,
      -1,
      [],
      false
    )
  }

  function JoinModeOptionParts(parts: seq<string>): string
  {
    if |parts| == 0 then
      ""
    else if |parts| == 1 then
      parts[0]
    else
      parts[0] + "," + JoinModeOptionParts(parts[1..])
  }

  function RecoverParseFailureValue(
    err: CliTypes.ParseError,
    argv: seq<string>
  ): ParseRecovery
  {
    if err.tokenIndex < 0 || err.tokenIndex > |argv| then ParseNotRecovered
    else
      var rewritten := argv[..err.tokenIndex] + ["--"] + argv[err.tokenIndex..];
      match CliModel.ParseValue(rewritten, SchemaValue(), ParserConfigValue())
      case ParseFailure(_) => ParseNotRecovered
      case ParseSuccess(parsed) =>
        var candidate := DecodeValue(parsed);
        var cmd := Command(candidate);
        if cmd.mode == ModeHelp || cmd.mode == ModeVersion then ParseRecovered(candidate)
        else ParseNotRecovered
  }

  method TryRecoverParseFailure(err: CliTypes.ParseError, argv: seq<string>)
    returns (ok: bool, raw: ChmodCmdRaw)
  {
    match RecoverParseFailureValue(err, argv)
    case ParseNotRecovered =>
      ok := false;
      raw := DefaultRawValue();
    case ParseRecovered(candidate) =>
      ok := true;
      raw := candidate;
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: ChmodCmdRaw)
  {
    raw := DecodeValue(p);
  }

  function DecodeValue(p: CliTypes.ParsedArgs): ChmodCmdRaw
  {
    var cli := DecodeCliParseValue(p);
    ChmodCmdRaw(
      cli.recursive,
      cli.verbose,
      cli.changes,
      cli.silent,
      cli.preserveRoot,
      cli.dereferenceMode,
      cli.traversalMode,
      cli.seenReference,
      cli.referenceFile,
      cli.seenHelp,
      cli.seenVersion,
      cli.helpTokenIndex,
      cli.versionTokenIndex,
      cli.operands,
      cli.diagnoseSurprises
    )
  }

  function InitialDecodeState(): ChmodDecodeState
  {
    ChmodDecodeState(
      false, false, false, false, false, -1, 1, false, "", false, false,
      -1, -1, []
    )
  }

  function ApplyOccurrence(
    state: ChmodDecodeState,
    occ: CliTypes.OptOccurrence
  ): ChmodDecodeState
  {
    var recursive := state.recursive || occ.key == "chmod.recursive";
    var verbose :=
      if occ.key == "chmod.verbose" then true
      else if occ.key == "chmod.changes" then false
      else state.verbose;
    var changes :=
      if occ.key == "chmod.changes" then true
      else if occ.key == "chmod.verbose" then false
      else state.changes;
    var preserveRoot :=
      if occ.key == "chmod.preserve_root" then true
      else if occ.key == "chmod.no_preserve_root" then false
      else state.preserveRoot;
    var dereferenceMode :=
      if occ.key == "chmod.no_dereference" then 0
      else if occ.key == "chmod.dereference" then 1
      else state.dereferenceMode;
    var traversalMode :=
      if occ.key == "chmod.traverse_H" then 1
      else if occ.key == "chmod.traverse_L" then 2
      else if occ.key == "chmod.traverse_P" then 0
      else state.traversalMode;
    var referenceFile :=
      if occ.key == "chmod.reference" && occ.value.Some? then occ.value.value
      else state.referenceFile;
    var helpTokenIndex :=
      if occ.key == "chmod.help" &&
         (state.helpTokenIndex == -1 || occ.tokenIndex < state.helpTokenIndex) then
        occ.tokenIndex
      else state.helpTokenIndex;
    var versionTokenIndex :=
      if occ.key == "chmod.version" &&
         (state.versionTokenIndex == -1 || occ.tokenIndex < state.versionTokenIndex) then
        occ.tokenIndex
      else state.versionTokenIndex;
    ChmodDecodeState(
      recursive,
      verbose,
      changes,
      state.silent || occ.key == "chmod.silent",
      preserveRoot,
      dereferenceMode,
      traversalMode,
      state.seenReference || occ.key == "chmod.reference",
      referenceFile,
      state.seenHelp || occ.key == "chmod.help",
      state.seenVersion || occ.key == "chmod.version",
      helpTokenIndex,
      versionTokenIndex,
      if occ.key == "chmod.mode_option" then
        state.modeOptionParts + [occ.rawToken]
      else state.modeOptionParts
    )
  }

  function DecodeOptions(
    options: seq<CliTypes.OptOccurrence>,
    state: ChmodDecodeState
  ): ChmodDecodeState
    decreases |options|
  {
    if |options| == 0 then state
    else DecodeOptions(options[1..], ApplyOccurrence(state, options[0]))
  }

  function DecodeCliParseValue(p: CliTypes.ParsedArgs): ChmodCliParse
  {
    var state := DecodeOptions(p.options, InitialDecodeState());
    var operands :=
      if |state.modeOptionParts| > 0 then
        [JoinModeOptionParts(state.modeOptionParts)] + p.positionals
      else
        p.positionals;
    ChmodCliParse(
      state.recursive,
      state.verbose,
      state.changes,
      state.silent,
      state.preserveRoot,
      state.dereferenceMode,
      state.traversalMode,
      state.seenReference,
      state.referenceFile,
      state.seenHelp,
      state.seenVersion,
      state.helpTokenIndex,
      state.versionTokenIndex,
      operands,
      |state.modeOptionParts| > 0
    )
  }

  function Command(raw: ChmodCmdRaw): ChmodCmd
  {
    var mode :=
      if raw.seenHelp && (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex) then
        ModeHelp
      else if raw.seenVersion then
        ModeVersion
      else
        ModeRun;
    var modeExpr :=
      if mode == ModeRun && !raw.seenReference && |raw.operands| > 0 then
        raw.operands[0]
      else
        "";
    var files :=
      if mode != ModeRun then
        []
      else if raw.seenReference then
        raw.operands
      else if |raw.operands| > 0 then
        raw.operands[1..]
      else
        [];
    ChmodCmd(
      mode,
      modeExpr,
      files,
      raw.seenRecursive,
      raw.seenVerbose,
      raw.seenChanges,
      raw.seenSilent,
      raw.preserveRoot,
      raw.dereferenceMode,
      raw.traversalMode,
      raw.seenReference,
      raw.referenceFile,
      raw.diagnoseSurprises
    )
  }

  const CHMOD_MODE_BITS: bv32 := BenchWorld.ALL_MODE_BITS
  const S_ISUID: bv32 := 2048 as bv32
  const S_ISGID: bv32 := 1024 as bv32
  const S_ISVTX: bv32 := 512 as bv32
  const S_IRUSR: bv32 := 256 as bv32
  const S_IWUSR: bv32 := 128 as bv32
  const S_IXUSR: bv32 := BenchWorld.OWNER_EXECUTE_MODE_BIT
  const S_IRGRP: bv32 := 32 as bv32
  const S_IWGRP: bv32 := 16 as bv32
  const S_IXGRP: bv32 := 8 as bv32
  const S_IROTH: bv32 := 4 as bv32
  const S_IWOTH: bv32 := 2 as bv32
  const S_IXOTH: bv32 := 1 as bv32
  const S_IRWXU: bv32 := S_IRUSR | S_IWUSR | S_IXUSR
  const S_IRWXG: bv32 := S_IRGRP | S_IWGRP | S_IXGRP
  const S_IRWXO: bv32 := S_IROTH | S_IWOTH | S_IXOTH
  const S_IRWXUGO: bv32 := S_IRWXU | S_IRWXG | S_IRWXO
  const SPECIAL_BITS: bv32 := S_ISUID | S_ISGID | S_ISVTX
  const READ_MASK: bv32 := S_IRUSR | S_IRGRP | S_IROTH
  const WRITE_MASK: bv32 := S_IWUSR | S_IWGRP | S_IWOTH
  const EXEC_MASK: bv32 := S_IXUSR | S_IXGRP | S_IXOTH

  datatype ModeFlag = ModeOrdinary | ModeXIfAnyX | ModeCopyExisting

  datatype ModeChange = ModeChange(
    op: char,
    flag: ModeFlag,
    affected: bv32,
    value: bv32,
    mentioned: bv32
  )

  datatype ParseResult<T> = Parsed(value: T, next: nat) | Invalid
  datatype OctalParse = OctalParse(value: int, next: nat)
  datatype PermParse = PermParse(value: bv32, flag: ModeFlag, next: nat)

  function ModeIsOp(c: char): bool
  {
    c == '+' || c == '-' || c == '='
  }

  function ModeIsWhoChar(c: char): bool
  {
    c == 'u' || c == 'g' || c == 'o' || c == 'a'
  }

  function WhoMask(c: char): bv32
  {
    if c == 'u' then
      S_ISUID | S_IRWXU
    else if c == 'g' then
      S_ISGID | S_IRWXG
    else if c == 'o' then
      S_ISVTX | S_IRWXO
    else if c == 'a' then
      CHMOD_MODE_BITS
    else
      0 as bv32
  }

  function CopySourceMask(c: char): bv32
  {
    if c == 'u' then
      S_IRWXU
    else if c == 'g' then
      S_IRWXG
    else if c == 'o' then
      S_IRWXO
    else
      0 as bv32
  }

  function DefaultMentioned(affected: bv32, value: bv32): bv32
  {
    if affected != 0 as bv32 then
      affected & value
    else
      value
  }

  function FlagWithX(flag: ModeFlag): ModeFlag
  {
    if flag == ModeXIfAnyX then
      flag
    else
      ModeXIfAnyX
  }

  function ParseWhoFrom(expr: string, i: nat, acc: bv32): ParseResult<bv32>
    decreases |expr| - i
  {
    if i >= |expr| then
      Parsed(acc, i)
    else if ModeIsOp(expr[i]) then
      Parsed(acc, i)
    else if ModeIsWhoChar(expr[i]) then
      ParseWhoFrom(expr, i + 1, acc | WhoMask(expr[i]))
    else
      Invalid
  }

  function ParseWho(expr: string, i: nat): ParseResult<bv32>
  {
    ParseWhoFrom(expr, i, 0 as bv32)
  }

  function ParseOctalRun(expr: string, i: nat, acc: int): OctalParse
    decreases |expr| - i
  {
    if i >= |expr| || !BenchWorld.IsOctalDigit(expr[i]) then
      OctalParse(acc, i)
    else
      ParseOctalRun(expr, i + 1, acc * 8 + BenchWorld.CharToDigit(expr[i]))
  }

  function ParsePerms(expr: string, i: nat, value: bv32, flag: ModeFlag): PermParse
    decreases |expr| - i
  {
    if i >= |expr| then
      PermParse(value, flag, i)
    else if expr[i] == 'r' then
      ParsePerms(expr, i + 1, value | READ_MASK, flag)
    else if expr[i] == 'w' then
      ParsePerms(expr, i + 1, value | WRITE_MASK, flag)
    else if expr[i] == 'x' then
      ParsePerms(expr, i + 1, value | EXEC_MASK, flag)
    else if expr[i] == 'X' then
      ParsePerms(expr, i + 1, value, FlagWithX(flag))
    else if expr[i] == 's' then
      ParsePerms(expr, i + 1, value | (S_ISUID | S_ISGID), flag)
    else if expr[i] == 't' then
      ParsePerms(expr, i + 1, value | S_ISVTX, flag)
    else
      PermParse(value, flag, i)
  }

  function ParseOneChange(expr: string, i: nat, affected: bv32): ParseResult<ModeChange>
    decreases |expr| - i
  {
    if i >= |expr| || !ModeIsOp(expr[i]) then
      Invalid
    else
      var op := expr[i];
      var j := i + 1;
      if j >= |expr| then
        var value := 0 as bv32;
        var mentioned := DefaultMentioned(affected, value);
        Parsed(ModeChange(op, ModeOrdinary, affected, value, mentioned), j)
      else if BenchWorld.IsOctalDigit(expr[j]) then
        if affected != 0 as bv32 then
          Invalid
        else
          var octal := ParseOctalRun(expr, j, 0);
          if octal.value > 4095 then
            Invalid
          else if octal.next < |expr| && expr[octal.next] != ',' then
            Invalid
          else
            var value := BenchWorld.NormalizeMode(BenchWorld.ToBv32(octal.value));
            Parsed(
              ModeChange(op, ModeOrdinary, CHMOD_MODE_BITS, value, CHMOD_MODE_BITS),
              octal.next
            )
      else if expr[j] == 'u' || expr[j] == 'g' || expr[j] == 'o' then
        var value := CopySourceMask(expr[j]);
        var mentioned := DefaultMentioned(affected, value);
        Parsed(ModeChange(op, ModeCopyExisting, affected, value, mentioned), j + 1)
      else
        var perms := ParsePerms(expr, j, 0 as bv32, ModeOrdinary);
        var mentioned := DefaultMentioned(affected, perms.value);
        Parsed(ModeChange(op, perms.flag, affected, perms.value, mentioned), perms.next)
  }

  function ParseOpSeq(expr: string, i: nat, affected: bv32): ParseResult<seq<ModeChange>>
    decreases |expr| - i
  {
    if i >= |expr| || !ModeIsOp(expr[i]) then
      Invalid
    else
      match ParseOneChange(expr, i, affected)
      case Invalid => Invalid
      case Parsed(change, next) =>
        if next <= i then
          Invalid
        else if next < |expr| && ModeIsOp(expr[next]) then
          match ParseOpSeq(expr, next, affected)
          case Invalid => Invalid
          case Parsed(rest, finalNext) => Parsed([change] + rest, finalNext)
        else
          Parsed([change], next)
  }

  function ParseSymbolic(expr: string, i: nat): ParseResult<seq<ModeChange>>
    decreases |expr| - i
  {
    if i >= |expr| then
      Invalid
    else
      match ParseWho(expr, i)
      case Invalid => Invalid
      case Parsed(affected, next) =>
        match ParseOpSeq(expr, next, affected)
        case Invalid => Invalid
        case Parsed(changes, endIdx) =>
          if endIdx < i then
            Invalid
          else if endIdx < |expr| && expr[endIdx] == ',' then
            match ParseSymbolic(expr, endIdx + 1)
            case Invalid => Invalid
            case Parsed(rest, finalNext) => Parsed(changes + rest, finalNext)
          else if endIdx == |expr| then
            Parsed(changes, endIdx)
          else
            Invalid
  }

  function IsValidModeExpr(expr: string): bool
  {
    if |expr| == 0 then
      false
    else if BenchWorld.IsOctalDigit(expr[0]) then
      BenchWorld.AllOctalDigits(expr, 0) && BenchWorld.OctalValue(expr, 0, 0) <= 4095
    else
      match ParseSymbolic(expr, 0)
      case Invalid => false
      case Parsed(_, endIdx) => endIdx == |expr|
  }

  function LongTokenName(token: string): string
  {
    if |token| <= 2 then ""
    else token[2..LongTokenNameEnd(token, 2)]
  }

  function LongTokenNameEnd(token: string, i: nat): nat
    requires i <= |token|
    ensures i <= LongTokenNameEnd(token, i) <= |token|
    decreases |token| - i
  {
    if i == |token| || token[i] == '=' then i
    else LongTokenNameEnd(token, i + 1)
  }

  function HasPrefix(text: string, prefix: string): bool
  {
    |prefix| <= |text| && text[..|prefix|] == prefix
  }

  function ExactLongMatches(longs: seq<string>, name: string): seq<string>
    decreases |longs|
  {
    if |longs| == 0 then []
    else ((if longs[0] == name then [longs[0]] else []) +
          ExactLongMatches(longs[1..], name))
  }

  function PrefixLongMatches(longs: seq<string>, name: string): seq<string>
    decreases |longs|
  {
    if |longs| == 0 then []
    else ((if HasPrefix(longs[0], name) then [longs[0]] else []) +
          PrefixLongMatches(longs[1..], name))
  }

  function ExactOptionMatches(options: seq<CliTypes.OptionDecl>, name: string): seq<string>
    decreases |options|
  {
    if |options| == 0 then []
    else
      ExactLongMatches(options[0].longs, name) +
      ExactOptionMatches(options[1..], name)
  }

  function PrefixOptionMatches(options: seq<CliTypes.OptionDecl>, name: string): seq<string>
    decreases |options|
  {
    if |options| == 0 then []
    else
      PrefixLongMatches(options[0].longs, name) +
      PrefixOptionMatches(options[1..], name)
  }

  function LongOptionMatches(token: string): seq<string>
  {
    var name := LongTokenName(token);
    var exact := ExactOptionMatches(Options(), name);
    if |exact| > 0 then exact
    else PrefixOptionMatches(Options(), name)
  }

  function CanonicalLongOption(token: string): string
  {
    var matches := LongOptionMatches(token);
    if |matches| == 1 then matches[0] else LongTokenName(token)
  }

  function PossibilityText(matches: seq<string>): string
    decreases |matches|
  {
    if |matches| == 0 then ""
    else " '--" + matches[0] + "'" + PossibilityText(matches[1..])
  }

  function ShortIn(shorts: seq<char>, target: char): bool
    decreases |shorts|
  {
    |shorts| > 0 && (shorts[0] == target || ShortIn(shorts[1..], target))
  }

  function KnownShort(options: seq<CliTypes.OptionDecl>, target: char): bool
    decreases |options|
  {
    |options| > 0 &&
    (ShortIn(options[0].shorts, target) ||
     KnownShort(options[1..], target))
  }

  function InvalidShortIndex(token: string, i: nat): nat
    requires i <= |token|
    decreases |token| - i
  {
    if i == |token| || !KnownShort(Options(), token[i]) then i
    else InvalidShortIndex(token, i + 1)
  }

  function UnknownShortTemplate(): BenchWorld.Bytes
  {
    ['c', 'h', 'm', 'o', 'd', ':', ' ', 'i', 'n', 'v', 'a', 'l', 'i', 'd',
     ' ', 'o', 'p', 't', 'i', 'o', 'n', ' ', '-', '-', ' ', '\'', '\0',
     '\'', '\n', 'T', 'r', 'y', ' ', '\'', 'c', 'h', 'm', 'o', 'd', ' ',
     '-', '-', 'h', 'e', 'l', 'p', '\'', ' ', 'f', 'o', 'r', ' ', 'm',
     'o', 'r', 'e', ' ', 'i', 'n', 'f', 'o', 'r', 'm', 'a', 't', 'i',
     'o', 'n', '.', '\n']
  }

  function UnknownShortText(byte: BenchWorld.RawByte): BenchWorld.Bytes
  {
    UnknownShortTemplate()[26 := byte]
  }

  function ParseErrorText(e: CliTypes.ParseError): BenchWorld.Bytes
  {
    if e.kind == CliTypes.UnknownOption then
      if |e.rawToken| > 2 && e.rawToken[0] == '-' &&
         e.rawToken[1] == '-' then
        "chmod: unrecognized option '" + Utf8.Encode(e.rawToken) + "'\n" +
        "Try 'chmod --help' for more information.\n"
      else if |e.rawToken| > 1 && e.rawToken[0] == '-' then
        var invalid := InvalidShortIndex(e.rawToken, 1);
        var invalidChar :=
          if invalid < |e.rawToken| then e.rawToken[invalid]
          else e.rawToken[1];
        UnknownShortText(Utf8.EncodeChar(invalidChar)[0])
      else
        "chmod: invalid option\nTry 'chmod --help' for more information.\n"
    else if e.kind == CliTypes.MissingValue && |e.rawToken| > 2 &&
            e.rawToken[0] == '-' && e.rawToken[1] == '-' then
      "chmod: option '--" + Utf8.Encode(CanonicalLongOption(e.rawToken)) +
      "' requires an argument\n" +
      "Try 'chmod --help' for more information.\n"
    else if e.kind == CliTypes.UnexpectedValue && |e.rawToken| > 2 &&
            e.rawToken[0] == '-' && e.rawToken[1] == '-' then
      "chmod: option '--" + Utf8.Encode(CanonicalLongOption(e.rawToken)) +
      "' doesn't allow an argument\n" +
      "Try 'chmod --help' for more information.\n"
    else if e.kind == CliTypes.Ambiguous then
      "chmod: option '" + Utf8.Encode(e.rawToken) +
      "' is ambiguous; possibilities:" +
      Utf8.Encode(PossibilityText(LongOptionMatches(e.rawToken))) + "\n" +
      "Try 'chmod --help' for more information.\n"
    else
      "chmod: parse error at token '" + Utf8.Encode(e.rawToken) + "'\n"
  }

  method ChmodFormatParseError(e: CliTypes.ParseError)
    returns (b: BenchWorld.Bytes)
  {
    b := ParseErrorText(e);
  }

  method PlanParseFailure(
    e: CliTypes.ParseError,
    argv: seq<string>
  ) returns (plan: CliTypes.CliPlan<ChmodCmdRaw>)
    decreases *
  {
    var ok, raw := TryRecoverParseFailure(e, argv);
    if ok {
      plan := CliTypes.CliRun(raw);
    } else {
      var msg := ChmodFormatParseError(e);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }
  }
}
