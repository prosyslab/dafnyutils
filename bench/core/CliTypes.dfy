include "World.dfy"

module {:verify false} CliTypes {
  import BW = BenchWorld
  datatype OptionArity = NoArg | ReqArg | OptArg
  datatype ArgOrderPolicy = GNU_Permute | POSIX_StopAtFirst

  datatype OptionDecl = OptionDecl(
    key: string,
    shorts: seq<char>,
    longs: seq<string>,
    arity: OptionArity
  )

  datatype CliSchema = CliSchema(
    options: seq<OptionDecl>,
    supportsDoubleDash: bool
  )

  datatype ParseConfig = ParseConfig(
    order: ArgOrderPolicy,
    allowBundling: bool,
    allowLongAbbrev: bool,
    treatDashAsOperand: bool
  )

  datatype OptionSource = Short(ch: char) | Long(name: string)
  datatype OptionalString = None | Some(value: string)

  datatype OptOccurrence = OptOccurrence(
    key: string,
    src: OptionSource,
    value: OptionalString,
    tokenIndex: int,
    rawToken: string
  )

  datatype ParsedArgs = ParsedArgs(
    prog: string,
    options: seq<OptOccurrence>,
    positionals: seq<string>,
    sawDoubleDash: bool
  )

  datatype ParseErrorKind = UnknownOption | MissingValue | UnexpectedValue | Ambiguous
  datatype ParseError = ParseError(kind: ParseErrorKind, tokenIndex: int, rawToken: string)
  datatype ParseResult = ParseSuccess(parsed: ParsedArgs) | ParseFailure(error: ParseError)
  datatype PriorRequest = RequestNone | RequestHelp | RequestVersion
  datatype CliPlan<CmdRaw> =
    | CliRun(raw: CmdRaw)
    | CliEarlyExit(exit: int, stdout: BW.RawBytes, stderr: BW.RawBytes)

  function PriorHelpVersionRequestFrom(
    argv: seq<string>,
    i: nat,
    limit: int,
    seenHelp: bool,
    seenVersion: bool,
    helpTokenIndex: int,
    versionTokenIndex: int
  ): PriorRequest
    requires i <= |argv|
    decreases |argv| - i
  {
    if i == |argv| || limit <= i then
      if seenHelp && (!seenVersion || helpTokenIndex <= versionTokenIndex) then
        RequestHelp
      else if seenVersion then
        RequestVersion
      else
        RequestNone
    else if argv[i] == "--help" then
      PriorHelpVersionRequestFrom(
        argv,
        i + 1,
        limit,
        true,
        seenVersion,
        if helpTokenIndex == -1 then i as int else helpTokenIndex,
        versionTokenIndex
      )
    else if argv[i] == "--version" then
      PriorHelpVersionRequestFrom(
        argv,
        i + 1,
        limit,
        seenHelp,
        true,
        helpTokenIndex,
        if versionTokenIndex == -1 then i as int else versionTokenIndex
      )
    else
      PriorHelpVersionRequestFrom(
        argv, i + 1, limit, seenHelp, seenVersion, helpTokenIndex, versionTokenIndex
      )
  }

  function PriorHelpVersionRequest(argv: seq<string>, limit: int): PriorRequest
  {
    PriorHelpVersionRequestFrom(argv, 0, limit, false, false, -1, -1)
  }
}
