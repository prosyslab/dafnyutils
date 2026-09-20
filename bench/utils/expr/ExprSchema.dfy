include "../../core/Utf8.dfy"
include "../../core/World.dfy"
include "../../core/CliTypes.dfy"

module ExprSchema {
  import Utf8 = Utf8Semantics
  import BenchWorld
  import CliTypes

  datatype ExprCmdRaw = ExprCmdRaw(args: seq<string>)

  method Schema() returns (s: CliTypes.CliSchema)
  {
    s := CliTypes.CliSchema([], false);
  }

  method ParserConfig() returns (cfg: CliTypes.ParseConfig)
  {
    cfg := CliTypes.ParseConfig(CliTypes.POSIX_StopAtFirst, false, false, true);
  }

  method Decode(p: CliTypes.ParsedArgs) returns (raw: ExprCmdRaw)
  {
    raw := ExprCmdRaw(p.positionals);
  }

  function ParseErrorText(e: CliTypes.ParseError): string
  {
    "expr: parse error\n"
  }

  method ExprFormatParseError(e: CliTypes.ParseError) returns (b: BenchWorld.Bytes)
  {
    b := Utf8.Encode(ParseErrorText(e));
  }
}
