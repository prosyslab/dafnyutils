include "CliTypes.dfy"
include "CliModel.dfy"

module CliExtern {
  import opened CliTypes
  import CliModel

  class Cli {
    static method Parse(
      argv: seq<string>,
      schema: CliSchema,
      cfg: ParseConfig
    ) returns (res: ParseResult)
      ensures res == CliModel.ParseValue(argv, schema, cfg)
    {
      res := CliModel.ParseValue(argv, schema, cfg);
    }

    static method ParsePortable(
      argv: seq<string>,
      schema: CliSchema,
      cfg: ParseConfig
    ) returns (res: ParseResult)
      ensures res == CliModel.ParseValue(argv, schema, cfg)
    {
      res := CliModel.ParseValue(argv, schema, cfg);
    }
  }
}
