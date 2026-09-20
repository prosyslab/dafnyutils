include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "BasenameSchema.dfy"
include "BasenameCore.dfy"
include "BasenameProof.dfy"
include "BasenameSpec.dfy"

module Basename {
  import BenchIO
  import BP = BasenameProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import BasenameSchema
  import Core = BasenameCore
  import BS = BasenameSpec

  class {:termination false} BasenameBenchmarkItem extends BenchItem.BenchmarkItemTwostate<BasenameSchema.BasenameCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "basename";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := BasenameSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := BasenameSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: BasenameSchema.BasenameCmdRaw)
    {
      raw := BasenameSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := BasenameSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<BasenameSchema.BasenameCmdRaw>)
      decreases *
    {
      plan := BasenameSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: BasenameSchema.BasenameCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures BS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      BP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
