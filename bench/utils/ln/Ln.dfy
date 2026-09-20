include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "LnSchema.dfy"
include "LnCore.dfy"
include "LnProof.dfy"
include "LnSpec.dfy"

module Ln {
  import BenchIO
  import LP = LnProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import LnSchema
  import Core = LnCore
  import LS = LnSpec

  class {:termination false} LnBenchmarkItem extends BenchItem.BenchmarkItemTwostate<LnSchema.LnCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "ln";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := LnSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := LnSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: LnSchema.LnCmdRaw)
    {
      raw := LnSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := LnSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<LnSchema.LnCmdRaw>)
      decreases *
    {
      plan := LnSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: LnSchema.LnCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
      ensures LS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      LP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
