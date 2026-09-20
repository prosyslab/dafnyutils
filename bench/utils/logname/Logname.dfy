include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "LognameSchema.dfy"
include "LognameCore.dfy"
include "LognameProof.dfy"
include "LognameSpec.dfy"

module Logname {
  import BenchIO
  import LP = LognameProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import LognameSchema
  import Core = LognameCore
  import LS = LognameSpec

  class {:termination false} LognameBenchmarkItem extends BenchItem.BenchmarkItemTwostate<LognameSchema.LognameCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "logname";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := LognameSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := LognameSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: LognameSchema.LognameCmdRaw)
    {
      raw := LognameSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := LognameSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<LognameSchema.LognameCmdRaw>)
      decreases *
    {
      plan := LognameSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: LognameSchema.LognameCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures LS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      LP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
