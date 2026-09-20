include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "FalseSchema.dfy"
include "FalseCore.dfy"
include "FalseSpec.dfy"
include "FalseProof.dfy"

module False {
  import BenchIO
  import FP = FalseProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import FalseSchema
  import Core = FalseCore
  import FS = FalseSpec

  class {:termination false} FalseBenchmarkItem extends BenchItem.BenchmarkItemTwostate<FalseSchema.FalseCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "false";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := FalseSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := FalseSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: FalseSchema.FalseCmdRaw)
    {
      raw := FalseSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := [];
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<FalseSchema.FalseCmdRaw>)
      decreases *
    {
      plan := FalseSchema.PlanParseFailure(err, argv);
    }

    method PlanArgv(argv: seq<string>) returns (plan: CliTypes.CliPlan<FalseSchema.FalseCmdRaw>)
      decreases *
    {
      var raw := FalseSchema.FromArgv(argv);
      plan := CliTypes.CliRun(raw);
    }

    method RunCore(raw: FalseSchema.FalseCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion
      ensures FS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      FP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
