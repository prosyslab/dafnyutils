include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "FactorSchema.dfy"
include "FactorCore.dfy"
include "FactorSpec.dfy"
include "FactorProof.dfy"

module Factor {
  import BenchIO
  import FP = FactorProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import FactorSchema
  import Core = FactorCore
  import FS = FactorSpec

  class {:termination false} FactorBenchmarkItem extends BenchItem.BenchmarkItemTwostate<FactorSchema.FactorCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "factor";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := FactorSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := FactorSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: FactorSchema.FactorCmdRaw)
    {
      raw := FactorSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := FactorSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<FactorSchema.FactorCmdRaw>)
      decreases *
    {
      plan := FactorSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: FactorSchema.FactorCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures FS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      FP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
