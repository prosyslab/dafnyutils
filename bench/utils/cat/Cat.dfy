include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "CatSchema.dfy"
include "CatCore.dfy"
include "CatSpec.dfy"
include "CatProof.dfy"

module Cat {
  import BenchIO
  import CP = CatProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import CatSchema
  import Exec = CatCore
  import CS = CatSpec

  class {:termination false} CatBenchmarkItem extends BenchItem.BenchmarkItemTwostate<CatSchema.CatCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "cat";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := CatSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := CatSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: CatSchema.CatCmdRaw)
    {
      raw := CatSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := CatSchema.CatFormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<CatSchema.CatCmdRaw>)
      decreases *
    {
      plan := CatSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: CatSchema.CatCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures CS.Spec(raw, io, exit)
      decreases *
    {
      exit := Exec.RunCore(raw, io);
      CP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
