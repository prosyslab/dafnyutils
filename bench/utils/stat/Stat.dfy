include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "StatSchema.dfy"
include "StatSpec.dfy"
include "StatCore.dfy"
include "StatProof.dfy"

module Stat {
  import BenchWorld
  import BenchIO
  import CliTypes
  import BenchItem
  import S = StatSchema
  import Spec = StatSpec
  import Core = StatCore
  import Proof = StatProof

  class {:termination false} StatBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.StatCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "stat";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.StatCmdRaw)
    {
      raw := S.Decode(parsed);
    }

    method FormatParseError(error: CliTypes.ParseError) returns (message: BenchWorld.Bytes)
    {
      message := S.FormatParseError(error);
    }

    method PlanParseFailure(
      error: CliTypes.ParseError,
      argv: seq<string>
    ) returns (plan: CliTypes.CliPlan<S.StatCmdRaw>)
      decreases *
    {
      plan := S.PlanParseFailure(error, argv);
    }

    method RunCore(raw: S.StatCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
