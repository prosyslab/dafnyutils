include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "CommSchema.dfy"
include "CommCore.dfy"
include "CommSpec.dfy"
include "CommProof.dfy"

module Comm {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import S = CommSchema
  import Core = CommCore
  import CS = CommSpec
  import Proof = CommProof

  class {:termination false} CommBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.CommCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "comm";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.CommCmdRaw)
    {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := S.CommFormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<S.CommCmdRaw>)
      decreases *
    {
      plan := S.PlanParseFailure(err, argv);
    }

    method RunCore(raw: S.CommCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures CS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
