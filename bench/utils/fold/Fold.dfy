include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "FoldSchema.dfy"
include "FoldCore.dfy"
include "FoldSpec.dfy"
include "FoldProof.dfy"

module Fold {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import S = FoldSchema
  import Core = FoldCore
  import ES = FoldSpec
  import Proof = FoldProof

  class {:termination false} FoldBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.FoldCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "fold";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.FoldCmdRaw)
    {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := S.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<S.FoldCmdRaw>)
      decreases *
    {
      var failure := S.PlanParseFailure(err, argv);
      match failure
      case FoldRun(raw) =>
        plan := CliTypes.CliRun(raw);
      case FoldParseError(error) =>
        plan := S.PlanError(error);
    }

    method RunCore(raw: S.FoldCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures ES.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
