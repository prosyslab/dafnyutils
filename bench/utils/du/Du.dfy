include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "DuSchema.dfy"
include "DuCore.dfy"
include "DuProof.dfy"
include "DuSpec.dfy"

module Du {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import S = DuSchema
  import Core = DuCore
  import DS = DuSpec
  import Proof = DuProof

  class {:termination false} DuBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.DuCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "du";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.DuCmdRaw)
    {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := S.ParseErrorMessage(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<S.DuCmdRaw>)
      decreases *
    {
      var msg := S.ParseErrorMessage(err);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: S.DuCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures DS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
