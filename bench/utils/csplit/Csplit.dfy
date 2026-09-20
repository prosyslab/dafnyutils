include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "CsplitSchema.dfy"
include "CsplitCore.dfy"
include "CsplitSpec.dfy"
include "CsplitProof.dfy"

module Csplit {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import S = CsplitSchema
  import Core = CsplitCore
  import CS = CsplitSpec
  import Proof = CsplitProof

  class {:termination false} CsplitBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.CsplitCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "csplit";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.CsplitCmdRaw)
    {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := S.CsplitFormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<S.CsplitCmdRaw>)
      decreases *
    {
      plan := S.PlanParseFailure(err, argv);
    }

    method PlanParsed(parsed: CliTypes.ParsedArgs) returns (plan: CliTypes.CliPlan<S.CsplitCmdRaw>)
      decreases *
    {
      plan := S.PlanParsed(parsed);
    }

    method RunCore(raw: S.CsplitCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures CS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
