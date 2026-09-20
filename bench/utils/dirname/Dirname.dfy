include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "DirnameSchema.dfy"
include "DirnameCore.dfy"
include "DirnameProof.dfy"
include "DirnameSpec.dfy"

module Dirname {
  import BenchIO
  import DP = DirnameProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import DirnameSchema
  import Core = DirnameCore
  import DS = DirnameSpec

  class {:termination false} DirnameBenchmarkItem extends BenchItem.BenchmarkItemTwostate<DirnameSchema.DirnameCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "dirname";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := DirnameSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := DirnameSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: DirnameSchema.DirnameCmdRaw)
    {
      raw := DirnameSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := DirnameSchema.DirnameFormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<DirnameSchema.DirnameCmdRaw>)
      decreases *
    {
      var msg := DirnameSchema.DirnameFormatParseError(err);
      plan := CliTypes.CliEarlyExit(1, [], msg);
    }

    method RunCore(raw: DirnameSchema.DirnameCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures DS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      DP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
