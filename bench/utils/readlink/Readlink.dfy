include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "ReadlinkSchema.dfy"
include "ReadlinkCore.dfy"
include "ReadlinkProof.dfy"
include "ReadlinkSpec.dfy"

module Readlink {
  import BenchIO
  import RP = ReadlinkProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import ReadlinkSchema
  import Core = ReadlinkCore
  import RS = ReadlinkSpec

  class {:termination false} ReadlinkBenchmarkItem extends BenchItem.BenchmarkItemTwostate<ReadlinkSchema.ReadlinkCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "readlink";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := ReadlinkSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := ReadlinkSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: ReadlinkSchema.ReadlinkCmdRaw)
    {
      raw := ReadlinkSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := ReadlinkSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<ReadlinkSchema.ReadlinkCmdRaw>)
      decreases *
    {
      plan := ReadlinkSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: ReadlinkSchema.ReadlinkCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures RS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      RP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
