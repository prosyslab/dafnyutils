include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "PrintenvSchema.dfy"
include "PrintenvCore.dfy"
include "PrintenvProof.dfy"
include "PrintenvSpec.dfy"

module Printenv {
  import BenchIO
  import PP = PrintenvProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import PrintenvSchema
  import Core = PrintenvCore
  import PS = PrintenvSpec

  class {:termination false} PrintenvBenchmarkItem extends BenchItem.BenchmarkItemTwostate<PrintenvSchema.PrintenvCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "printenv";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := PrintenvSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := PrintenvSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: PrintenvSchema.PrintenvCmdRaw)
    {
      raw := PrintenvSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := PrintenvSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<PrintenvSchema.PrintenvCmdRaw>)
      decreases *
    {
      plan := PrintenvSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: PrintenvSchema.PrintenvCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion
      ensures PS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      PP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
