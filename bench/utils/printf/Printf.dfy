include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "PrintfSchema.dfy"
include "PrintfCore.dfy"
include "PrintfSpec.dfy"
include "PrintfProof.dfy"

module Printf {
  import BenchIO
  import PP = PrintfProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import PrintfSchema
  import Core = PrintfCore
  import PS = PrintfSpec

  class {:termination false} PrintfBenchmarkItem extends BenchItem.BenchmarkItemTwostate<PrintfSchema.PrintfCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "printf";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := PrintfSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := PrintfSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: PrintfSchema.PrintfCmdRaw)
    {
      raw := PrintfSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := PrintfSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<PrintfSchema.PrintfCmdRaw>)
      decreases *
    {
      plan := PrintfSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: PrintfSchema.PrintfCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdoutRegion, io.stderrRegion
      ensures PS.Spec(raw, io, exit)
      decreases *
    {
      exit := Core.RunCore(raw, io);
      PP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
