include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "PasteSchema.dfy"
include "PasteCore.dfy"
include "PasteSpec.dfy"
include "PasteProof.dfy"

module Paste {
  import BenchIO
  import PP = PasteProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import PasteSchema
  import Exec = PasteCore
  import PS = PasteSpec

  class {:termination false} PasteBenchmarkItem extends BenchItem.BenchmarkItemTwostate<PasteSchema.PasteCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "paste";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := PasteSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := PasteSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: PasteSchema.PasteCmdRaw)
    {
      raw := PasteSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := PasteSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<PasteSchema.PasteCmdRaw>)
      decreases *
    {
      plan := PasteSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: PasteSchema.PasteCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures PS.Spec(raw, io, exit)
      decreases *
    {
      exit := Exec.RunCore(raw, io);
      PP.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
