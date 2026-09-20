include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "ChmodSchema.dfy"
include "ChmodCore.dfy"
include "ChmodProof.dfy"
include "ChmodSpec.dfy"
include "ChmodRecursiveSpec.dfy"
include "ChmodRecursiveRuntime.dfy"
include "ChmodRecursiveProof.dfy"

module Chmod {
  import BenchIO
  import CP = ChmodProof
  import BenchWorld
  import CliTypes
  import BenchItem
  import ChmodSchema
  import Core = ChmodCore
  import CS = ChmodSpec
  import RecursiveSpec = ChmodRecursiveSpec
  import RecursiveRuntime = ChmodRecursiveRuntime
  import RecursiveProof = ChmodRecursiveProof

  class {:termination false} ChmodBenchmarkItem extends BenchItem.BenchmarkItemTwostate<ChmodSchema.ChmodCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "chmod";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := ChmodSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := ChmodSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: ChmodSchema.ChmodCmdRaw)
    {
      raw := ChmodSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := ChmodSchema.ChmodFormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<ChmodSchema.ChmodCmdRaw>)
      decreases *
    {
      plan := ChmodSchema.PlanParseFailure(err, argv);
    }

    predicate ExternalDomain(raw: ChmodSchema.ChmodCmdRaw)
    {
      CS.SpecExternalDomain(raw)
    }

    method RunCore(raw: ChmodSchema.ChmodCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.dirHandlesRegion
      ensures RecursiveSpec.Spec(raw, io, exit)
      decreases *
    {
      if ChmodSchema.Command(raw).recursive {
        exit := RecursiveRuntime.RunRecursiveCore(raw, io);
        RecursiveProof.RecursiveCoreSummaryImpliesSpec(raw, io, exit);
      } else {
        exit := Core.RunCore(raw, io);
        CP.CoreSummaryImpliesSpec(raw, io, exit);
      }
    }
  }

  method RunCli(argv: seq<string>, io: BenchIO.IO) returns (exit: int)
    modifies io.Footprint()
    decreases *
  {
    var item := new ChmodBenchmarkItem();
    exit := BenchItem.RunMain(item, argv, io);
  }
}
