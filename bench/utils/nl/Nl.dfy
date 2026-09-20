include "../../core/World.dfy"
include "../../core/CliTypes.dfy"
include "../../core/BenchmarkItem.dfy"
include "NlSchema.dfy"
include "NlCore.dfy"
include "NlSpec.dfy"
include "NlProof.dfy"

module Nl {
  import BenchIO
  import BenchWorld
  import CliTypes
  import BenchItem
  import NlSchema
  import Exec = NlCore
  import NS = NlSpec
  import Proof = NlProof

  class {:termination false} NlBenchmarkItem extends BenchItem.BenchmarkItemTwostate<NlSchema.NlCmdRaw> {
    constructor()
    {
    }

    method Name() returns (name: string)
    {
      name := "nl";
    }

    method Schema() returns (schema: CliTypes.CliSchema)
    {
      schema := NlSchema.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig)
    {
      cfg := NlSchema.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: NlSchema.NlCmdRaw)
    {
      raw := NlSchema.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    {
      msg := NlSchema.FormatParseError(err);
    }

    method PlanParseFailure(err: CliTypes.ParseError, argv: seq<string>) returns (plan: CliTypes.CliPlan<NlSchema.NlCmdRaw>)
      decreases *
    {
      plan := NlSchema.PlanParseFailure(err, argv);
    }

    method RunCore(raw: NlSchema.NlCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures NS.Spec(raw, io, exit)
      decreases *
    {
      ghost var readResults: seq<BenchWorld.Result<BenchWorld.Bytes>>;
      ghost var inputFragments: seq<BenchWorld.Bytes>;
      ghost var combined: BenchWorld.Bytes;
      ghost var inputCuts: seq<nat>;
      ghost var errorFragments: seq<BenchWorld.Bytes>;
      ghost var errorOutput: BenchWorld.Bytes;
      ghost var errorCuts: seq<nat>;
      ghost var hadError: bool;
      ghost var hasDelimiter: bool;
      ghost var outputPart: BenchWorld.Bytes;
      exit, readResults, inputFragments, combined, inputCuts,
      errorFragments, errorOutput, errorCuts, hadError, hasDelimiter,
      outputPart := Exec.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(
        raw, io, exit, readResults, inputFragments, combined, inputCuts,
        errorFragments, errorOutput, errorCuts, hadError, hasDelimiter,
        outputPart
      );
    }
  }
}
