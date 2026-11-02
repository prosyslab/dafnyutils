include "CliSupport.dfy"
include "../Spec/PathchkSpec.dfy"
include "../Impl/PathchkCore.dfy"
include "../Proof/PathchkProof.dfy"

module Pathchk {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import S = PathchkSchema
  import Core = PathchkCore
  import Spec = PathchkSpec
  import Proof = PathchkProof

  class PathchkBenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.PathchkCmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "pathchk";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.PathchkCmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      // TODO: implement and test command-line parse errors, including early exits.
      assert false;
      msg := Spec.ParseErrorText(err);
    }

    method RunCore(raw: S.PathchkCmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
