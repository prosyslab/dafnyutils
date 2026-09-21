include "../../core/BenchmarkItem.dfy"
include "{{CLASS_NAME}}Spec.dfy"
include "{{CLASS_NAME}}Core.dfy"
include "{{CLASS_NAME}}Proof.dfy"

module {{CLASS_NAME}} {
  import BenchIO
  import BenchWorld
  import BenchItem
  import CliTypes
  import S = {{CLASS_NAME}}Schema
  import Core = {{CLASS_NAME}}Core
  import Spec = {{CLASS_NAME}}Spec
  import Proof = {{CLASS_NAME}}Proof

  class {{CLASS_NAME}}BenchmarkItem extends BenchItem.BenchmarkItemTwostate<S.{{CLASS_NAME}}CmdRaw> {
    constructor() {}

    method Name() returns (name: string) {
      name := "{{TASK_ID}}";
    }

    method Schema() returns (schema: CliTypes.CliSchema) {
      schema := S.Schema();
    }

    method ParseConfig() returns (cfg: CliTypes.ParseConfig) {
      cfg := S.ParserConfig();
    }

    method Decode(parsed: CliTypes.ParsedArgs) returns (raw: S.{{CLASS_NAME}}CmdRaw) {
      raw := S.Decode(parsed);
    }

    method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes) {
      // TODO: implement and test GNU parse-error behavior, including early exits.
      assert false;
      msg := Spec.ParseErrorText(err);
    }

    method RunCore(raw: S.{{CLASS_NAME}}CmdRaw, io: BenchIO.IO) returns (exit: int)
      modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
      ensures Spec.Spec(raw, io, exit)
    {
      exit := Core.RunCore(raw, io);
      Proof.CoreSummaryImpliesSpec(raw, io, exit);
    }
  }
}
