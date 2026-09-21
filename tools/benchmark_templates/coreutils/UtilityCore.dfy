include "../../core/IO.dfy"
include "{{CLASS_NAME}}Schema.dfy"

module {{CLASS_NAME}}Core {
  import BenchIO
  import Schema = {{CLASS_NAME}}Schema

  twostate predicate CoreSummary(raw: Schema.{{CLASS_NAME}}CmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdinRegion, io.stdoutRegion, io.stderrRegion
  {
    // TODO: state what the implementation establishes.
    false
  }

  method RunCore(raw: Schema.{{CLASS_NAME}}CmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    // TODO: implement the agreed behavior and prove CoreSummary.
    assert false;
    exit := 1;
  }
}
