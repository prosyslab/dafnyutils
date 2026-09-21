include "{{CLASS_NAME}}Spec.dfy"
include "{{CLASS_NAME}}Core.dfy"

module {{CLASS_NAME}}Proof {
  import BenchIO
  import Schema = {{CLASS_NAME}}Schema
  import Core = {{CLASS_NAME}}Core
  import Spec = {{CLASS_NAME}}Spec

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.{{CLASS_NAME}}CmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    // TODO: prove this connection after replacing the false placeholder relations.
  }
}
