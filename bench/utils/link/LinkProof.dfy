include "LinkSpec.dfy"
include "LinkCore.dfy"

module LinkProof {
  import BenchIO
  import Schema = LinkSchema
  import Core = LinkCore
  import Spec = LinkSpec

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.LinkCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    
  }
}
