include "SortSpec.dfy"
include "SortCore.dfy"

module SortProof {
  import BenchIO
  import Schema = SortSchema
  import Core = SortCore
  import Spec = SortSpec

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.SortCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    // TODO: prove this connection after replacing the false placeholder relations.
  }
}
