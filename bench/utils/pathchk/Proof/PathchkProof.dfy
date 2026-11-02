include "../Spec/PathchkSpec.dfy"
include "../Impl/PathchkCore.dfy"

module PathchkProof {
  import BenchIO
  import Schema = PathchkSchema
  import Core = PathchkCore
  import Spec = PathchkSpec

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.PathchkCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    // TODO: prove this connection after replacing the false placeholder relations.
  }
}
