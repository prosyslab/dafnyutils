include "../Spec/PathchkSpec.dfy"
include "../Impl/PathchkCore.dfy"

module PathchkProof {
  import BenchIO
  import BenchWorld
  import Schema = PathchkSchema
  import Core = PathchkCore
  import Spec = PathchkSpec

  lemma PreparedSummaryImpliesPreparedSpec(
    raw: Schema.PathchkCmdRaw, exit: int,
    plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes
  )
    requires Core.PreparedSummary(raw, exit, plannedStdout, plannedStderr)
    ensures Spec.PreparedSpec(raw, exit, plannedStdout, plannedStderr)
  { reveal Core.PreparedSummary(); }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.PathchkCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    if Spec.AllowedInput(raw) {
      var output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int :|
        Core.PreparedSummary(raw, normalExit, output, diagnostics) &&
        Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                            io.trustedStreams(), output, diagnostics, normalExit, exit);
      PreparedSummaryImpliesPreparedSpec(raw, normalExit, output, diagnostics);
    }
  }
}
