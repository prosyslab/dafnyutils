include "../../core/World.dfy"
include "../../core/IO.dfy"
include "PwdSchema.dfy"
include "PwdCore.dfy"
include "PwdSpec.dfy"

module PwdProof {
  import BenchIO
  import BenchWorld
  import Schema = PwdSchema
  import Core = PwdCore
  import Spec = PwdSpec

  lemma NoUnsafeComponentIffAllSafe(segs: seq<string>, i: nat)
    requires i <= |segs|
    ensures !Core.ContainsUnsafeComponent(segs, i) ==
            (forall j :: i <= j < |segs| ==>
                           segs[j] != "." && segs[j] != "..")
    decreases |segs| - i
  {
    if i < |segs| &&
       segs[i] != "." &&
       segs[i] != ".."
    {
      NoUnsafeComponentIffAllSafe(segs, i + 1);
    }
  }

  lemma SelectedCurrentDirFieldsSatisfiesRelation(
    raw: Schema.PwdCmdRaw,
    cwd: string,
    env: map<string, string>
  )
    ensures Spec.SelectedDirectoryRelation(
              raw,
              cwd,
              env,
              Core.SelectedCurrentDirFields(raw, cwd, env)
            )
  {
    if Core.UseLogicalFields(raw, env) && "PWD" in env {
      var pwd := env["PWD"];
      var components :=
        BenchWorld.SplitSegments(BenchWorld.StripLeadingSlash(pwd), 0, 0);
      NoUnsafeComponentIffAllSafe(components, 0);
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.PwdCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    if Core.HelpSelected(raw) {
    } else if Core.VersionSelected(raw) {
    } else {
      SelectedCurrentDirFieldsSatisfiesRelation(
        raw, old(io.cwd()), old(io.env())
      );
    }
  }
}
