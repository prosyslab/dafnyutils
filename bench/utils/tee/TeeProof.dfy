include "../../core/World.dfy"
include "../../core/IOContract.dfy"
include "TeeSchema.dfy"
include "TeeCore.dfy"
include "TeeSpec.dfy"

module TeeProof {
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = TeeSchema
  import Core = TeeCore
  import Spec = TeeSpec

  lemma CommandMatchesSpec(raw: Schema.TeeCmdRaw)
    ensures Core.Command(raw) == Spec.CommandSpec(raw)
  {
  }

  lemma WriteOneSummaryFieldsImpliesSpec(
    append: bool,
    path: BenchWorld.Path,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  )
    requires Core.WriteOneSummaryFields(append, path, input, preFs, preNow, fs2, stderr, exit)
    ensures Spec.WriteOneSpecFields(append, path, input, preFs, preNow, fs2, stderr, exit)
  {
    reveal Spec.WriteOneSpecFields();
    match IOContract.ReadFileResultFields(preFs, path)
    case Ok(_) =>
    case Err(err) =>
  }

  lemma EmptyWriteOutputsSummary(
    append: bool,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  )
    requires Core.WriteOutputsSummaryFields(
               append, [], input, preFs, preNow, fs2, stderr, exit
             )
    ensures fs2 == preFs
    ensures stderr == []
    ensures exit == 0
  {
    reveal Core.WriteOutputsSummaryFields();
  }

  lemma SplitWriteOutputsSummary(
    append: bool,
    outputs: seq<BenchWorld.Path>,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  ) returns (
      prefixFs: BenchWorld.FileSystem,
      prefixErr: BenchWorld.Bytes,
      prefixExit: int,
      stepErr: BenchWorld.Bytes,
      stepExit: int
    )
    requires 0 < |outputs|
    requires Core.WriteOutputsSummaryFields(
               append, outputs, input, preFs, preNow, fs2, stderr, exit
             )
    ensures Core.WriteOutputsSummaryFields(
              append, outputs[..|outputs| - 1], input, preFs, preNow,
              prefixFs, prefixErr, prefixExit
            )
    ensures Core.WriteOneSummaryFields(
              append, outputs[|outputs| - 1], input, prefixFs, preNow,
              fs2, stepErr, stepExit
            )
    ensures stderr == prefixErr + stepErr
    ensures exit == (if prefixExit == 0 && stepExit == 0 then 0 else 1)
  {
    reveal Core.WriteOutputsSummaryFields();
    prefixFs, prefixErr, prefixExit, stepErr, stepExit :|
      Core.WriteOutputsSummaryFields(
        append, outputs[..|outputs| - 1], input, preFs, preNow,
        prefixFs, prefixErr, prefixExit
      ) &&
      Core.WriteOneSummaryFields(
        append, outputs[|outputs| - 1], input, prefixFs, preNow,
        fs2, stepErr, stepExit
      ) &&
      stderr == prefixErr + stepErr &&
      exit == (if prefixExit == 0 && stepExit == 0 then 0 else 1);
  }

  lemma WriteCoreStepImpliesRelation(
    append: bool,
    path: BenchWorld.Path,
    input: BenchWorld.Bytes,
    preNow: int,
    before: Spec.WriteState,
    after: Spec.WriteState,
    stepErr: BenchWorld.Bytes,
    stepExit: int
  )
    requires Core.WriteOneSummaryFields(
               append, path, input, before.fs, preNow, after.fs, stepErr, stepExit
             )
    requires after.stderr == before.stderr + stepErr
    requires after.exit == (if before.exit == 0 && stepExit == 0 then 0 else 1)
    ensures Spec.WriteStepRelation(append, path, input, preNow, before, after)
  {
    WriteOneSummaryFieldsImpliesSpec(
      append, path, input, before.fs, preNow, after.fs, stepErr, stepExit
    );
    reveal Spec.WriteStepRelation();
  }

  lemma WriteOutputsWitnessImpliesSpec(
    append: bool,
    outputs: seq<BenchWorld.Path>,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int,
    states: seq<Spec.WriteState>
  )
    requires |states| == |outputs| + 1
    requires states[0] == Spec.WriteState(preFs, [], 0)
    requires states[|outputs|] == Spec.WriteState(fs2, stderr, exit)
    requires forall i {:trigger Spec.WriteStepRelation(append, outputs[i], input, preNow, states[i], states[i + 1])} ::
               0 <= i < |outputs| ==>
                 Spec.WriteStepRelation(append, outputs[i], input, preNow, states[i], states[i + 1])
    ensures Spec.WriteOutputsSpecFields(append, outputs, input, preFs, preNow, fs2, stderr, exit)
  {
    reveal Spec.WriteOutputsSpecFields();
  }

  lemma ExtendWriteStates(
    append: bool,
    outputs: seq<BenchWorld.Path>,
    input: BenchWorld.Bytes,
    preNow: int,
    prefixStates: seq<Spec.WriteState>,
    after: Spec.WriteState
  ) returns (states: seq<Spec.WriteState>)
    requires 0 < |outputs|
    requires |prefixStates| == |outputs|
    requires forall i {:trigger Spec.WriteStepRelation(append, outputs[i], input, preNow, prefixStates[i], prefixStates[i + 1])} ::
               0 <= i < |outputs| - 1 ==>
                 Spec.WriteStepRelation(append, outputs[i], input, preNow, prefixStates[i], prefixStates[i + 1])
    requires Spec.WriteStepRelation(
               append, outputs[|outputs| - 1], input, preNow,
               prefixStates[|outputs| - 1], after
             )
    ensures states == prefixStates + [after]
    ensures forall i {:trigger Spec.WriteStepRelation(append, outputs[i], input, preNow, states[i], states[i + 1])} ::
              0 <= i < |outputs| ==>
                Spec.WriteStepRelation(append, outputs[i], input, preNow, states[i], states[i + 1])
  {
    states := prefixStates + [after];
    forall i {:trigger Spec.WriteStepRelation(append, outputs[i], input, preNow, states[i], states[i + 1])} |
      0 <= i < |outputs|
      ensures Spec.WriteStepRelation(append, outputs[i], input, preNow, states[i], states[i + 1])
    {
      if i == |outputs| - 1 {
        assert states[i] == prefixStates[i];
        assert states[i + 1] == after;
      } else {
        assert states[i] == prefixStates[i];
        assert states[i + 1] == prefixStates[i + 1];
      }
    }
  }

  lemma {:vcs_split_on_every_assert} WriteOutputsSummaryFieldsImpliesSpec(
    append: bool,
    outputs: seq<BenchWorld.Path>,
    input: BenchWorld.Bytes,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    stderr: BenchWorld.Bytes,
    exit: int
  ) returns (states: seq<Spec.WriteState>)
    requires Core.WriteOutputsSummaryFields(append, outputs, input, preFs, preNow, fs2, stderr, exit)
    ensures |states| == |outputs| + 1
    ensures states[0] == Spec.WriteState(preFs, [], 0)
    ensures states[|outputs|] == Spec.WriteState(fs2, stderr, exit)
    ensures forall i {:trigger Spec.WriteStepRelation(append, outputs[i], input, preNow, states[i], states[i + 1])} ::
              0 <= i < |outputs| ==>
                Spec.WriteStepRelation(append, outputs[i], input, preNow, states[i], states[i + 1])
    ensures Spec.WriteOutputsSpecFields(append, outputs, input, preFs, preNow, fs2, stderr, exit)
    decreases |outputs|
  {
    if |outputs| == 0 {
      EmptyWriteOutputsSummary(append, input, preFs, preNow, fs2, stderr, exit);
      states := [Spec.WriteState(preFs, [], 0)];
      WriteOutputsWitnessImpliesSpec(append, outputs, input, preFs, preNow, fs2, stderr, exit, states);
    } else {
      var prefixFs, prefixErr, prefixExit, stepErr, stepExit :=
        SplitWriteOutputsSummary(
          append, outputs, input, preFs, preNow, fs2, stderr, exit
        );
      var prefixStates := WriteOutputsSummaryFieldsImpliesSpec(
        append, outputs[..|outputs| - 1], input, preFs, preNow,
        prefixFs, prefixErr, prefixExit
      );
      var before := Spec.WriteState(prefixFs, prefixErr, prefixExit);
      var after := Spec.WriteState(fs2, stderr, exit);
      assert prefixStates[|outputs| - 1] == before;
      WriteCoreStepImpliesRelation(
        append, outputs[|outputs| - 1], input, preNow,
        before, after, stepErr, stepExit
      );
      forall i | 0 <= i < |outputs| - 1
        ensures Spec.WriteStepRelation(
          append, outputs[i], input, preNow, prefixStates[i], prefixStates[i + 1]
        )
      {
        assert outputs[..|outputs| - 1][i] == outputs[i];
      }
      states := ExtendWriteStates(append, outputs, input, preNow, prefixStates, after);
      WriteOutputsWitnessImpliesSpec(append, outputs, input, preFs, preNow, fs2, stderr, exit, states);
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.TeeCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    CommandMatchesSpec(raw);
    var cmd := Core.Command(raw);
    if cmd.mode == Schema.ModeRun {
      var errOut: BenchWorld.Bytes, writeExit: int :|
        Core.WriteOutputsSummaryFields(cmd.append, cmd.outputs, old(io.stdin()), old(io.fs()), old(io.now()), io.fs(), errOut, writeExit) &&
        io.stdin() == IOContract.AfterReadStdinFields(old(io.stdin())) &&
        io.stdout() == old(io.stdout()) + old(io.stdin()) &&
        io.stderr() == old(io.stderr()) + errOut &&
        exit == writeExit;
      var states := WriteOutputsSummaryFieldsImpliesSpec(cmd.append, cmd.outputs, old(io.stdin()), old(io.fs()), old(io.now()), io.fs(), errOut, writeExit);
    }
  }
}
