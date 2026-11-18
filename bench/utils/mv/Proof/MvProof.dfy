include "../Spec/MvPathSpec.dfy"
include "../Spec/MvSpec.dfy"
include "../../../core/World.dfy"
include "../../../core/IOContract.dfy"
include "MvPathProof.dfy"
include "../Spec/MvSchema.dfy"
include "../Impl/MvCore.dfy"

module MvProof {
  import StateModel = MvTransitionModel
  import Result = Results
  import BenchIO
  import IOContract
  import BW = BenchWorld
  import BasenameSpec = MvPathSpec
  import PathProof = MvPathProof
  import DirnameSpec = MvPathSpec
  import Schema = MvSchema
  import Core = MvCore
  import Spec = MvSpec

  lemma {:induction false} BatchTailWitness(
    sources: seq<string>, directory: string, cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem, cwd: BW.Path, afterFs: BW.FileSystem, outcome: Spec.MoveOutcome,
    states: seq<BW.FileSystem>, outcomes: seq<Spec.MoveOutcome>, outputs: seq<BW.Bytes>, errors: seq<BW.Bytes>
  ) returns (rest: Spec.MoveOutcome)
    requires |sources| > 0
    requires StateModel.ValueBatchMoveWitnessRelation(
               sources, directory, cmd, beforeFs, cwd, afterFs,
               outcome.failed, outcome.stdoutFragment, outcome.stderrFragment, states, outcomes, outputs, errors)
    ensures |states| == |sources| + 1 && |outcomes| == |sources|
    ensures |outputs| == |sources| && |errors| == |sources|
    ensures StateModel.ValueMoveEffectRelation(
              Spec.NormalizeSourceSpec(sources[0], cmd.stripTrailingSlashes),
              Spec.TargetInDirectorySpec(directory, Spec.NormalizeSourceSpec(sources[0], cmd.stripTrailingSlashes)),
              cmd, beforeFs, cwd, states[1], outcomes[0])
    ensures StateModel.ValueBatchMoveWitnessRelation(
              sources[1..], directory, cmd, states[1], cwd, afterFs,
              rest.failed, rest.stdoutFragment, rest.stderrFragment,
              states[1..], outcomes[1..], outputs[1..], errors[1..])
    ensures outcome == Spec.JoinOutcomes(outcomes[0], rest)
  {
    hide *;
    reveal StateModel.ValueBatchMoveWitnessRelation(), Spec.ConcatenateFragments(), Spec.JoinOutcomes();
    var tail := outcomes[1..];
    rest := Spec.MoveOutcome(Spec.ConcatenateFragments(outputs[1..]), Spec.ConcatenateFragments(errors[1..]),
                             exists i: nat | i < |tail| :: tail[i].failed);
    assert states[0] == beforeFs;
    assert outputs[0] == outcomes[0].stdoutFragment && errors[0] == outcomes[0].stderrFragment;
    assert outcome.failed == (outcomes[0].failed || rest.failed) by {
      if outcome.failed {
        var i: nat :| i < |outcomes| && outcomes[i].failed;
        if i > 0 {
          assert tail[i - 1] == outcomes[i];
        }
      } else if rest.failed {
        var i: nat :| i < |tail| && tail[i].failed;
        assert outcomes[i + 1] == tail[i];
      }
    }
    var tailStates := states[1..];
    var tailOutputs := outputs[1..];
    var tailErrors := errors[1..];
    assert Spec.ConcatenateFragments(outputs) == outputs[0] + Spec.ConcatenateFragments(tailOutputs);
    assert Spec.ConcatenateFragments(errors) == errors[0] + Spec.ConcatenateFragments(tailErrors);
    assert outcome == Spec.JoinOutcomes(outcomes[0], rest);
    forall i: nat {:trigger tailStates[i]} | i < |sources[1..]|
      ensures StateModel.ValueMoveEffectRelation(
                Spec.NormalizeSourceSpec(sources[1..][i], cmd.stripTrailingSlashes),
                Spec.TargetInDirectorySpec(directory, Spec.NormalizeSourceSpec(sources[1..][i], cmd.stripTrailingSlashes)),
                cmd, tailStates[i], cwd, tailStates[i + 1], tail[i]) &&
              tailOutputs[i] == tail[i].stdoutFragment && tailErrors[i] == tail[i].stderrFragment
    {
      assert tailStates[i] == states[i + 1] && tailStates[i + 1] == states[i + 2];
    }
    assert tailStates[0] == states[1] && tailStates[|tailStates| - 1] == states[|states| - 1];
    BatchMoveComponentsImplyWitnessRelation(
      sources[1..], directory, cmd, states[1], cwd, afterFs, rest.failed, rest.stdoutFragment, rest.stderrFragment,
      tailStates, tail, tailOutputs, tailErrors);
  }

  lemma {:induction false} BatchMovesFromWitness(
    sources: seq<string>, directory: string, cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem, cwd: BW.Path, afterFs: BW.FileSystem, outcome: Spec.MoveOutcome,
    states: seq<BW.FileSystem>, outcomes: seq<Spec.MoveOutcome>, outputs: seq<BW.Bytes>, errors: seq<BW.Bytes>
  )
    requires StateModel.ValueBatchMoveWitnessRelation(
               sources, directory, cmd, beforeFs, cwd, afterFs,
               outcome.failed, outcome.stdoutFragment, outcome.stderrFragment, states, outcomes, outputs, errors)
    ensures Spec.BatchMovesAllowed(sources, directory, cmd, beforeFs, cwd, afterFs, outcome)
    decreases |sources|
  {
    hide *;
    reveal Spec.BatchMovesAllowed();
    if |sources| == 0 {
      reveal StateModel.ValueBatchMoveWitnessRelation();
    } else {
      var rest := BatchTailWitness(sources, directory, cmd, beforeFs, cwd, afterFs, outcome,
                                   states, outcomes, outputs, errors);
      BatchMovesFromWitness(sources[1..], directory, cmd, states[1], cwd, afterFs, rest,
                            states[1..], outcomes[1..], outputs[1..], errors[1..]);
      reveal StateModel.ValueMoveEffectRelation();
    }
  }

  ghost opaque predicate ObservedBatchIntervals(
    sources: seq<string>, directory: string, cmd: Schema.MvCmd, cwd: BW.Path,
    states: seq<BW.FileSystem>, outcomes: seq<Spec.MoveOutcome>,
    observations: Spec.NativeStatusInputs, firstStatus: nat, calls: seq<Spec.StatusCallEvidence>,
    bounds: seq<nat>
  )
  {
    |states| == |sources| + 1 && |outcomes| == |sources| &&
    |bounds| == |sources| + 1 && bounds[0] == firstStatus && bounds[|sources|] == firstStatus + |calls| &&
    (forall i: nat {:trigger bounds[i]} | i < |sources| ::
       firstStatus <= bounds[i] <= bounds[i + 1] <= firstStatus + |calls| &&
       var source := Spec.NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes);
       StateModel.ValueObservedStepRelation(
         source, Spec.TargetInDirectorySpec(directory, source), cmd, states[i], cwd, states[i + 1], outcomes[i],
         observations, bounds[i], bounds[i + 1], calls[bounds[i] - firstStatus .. bounds[i + 1] - firstStatus]))
  }

  lemma {:induction false} ObservedBatchIntervalAt(
    sources: seq<string>, directory: string, cmd: Schema.MvCmd, cwd: BW.Path,
    states: seq<BW.FileSystem>, outcomes: seq<Spec.MoveOutcome>,
    observations: Spec.NativeStatusInputs, firstStatus: nat, calls: seq<Spec.StatusCallEvidence>,
    bounds: seq<nat>, i: nat
  )
    requires ObservedBatchIntervals(sources, directory, cmd, cwd, states, outcomes,
                                    observations, firstStatus, calls, bounds)
    requires i < |sources|
    ensures |states| == |sources| + 1 && |outcomes| == |sources| && |bounds| == |sources| + 1
    ensures bounds[0] == firstStatus && bounds[|sources|] == firstStatus + |calls|
    ensures firstStatus <= bounds[i] <= bounds[i + 1] <= firstStatus + |calls|
    ensures
      var source := Spec.NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes);
      StateModel.ValueObservedStepRelation(
        source, Spec.TargetInDirectorySpec(directory, source), cmd, states[i], cwd, states[i + 1], outcomes[i],
        observations, bounds[i], bounds[i + 1], calls[bounds[i] - firstStatus .. bounds[i + 1] - firstStatus])
  {
    hide *;
    reveal ObservedBatchIntervals();
  }

  lemma {:induction false} StatusSliceFromSuffix(
    calls: seq<Spec.StatusCallEvidence>, cut: nat, lo: nat, hi: nat
  )
    requires cut <= lo <= hi <= |calls|
    ensures calls[cut..][lo - cut .. hi - cut] == calls[lo..hi]
  {
    var left := calls[cut..][lo - cut .. hi - cut];
    var right := calls[lo..hi];
    forall i | 0 <= i < |left|
      ensures left[i] == right[i]
    {
    }
  }

  lemma {:induction false} ObservedBatchTailIntervals(
    sources: seq<string>, directory: string, cmd: Schema.MvCmd, cwd: BW.Path,
    states: seq<BW.FileSystem>, outcomes: seq<Spec.MoveOutcome>,
    observations: Spec.NativeStatusInputs, firstStatus: nat, calls: seq<Spec.StatusCallEvidence>,
    bounds: seq<nat>
  ) returns (cut: nat)
    requires |sources| > 0
    requires ObservedBatchIntervals(sources, directory, cmd, cwd, states, outcomes,
                                    observations, firstStatus, calls, bounds)
    ensures |states| == |sources| + 1 && |outcomes| == |sources| && |bounds| == |sources| + 1
    ensures cut <= |calls| && firstStatus + cut == bounds[1]
    ensures ObservedBatchIntervals(sources[1..], directory, cmd, cwd, states[1..], outcomes[1..],
                                   observations, firstStatus + cut, calls[cut..], bounds[1..])
    ensures
      var source := Spec.NormalizeSourceSpec(sources[0], cmd.stripTrailingSlashes);
      StateModel.ValueObservedStepRelation(
        source, Spec.TargetInDirectorySpec(directory, source), cmd, states[0], cwd, states[1], outcomes[0],
        observations, firstStatus, firstStatus + cut, calls[..cut])
  {
    hide *;
    ObservedBatchIntervalAt(sources, directory, cmd, cwd, states, outcomes, observations, firstStatus, calls, bounds, 0);
    cut := bounds[1] - firstStatus;
    assert calls[0..cut] == calls[..cut];
    var source := Spec.NormalizeSourceSpec(sources[0], cmd.stripTrailingSlashes);
    assert StateModel.ValueObservedStepRelation(
      source, Spec.TargetInDirectorySpec(directory, source), cmd, states[0], cwd, states[1], outcomes[0],
      observations, firstStatus, firstStatus + cut, calls[..cut]);
    var tailBounds := bounds[1..];
    var tailCalls := calls[cut..];
    var tailFirst := firstStatus + cut;
    var tailSources := sources[1..];
    var tailStates := states[1..];
    var tailOutcomes := outcomes[1..];
    assert tailBounds[0] == tailFirst && tailBounds[|tailSources|] == firstStatus + |calls|;
    assert forall i: nat {:trigger bounds[i]} | i + 1 < |bounds| :: bounds[i] <= bounds[i + 1] by {
      reveal ObservedBatchIntervals();
    }
    forall i: nat {:trigger tailBounds[i]} | i < |tailSources|
      ensures tailFirst <= tailBounds[i] <= tailBounds[i + 1] <= tailFirst + |tailCalls| &&
              var source := Spec.NormalizeSourceSpec(tailSources[i], cmd.stripTrailingSlashes);
              StateModel.ValueObservedStepRelation(
                source, Spec.TargetInDirectorySpec(directory, source), cmd,
                tailStates[i], cwd, tailStates[i + 1], tailOutcomes[i],
                observations, tailBounds[i], tailBounds[i + 1],
                tailCalls[tailBounds[i] - tailFirst .. tailBounds[i + 1] - tailFirst])
    {
      assert tailBounds[i] == bounds[i + 1] && tailBounds[i + 1] == bounds[i + 2];
      ObservedBatchIntervalAt(sources, directory, cmd, cwd, states, outcomes, observations, firstStatus, calls, bounds, i + 1);
      StatusBoundsIncrease(bounds, 1, i + 1);
      var lo := bounds[i + 1] - firstStatus;
      var hi := bounds[i + 2] - firstStatus;
      assert cut <= lo <= hi <= |calls|;
      StatusSliceFromSuffix(calls, cut, lo, hi);
      assert tailCalls[tailBounds[i] - tailFirst .. tailBounds[i + 1] - tailFirst] == calls[lo..hi];
    }
    reveal ObservedBatchIntervals();
  }

  lemma {:induction false} StatusBoundsIncrease(bounds: seq<nat>, first: nat, last: nat)
    requires first <= last < |bounds|
    requires forall i: nat {:trigger bounds[i]} | i + 1 < |bounds| :: bounds[i] <= bounds[i + 1]
    ensures bounds[first] <= bounds[last]
    decreases last - first
  {
    if first < last {
      StatusBoundsIncrease(bounds, first, last - 1);
      assert bounds[last - 1] <= bounds[last];
    }
  }

  lemma {:induction false} ObservedBatchMovesFromWitness(
    sources: seq<string>, directory: string, cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem, cwd: BW.Path, afterFs: BW.FileSystem, outcome: Spec.MoveOutcome,
    states: seq<BW.FileSystem>, outcomes: seq<Spec.MoveOutcome>, outputs: seq<BW.Bytes>, errors: seq<BW.Bytes>,
    observations: Spec.NativeStatusInputs, firstStatus: nat, calls: seq<Spec.StatusCallEvidence>,
    bounds: seq<nat>
  )
    requires StateModel.ValueBatchMoveWitnessRelation(
               sources, directory, cmd, beforeFs, cwd, afterFs,
               outcome.failed, outcome.stdoutFragment, outcome.stderrFragment, states, outcomes, outputs, errors)
    requires ObservedBatchIntervals(sources, directory, cmd, cwd, states, outcomes,
                                    observations, firstStatus, calls, bounds)
    ensures Spec.ObservedBatchMovesAllowed(sources, directory, cmd, beforeFs, cwd, afterFs, outcome,
                                         observations, firstStatus, calls)
    decreases |sources|
  {
    hide *;
    reveal Spec.ObservedBatchMovesAllowed();
    if |sources| == 0 {
      reveal StateModel.ValueBatchMoveWitnessRelation(), ObservedBatchIntervals();
    } else {
      var rest := BatchTailWitness(sources, directory, cmd, beforeFs, cwd, afterFs, outcome,
                                   states, outcomes, outputs, errors);
      assert states[0] == beforeFs by { reveal StateModel.ValueBatchMoveWitnessRelation(); }
      var cut := ObservedBatchTailIntervals(sources, directory, cmd, cwd, states, outcomes,
                                            observations, firstStatus, calls, bounds);
      ObservedBatchMovesFromWitness(sources[1..], directory, cmd, states[1], cwd, afterFs, rest,
                                    states[1..], outcomes[1..], outputs[1..], errors[1..],
                                    observations, firstStatus + cut, calls[cut..], bounds[1..]);
      reveal StateModel.ValueObservedStepRelation();
    }
  }

  lemma {:induction false} SingletonBatchIsMove(
    rawSource: string, directory: string, cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem, cwd: BW.Path, afterFs: BW.FileSystem, outcome: Spec.MoveOutcome
  )
    requires Spec.BatchMovesAllowed([rawSource], directory, cmd, beforeFs, cwd, afterFs, outcome)
    ensures Spec.MoveAllowed(Spec.MoveEdge(beforeFs, Spec.MoveStep(afterFs, outcome)),
                             Spec.NormalizeSourceSpec(rawSource, cmd.stripTrailingSlashes),
                             Spec.TargetInDirectorySpec(directory, Spec.NormalizeSourceSpec(rawSource, cmd.stripTrailingSlashes)),
                             cmd, cwd)
  {
    hide *;
    reveal Spec.BatchMovesAllowed(), Spec.JoinOutcomes();
    var source := Spec.NormalizeSourceSpec(rawSource, cmd.stripTrailingSlashes);
    var step: Spec.MoveStep, rest: Spec.MoveOutcome :|
      Spec.MoveAllowed(Spec.MoveEdge(beforeFs, step), source, Spec.TargetInDirectorySpec(directory, source), cmd, cwd) &&
      Spec.BatchMovesAllowed([], directory, cmd, step.state, cwd, afterFs, rest) &&
      outcome == Spec.JoinOutcomes(step.outcome, rest);
    assert rest == Spec.MoveOutcome([], [], false) && step.state == afterFs;
    assert outcome == step.outcome;
    assert step == Spec.MoveStep(afterFs, outcome);
  }

  twostate lemma CandidateDirectoryFieldsImpliesSpec(
    io: BenchIO.IO, sources: seq<string>, directory: string, explicitTargetDirectory: bool, cmd: Schema.MvCmd,
    output: BW.Bytes, diagnostics: BW.Bytes, exit: int
  )
    ensures StateModel.ValueCandidateRunIntoDirectoryFields(sources, directory, explicitTargetDirectory, cmd,
                                                            old(io.fs()), old(io.cwd()), io.fs(), [],
                                                            [], output, diagnostics, exit) ==>
            Spec.CandidateRunIntoDirectory(io, sources, directory, explicitTargetDirectory, cmd, output, diagnostics, exit)
  {
    hide *;
    reveal StateModel.ValueCandidateRunIntoDirectoryFields(), Spec.CandidateRunIntoDirectory();
    reveal StateModel.ValueBatchMoveRelation();
    if exists failed: bool, out: BW.Bytes, err: BW.Bytes ::
        Spec.TargetDirectoryCheckSpecFields(directory, old(io.fs()), true, 0) &&
        StateModel.ValueBatchMoveRelation(sources, directory, cmd, old(io.fs()), old(io.cwd()), io.fs(), failed, out, err) &&
        exit == (if failed then 1 else 0) && output == [] + out && diagnostics == [] + err {
      var failed: bool, out: BW.Bytes, err: BW.Bytes :|
        Spec.TargetDirectoryCheckSpecFields(directory, old(io.fs()), true, 0) &&
        StateModel.ValueBatchMoveRelation(sources, directory, cmd, old(io.fs()), old(io.cwd()), io.fs(), failed, out, err) &&
        exit == (if failed then 1 else 0) && output == [] + out && diagnostics == [] + err;
      assert [] + out == out && [] + err == err;
      assert Spec.BatchMovesAllowed(sources, directory, cmd, old(io.fs()), old(io.cwd()), io.fs(),
                                    Spec.MoveOutcome(out, err, failed));
      assert Spec.BatchMovesAllowed(sources, directory, cmd, old(io.fs()), old(io.cwd()), io.fs(),
                                    Spec.MoveOutcome(output, diagnostics, failed));
    }
  }

  twostate lemma CandidateSpecFieldsImpliesSpec(
    io: BenchIO.IO, raw: Schema.MvCmdRaw, output: BW.Bytes, diagnostics: BW.Bytes, exit: int
  )
    requires StateModel.ValueCandidateSpecFields(raw, old(io.fs()), old(io.cwd()), [], [],
                                                 io.fs(), output, diagnostics, exit)
    ensures Spec.CandidateSpec(io, raw, output, diagnostics, exit)
  {
    hide *;
    reveal StateModel.ValueCandidateSpecFields(), Spec.CandidateSpec();
    var cmd := Schema.Command(raw);
    CandidateDirectoryFieldsImpliesSpec(io, cmd.operands, cmd.targetDirectory, true, cmd, output, diagnostics, exit);
    if |cmd.operands| > 0 {
      CandidateDirectoryFieldsImpliesSpec(io, cmd.operands[..|cmd.operands| - 1], cmd.operands[|cmd.operands| - 1],
                                          false, cmd, output, diagnostics, exit);
    }
    if |cmd.operands| == 2 {
      reveal StateModel.ValueCandidateRunTwoOperandFields(), Spec.CandidateRunTwoOperand();
      reveal StateModel.ValueMoveEffectRelation();
    }
  }

  lemma ObservedDirectoryFieldsImpliesMoves(
    sources: seq<string>, directory: string, cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem, cwd: BW.Path, afterFs: BW.FileSystem,
    output: BW.Bytes, diagnostics: BW.Bytes, exit: int, observations: Spec.NativeStatusInputs,
    firstStatus: nat, afterStatus: nat, calls: seq<Spec.StatusCallEvidence>
  )
    ensures
      (exists failed: bool, out: BW.Bytes, err: BW.Bytes ::
         StateModel.ValueObservedBatchRelation(sources, directory, cmd, beforeFs, cwd, afterFs,
                                               failed, out, err, observations, firstStatus, afterStatus, calls) &&
         exit == (if failed then 1 else 0) && output == [] + out && diagnostics == [] + err) ==>
      (exists failed: bool ::
         Spec.ObservedBatchMovesAllowed(sources, directory, cmd, beforeFs, cwd, afterFs,
                                       Spec.MoveOutcome(output, diagnostics, failed), observations, firstStatus, calls) &&
         exit == (if failed then 1 else 0))
  {
    hide *;
    if exists failed: bool, out: BW.Bytes, err: BW.Bytes ::
        StateModel.ValueObservedBatchRelation(sources, directory, cmd, beforeFs, cwd, afterFs,
                                             failed, out, err, observations, firstStatus, afterStatus, calls) &&
        exit == (if failed then 1 else 0) && output == [] + out && diagnostics == [] + err {
      var failed: bool, out: BW.Bytes, err: BW.Bytes :|
        StateModel.ValueObservedBatchRelation(sources, directory, cmd, beforeFs, cwd, afterFs,
                                             failed, out, err, observations, firstStatus, afterStatus, calls) &&
        exit == (if failed then 1 else 0) && output == [] + out && diagnostics == [] + err;
      reveal StateModel.ValueObservedBatchRelation();
      assert [] + out == out && [] + err == err;
      assert Spec.ObservedBatchMovesAllowed(sources, directory, cmd, beforeFs, cwd, afterFs,
                                            Spec.MoveOutcome(out, err, failed), observations, firstStatus, calls);
      assert Spec.ObservedBatchMovesAllowed(sources, directory, cmd, beforeFs, cwd, afterFs,
                                            Spec.MoveOutcome(output, diagnostics, failed), observations, firstStatus, calls);
    }
  }

  twostate lemma ObservedStatusFieldsImpliesSpec(
    io: BenchIO.IO, raw: Schema.MvCmdRaw, output: BW.Bytes, diagnostics: BW.Bytes, exit: int,
    observations: Spec.NativeStatusInputs, calls: seq<Spec.StatusCallEvidence>
  )
    requires StateModel.ValueObservedStatusSpec(raw, old(io.fs()), old(io.cwd()), io.fs(),
                                               [], output, [], diagnostics, exit, observations,
                                               old(io.statusCursor()), io.statusCursor(), calls)
    ensures Spec.ObservedStatusSpec(io, raw, output, diagnostics, exit, observations, calls)
  {
    hide *;
    reveal StateModel.ValueObservedStatusSpec(), Spec.ObservedStatusSpec();
    reveal StateModel.ValueObservedStepRelation();
    var cmd := Schema.Command(raw);
    if |calls| > 0 {
      ObservedDirectoryFieldsImpliesMoves(cmd.operands, cmd.targetDirectory, cmd, old(io.fs()), old(io.cwd()), io.fs(),
                                           output, diagnostics, exit, observations,
                                           old(io.statusCursor()) + 1, io.statusCursor(), calls[1..]);
      if |cmd.operands| > 0 {
        ObservedDirectoryFieldsImpliesMoves(cmd.operands[..|cmd.operands| - 1], cmd.operands[|cmd.operands| - 1], cmd,
                                             old(io.fs()), old(io.cwd()), io.fs(), output, diagnostics, exit, observations,
                                             old(io.statusCursor()) + 1, io.statusCursor(), calls[1..]);
      }
    }
  }

  lemma EntryNameEvidenceImpliesPathRelations(
    fs: BW.FileSystem,
    path: string,
    evidence: Core.EntryNameEvidence
  )
    requires Core.EntryNameEvidenceFor(fs, path, evidence)
    ensures BasenameSpec.BasenameRelation(path, evidence.leaf)
    ensures DirnameSpec.DirnameRelation(path, evidence.parent)
    ensures Spec.EntryNameSpec(path) == Spec.EntryName(evidence.parent, evidence.leaf)
  {
    reveal Core.EntryNameEvidenceFor();
    PathProof.BasenameValueSummaryGivesRelation(
      path, evidence.leaf
    );
    PathProof.DirnameValueSummaryGivesRelation(
      path, evidence.parent
    );
    BasenameRelationFunctional(path, evidence.leaf, Spec.EntryNameSpec(path).leaf);
    DirnameRelationFunctional(path, evidence.parent, Spec.EntryNameSpec(path).parent);
  }

  lemma BackupStatusSuffixCoreImpliesSpec(
    backupMode: Schema.BackupMode,
    fs: BW.FileSystem,
    target: string,
    calls: seq<Spec.StatusCallEvidence>
  )
    requires Core.BackupStatusSuffixFor(backupMode, fs, target, calls)
    ensures Spec.BackupStatusSuffix(backupMode, fs, target, calls)
  {
  }

  lemma NonSlashPrefixSlashSuffixFunctional(
    path: string,
    left: string,
    leftTrailing: string,
    right: string,
    rightTrailing: string
  )
    requires path == left + leftTrailing
    requires path == right + rightTrailing
    requires 0 < |left| && left[|left| - 1] != '/'
    requires 0 < |right| && right[|right| - 1] != '/'
    requires forall i :: 0 <= i < |leftTrailing| ==>
                           leftTrailing[i] == '/'
    requires forall i :: 0 <= i < |rightTrailing| ==>
                           rightTrailing[i] == '/'
    ensures left == right
  {
    if |left| < |right| {
      var i := |right| - 1;
      assert path[i] == right[i];
      assert i - |left| < |leftTrailing|;
      assert path[i] == leftTrailing[i - |left|];
      assert false;
    } else if |right| < |left| {
      var i := |left| - 1;
      assert path[i] == left[i];
      assert i - |right| < |rightTrailing|;
      assert path[i] == rightTrailing[i - |right|];
      assert false;
    }
    assert left == path[..|left|];
    assert right == path[..|right|];
  }

  lemma MaximalSlashFreeSuffixFunctional(
    text: string,
    left: string,
    right: string
  )
    requires BasenameSpec.MaximalSlashFreeSuffix(text, left)
    requires BasenameSpec.MaximalSlashFreeSuffix(text, right)
    ensures left == right
  {
    if |left| < |right| {
      var boundary := |text| - |left| - 1;
      assert 0 <= boundary < |text|;
      assert BasenameSpec.IsSlash(text[boundary]);
      assert |text| - |right| <= boundary;
      var i := boundary - (|text| - |right|);
      assert 0 <= i < |right|;
      assert right[i] == text[boundary];
      assert !BasenameSpec.IsSlash(right[i]);
      assert false;
    } else if |right| < |left| {
      var boundary := |text| - |right| - 1;
      assert 0 <= boundary < |text|;
      assert BasenameSpec.IsSlash(text[boundary]);
      assert |text| - |left| <= boundary;
      var i := boundary - (|text| - |left|);
      assert 0 <= i < |left|;
      assert left[i] == text[boundary];
      assert !BasenameSpec.IsSlash(left[i]);
      assert false;
    }
    assert left == text[|text| - |left|..];
    assert right == text[|text| - |right|..];
  }

  lemma BasenameRelationFunctional(
    path: string,
    left: string,
    right: string
  )
    requires BasenameSpec.BasenameRelation(path, left)
    requires BasenameSpec.BasenameRelation(path, right)
    ensures left == right
  {
    if |path| == 0 || BasenameSpec.SlashesOnly(path) {
    } else {
      var leftTrimmed, leftPrefix, leftTrailing :|
        path == leftTrimmed + leftTrailing &&
        BasenameSpec.SlashesOnly(leftTrailing) &&
        0 < |leftTrimmed| &&
        !BasenameSpec.IsSlash(leftTrimmed[|leftTrimmed| - 1]) &&
        leftTrimmed == leftPrefix + left &&
        BasenameSpec.MaximalSlashFreeSuffix(leftTrimmed, left);
      var rightTrimmed, rightPrefix, rightTrailing :|
        path == rightTrimmed + rightTrailing &&
        BasenameSpec.SlashesOnly(rightTrailing) &&
        0 < |rightTrimmed| &&
        !BasenameSpec.IsSlash(rightTrimmed[|rightTrimmed| - 1]) &&
        rightTrimmed == rightPrefix + right &&
        BasenameSpec.MaximalSlashFreeSuffix(rightTrimmed, right);
      NonSlashPrefixSlashSuffixFunctional(
        path,
        leftTrimmed,
        leftTrailing,
        rightTrimmed,
        rightTrailing
      );
      MaximalSlashFreeSuffixFunctional(
        leftTrimmed, left, right
      );
    }
  }

  lemma MaximalDirnamePrefixFunctional(
    trimmed: string,
    leftPrefix: string,
    leftComponent: string,
    rightPrefix: string,
    rightComponent: string
  )
    requires DirnameSpec.MaximalDirnamePrefix(
               trimmed, leftPrefix, leftComponent
             )
    requires DirnameSpec.MaximalDirnamePrefix(
               trimmed, rightPrefix, rightComponent
             )
    ensures leftPrefix == rightPrefix
  {
    assert trimmed[|leftPrefix|] == '/';
    assert trimmed[|rightPrefix|] == '/';
    if |leftPrefix| < |rightPrefix| {
      assert |rightPrefix| <= |leftPrefix|;
      assert false;
    } else if |rightPrefix| < |leftPrefix| {
      assert |leftPrefix| <= |rightPrefix|;
      assert false;
    }
    assert leftPrefix == trimmed[..|leftPrefix|];
    assert rightPrefix == trimmed[..|rightPrefix|];
  }

  lemma NormalizedDirnamePrefixFunctional(
    prefix: string,
    left: string,
    right: string
  )
    requires DirnameSpec.NormalizedDirnamePrefix(prefix, left)
    requires DirnameSpec.NormalizedDirnamePrefix(prefix, right)
    ensures left == right
  {
    if |prefix| == 0 || DirnameSpec.SlashesOnly(prefix) {
    } else {
      var leftTrailing :|
        prefix == left + leftTrailing &&
        DirnameSpec.SlashesOnly(leftTrailing) &&
        0 < |left| &&
        !DirnameSpec.IsSlash(left[|left| - 1]);
      var rightTrailing :|
        prefix == right + rightTrailing &&
        DirnameSpec.SlashesOnly(rightTrailing) &&
        0 < |right| &&
        !DirnameSpec.IsSlash(right[|right| - 1]);
      NonSlashPrefixSlashSuffixFunctional(
        prefix, left, leftTrailing, right, rightTrailing
      );
    }
  }

  lemma DirnameRelationFunctional(
    path: string,
    left: string,
    right: string
  )
    requires DirnameSpec.DirnameRelation(path, left)
    requires DirnameSpec.DirnameRelation(path, right)
    ensures left == right
  {
    reveal DirnameSpec.DirnameRelation();
    if |path| == 0 || DirnameSpec.SlashesOnly(path) {
    } else {
      var leftTrimmed, leftTrailing :|
        DirnameSpec.PathWithoutTrailingSlashes(
          path, leftTrimmed, leftTrailing
        ) &&
        (if DirnameSpec.SlashFree(leftTrimmed) then
           left == "."
         else
           exists leftPrefix: string, leftComponent: string ::
             DirnameSpec.MaximalDirnamePrefix(
               leftTrimmed, leftPrefix, leftComponent
             ) &&
             DirnameSpec.NormalizedDirnamePrefix(leftPrefix, left));
      var rightTrimmed, rightTrailing :|
        DirnameSpec.PathWithoutTrailingSlashes(
          path, rightTrimmed, rightTrailing
        ) &&
        (if DirnameSpec.SlashFree(rightTrimmed) then
           right == "."
         else
           exists rightPrefix: string, rightComponent: string ::
             DirnameSpec.MaximalDirnamePrefix(
               rightTrimmed, rightPrefix, rightComponent
             ) &&
             DirnameSpec.NormalizedDirnamePrefix(rightPrefix, right));
      NonSlashPrefixSlashSuffixFunctional(
        path,
        leftTrimmed,
        leftTrailing,
        rightTrimmed,
        rightTrailing
      );
      if !DirnameSpec.SlashFree(leftTrimmed) {
        var leftPrefix, leftComponent :|
          DirnameSpec.MaximalDirnamePrefix(
            leftTrimmed, leftPrefix, leftComponent
          ) &&
          DirnameSpec.NormalizedDirnamePrefix(leftPrefix, left);
        var rightPrefix, rightComponent :|
          DirnameSpec.MaximalDirnamePrefix(
            leftTrimmed, rightPrefix, rightComponent
          ) &&
          DirnameSpec.NormalizedDirnamePrefix(rightPrefix, right);
        MaximalDirnamePrefixFunctional(
          leftTrimmed,
          leftPrefix,
          leftComponent,
          rightPrefix,
          rightComponent
        );
        NormalizedDirnamePrefixFunctional(
          leftPrefix, left, right
        );
      }
    }
  }

  lemma MetadataEvidenceKeysImplySameResolvedObject(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    followLeft: bool,
    followRight: bool,
    left: Core.MetadataEvidence,
    right: Core.MetadataEvidence
  )
    requires Core.MetadataEvidenceFor(
               fs, leftPath, followLeft, left
             )
    requires Core.MetadataEvidenceFor(
               fs, rightPath, followRight, right
             )
    requires left.ok && right.ok
    requires left.key == right.key
    ensures exists
              resolvedLeft: BW.Path,
              resolvedRight: BW.Path
              ::
                IOContract.ResolvePathForMetadataFields(
                  fs, leftPath, followLeft
                ) == Result.Ok(resolvedLeft) &&
                IOContract.ResolvePathForMetadataFields(
                  fs, rightPath, followRight
                ) == Result.Ok(resolvedRight) &&
                BW.InodeSameObject(fs, resolvedLeft, resolvedRight)
  {
    var resolvedLeft :=
      IOContract.ResolvePathForMetadataFields(
        fs, leftPath, followLeft
      ).v;
    var resolvedRight :=
      IOContract.ResolvePathForMetadataFields(
        fs, rightPath, followRight
      ).v;
    var leftId := BW.FsIdAt(fs, resolvedLeft);
    var rightId := BW.FsIdAt(fs, resolvedRight);
    assert BW.InodeUniqueHostKeys(fs);
    assert fs.inodes[leftId].hostKey == left.key;
    assert fs.inodes[rightId].hostKey == right.key;
    assert leftId == rightId;
    assert BW.InodeSameObject(fs, resolvedLeft, resolvedRight);
  }

  lemma MetadataEvidenceImpliesSameInode(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    left: Core.MetadataEvidence,
    right: Core.MetadataEvidence
  )
    requires Core.MetadataEvidenceFor(fs, leftPath, false, left)
    requires Core.MetadataEvidenceFor(fs, rightPath, false, right)
    requires left.ok && right.ok
    requires left.key == right.key
    ensures Spec.SameInode(fs, leftPath, rightPath)
  {
    MetadataEvidenceKeysImplySameResolvedObject(
      fs, leftPath, rightPath, false, false, left, right
    );
  }

  lemma SameInodeImpliesMetadataKeysEqual(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    left: Core.MetadataEvidence,
    right: Core.MetadataEvidence
  )
    requires Core.MetadataEvidenceFor(fs, leftPath, false, left)
    requires Core.MetadataEvidenceFor(fs, rightPath, false, right)
    requires left.ok && right.ok
    requires Spec.SameInode(fs, leftPath, rightPath)
    ensures left.key == right.key
  {
    var resolvedLeft :=
      IOContract.ResolvePathForMetadataFields(fs, leftPath, false).v;
    var resolvedRight :=
      IOContract.ResolvePathForMetadataFields(fs, rightPath, false).v;
    assert fs.inodes[BW.FsIdAt(fs, resolvedLeft)].hostKey == left.key;
    assert fs.inodes[BW.FsIdAt(fs, resolvedRight)].hostKey == right.key;
  }

  lemma SameResolvedObjectImpliesMetadataKeysEqual(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    followLeft: bool,
    followRight: bool,
    left: Core.MetadataEvidence,
    right: Core.MetadataEvidence
  )
    requires Core.MetadataEvidenceFor(
               fs, leftPath, followLeft, left
             )
    requires Core.MetadataEvidenceFor(
               fs, rightPath, followRight, right
             )
    requires left.ok && right.ok
    requires exists
               resolvedLeft: BW.Path,
               resolvedRight: BW.Path
               ::
                 IOContract.ResolvePathForMetadataFields(
                   fs, leftPath, followLeft
                 ) == Result.Ok(resolvedLeft) &&
                 IOContract.ResolvePathForMetadataFields(
                   fs, rightPath, followRight
                 ) == Result.Ok(resolvedRight) &&
                 BW.InodeSameObject(fs, resolvedLeft, resolvedRight)
    ensures left.key == right.key
  {
    var resolvedLeft :=
      IOContract.ResolvePathForMetadataFields(
        fs, leftPath, followLeft
      ).v;
    var resolvedRight :=
      IOContract.ResolvePathForMetadataFields(
        fs, rightPath, followRight
      ).v;
    assert fs.inodes[BW.FsIdAt(fs, resolvedLeft)].hostKey == left.key;
    assert fs.inodes[BW.FsIdAt(fs, resolvedRight)].hostKey == right.key;
  }

  lemma EntryNameEvidenceImpliesSameDirectoryEntry(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    left: Core.EntryNameEvidence,
    right: Core.EntryNameEvidence
  )
    requires Core.EntryNameEvidenceFor(fs, leftPath, left)
    requires Core.EntryNameEvidenceFor(fs, rightPath, right)
    requires Core.EvidenceNamesSame(left, right)
    ensures Spec.SameDirectoryEntry(fs, leftPath, rightPath)
  {
    EntryNameEvidenceImpliesPathRelations(fs, leftPath, left);
    EntryNameEvidenceImpliesPathRelations(fs, rightPath, right);
    MetadataEvidenceImpliesSameInode(
      fs,
      left.parent,
      right.parent,
      left.parentMetadata,
      right.parentMetadata
    );
  }

  lemma {:isolate_assertions} SameDirectoryEntryImpliesEvidenceNamesSame(
    fs: BW.FileSystem,
    leftPath: string,
    rightPath: string,
    left: Core.EntryNameEvidence,
    right: Core.EntryNameEvidence
  )
    requires Core.EntryNameEvidenceFor(fs, leftPath, left)
    requires Core.EntryNameEvidenceFor(fs, rightPath, right)
    requires Spec.SameDirectoryEntry(fs, leftPath, rightPath)
    requires left.parentMetadata.ok ||
             !Spec.StatusExistsOutcomeFields(fs, left.parent, false, true, 0)
    requires right.parentMetadata.ok ||
             !Spec.StatusExistsOutcomeFields(fs, right.parent, false, true, 0)
    ensures Core.EvidenceNamesSame(left, right)
  {
    EntryNameEvidenceImpliesPathRelations(fs, leftPath, left);
    EntryNameEvidenceImpliesPathRelations(fs, rightPath, right);
    var leftParent, rightParent, leftLeaf, rightLeaf,
        resolvedLeftParent, resolvedRightParent :|
      DirnameSpec.DirnameRelation(leftPath, leftParent) &&
      DirnameSpec.DirnameRelation(rightPath, rightParent) &&
      BasenameSpec.BasenameRelation(leftPath, leftLeaf) &&
      BasenameSpec.BasenameRelation(rightPath, rightLeaf) &&
      leftLeaf == rightLeaf &&
      IOContract.ResolvePathForMetadataFields(
        fs, leftParent, false
      ) == Result.Ok(resolvedLeftParent) &&
      IOContract.ResolvePathForMetadataFields(
        fs, rightParent, false
      ) == Result.Ok(resolvedRightParent) &&
      BW.InodeSameObject(
        fs, resolvedLeftParent, resolvedRightParent
      );
    BasenameRelationFunctional(leftPath, left.leaf, leftLeaf);
    BasenameRelationFunctional(rightPath, right.leaf, rightLeaf);
    DirnameRelationFunctional(leftPath, left.parent, leftParent);
    DirnameRelationFunctional(rightPath, right.parent, rightParent);
    reveal BW.InodeSameObject();
    reveal BW.FsContainsPath();
    reveal Core.EntryNameEvidenceFor();
    reveal Core.MetadataEvidenceFor();
    assert IOContract.ResolvePathForMetadataFields(
        fs, left.parent, false
      ) == Result.Ok(resolvedLeftParent);
    assert IOContract.ResolvePathForMetadataFields(
        fs, right.parent, false
      ) == Result.Ok(resolvedRightParent);
    assert BW.FsContainsPath(fs, resolvedLeftParent);
    assert BW.FsContainsPath(fs, resolvedRightParent);
    assert left.parentMetadata.ok;
    assert right.parentMetadata.ok;
    assert Spec.SameInode(fs, left.parent, right.parent);
    SameInodeImpliesMetadataKeysEqual(
      fs,
      left.parent,
      right.parent,
      left.parentMetadata,
      right.parentMetadata
    );
  }

  lemma ResolvePathIdentitySuccessFunctional(
    fs: BW.FileSystem,
    cwd: BW.Path,
    path: BW.Path,
    left: BW.Path,
    right: BW.Path
  )
    requires IOContract.ResolvePathIdentityContractFields(
               fs, cwd, path, true, left, 0
             )
    requires IOContract.ResolvePathIdentityContractFields(
               fs, cwd, path, true, right, 0
             )
    ensures left == right
  {
  }

  lemma {:isolate_assertions} SameFileEvidenceImpliesPolicy(
    cmd: Schema.MvCmd,
    fs: BW.FileSystem,
    preCwd: BW.Path,
    source: string,
    target: string,
    evidence: Core.SameFileEvidence
  )
    requires Core.SameFileEvidenceFor(
               cmd, fs, preCwd, source, target, evidence
             )
    requires evidence.CheckedSameFile? && !evidence.decision.FailedParentStat?
    requires evidence.sourceEntry.parentMetadata.ok ||
             !Spec.StatusExistsOutcomeFields(fs, evidence.sourceEntry.parent, false, true, 0)
    requires evidence.targetEntry.parentMetadata.ok ||
             !Spec.StatusExistsOutcomeFields(fs, evidence.targetEntry.parent, false, true, 0)
    requires evidence.source.isSymlink ==> evidence.sourceReferentEntry.SomeEntryNameEvidence?
    requires evidence.sourceReferentEntry.SomeEntryNameEvidence? ==>
               evidence.sourceReferentEntry.value.parentMetadata.ok ||
               !Spec.StatusExistsOutcomeFields(fs, evidence.sourceReferentEntry.value.parent, false, true, 0)
    ensures
      var decision :=
        match evidence
        case NoSameFileCheck => Core.ContinueMove
        case CheckedSameFile(_, _, _, _, _, _, _, value) =>
          value;
      (decision == Core.RejectSameFile) == Spec.SameFileMustBeRejected(cmd, fs, preCwd, source, target)
  {
    reveal Core.SameFileEvidenceFor();
    match evidence {
      case NoSameFileCheck =>
      case CheckedSameFile(
        sourceMetadata,
        targetMetadata,
        sourceFollowed,
        sourceEntry,
        targetEntry,
        sourceReferentEntry,
        _,
        decision
        ) =>
        if Core.EvidenceNamesSame(sourceEntry, targetEntry) {
          EntryNameEvidenceImpliesSameDirectoryEntry(
            fs, source, target, sourceEntry, targetEntry
          );
        }
        if sourceMetadata.key == targetMetadata.key {
          MetadataEvidenceImpliesSameInode(
            fs, source, target, sourceMetadata, targetMetadata
          );
        }
        match sourceReferentEntry {
          case SomeEntryNameEvidence(resolvedPath, referentEntry) =>
            if Core.EvidenceNamesSame(referentEntry, targetEntry) {
              EntryNameEvidenceImpliesSameDirectoryEntry(
                fs,
                resolvedPath,
                target,
                referentEntry,
                targetEntry
              );
            }
          case _ =>
        }
        if Spec.SameDirectoryEntry(fs, source, target) {
          SameDirectoryEntryImpliesEvidenceNamesSame(
            fs, source, target, sourceEntry, targetEntry
          );
        }
        if Spec.SameInode(fs, source, target) {
          SameInodeImpliesMetadataKeysEqual(
            fs, source, target, sourceMetadata, targetMetadata
          );
        }
        if Spec.SourceSymlinkReferentHasTargetName(
            fs, preCwd, source, target
          ) {
          var publicResolvedSource, publicResolvedReferent :|
            IOContract.ResolvePathForMetadataFields(
              fs, source, false
            ) == Result.Ok(publicResolvedSource) &&
            BW.FsContainsPath(fs, publicResolvedSource) &&
            BW.FsNodeAt(fs, publicResolvedSource).Symlink? &&
            IOContract.ResolvePathIdentityContractFields(
              fs,
              preCwd,
              source,
              true,
              publicResolvedReferent,
              0
            ) &&
            Spec.SameDirectoryEntry(
              fs, publicResolvedReferent, target
            );
          assert sourceMetadata.isSymlink;
          match sourceReferentEntry {
            case SomeEntryNameEvidence(resolvedPath, referentEntry) =>
              assert IOContract.ResolvePathIdentityContractFields(
                  fs, preCwd, source, true, resolvedPath, 0
                ) by {
                hide *;
                reveal Core.SameFileEvidenceFor();
              }
              assert IOContract.ResolvePathIdentityContractFields(
                  fs, preCwd, source, true, publicResolvedReferent, 0
                ) by { hide *; }
              ResolvePathIdentitySuccessFunctional(
                fs,
                preCwd,
                source,
                resolvedPath,
                publicResolvedReferent
              );
              assert Spec.SameDirectoryEntry(
                  fs, resolvedPath, target
                );
              SameDirectoryEntryImpliesEvidenceNamesSame(
                fs,
                resolvedPath,
                target,
                referentEntry,
                targetEntry
              );
            case _ =>
          }
        }
        var capturedReject :=
          Core.EvidenceNamesSame(sourceEntry, targetEntry) ||
          (cmd.backupMode == Schema.BackupOff &&
           ((sourceMetadata.ok &&
             targetMetadata.ok &&
             sourceMetadata.key == targetMetadata.key) ||
            Core.ReferentEvidenceNamesTarget(
              sourceReferentEntry, targetEntry
            )));
        assert Spec.SameFileMustBeRejected(
            cmd, fs, preCwd, source, target
          )
          ==> capturedReject by {
          if Spec.SameFileMustBeRejected(
              cmd, fs, preCwd, source, target
            ) {
            if Spec.SameDirectoryEntry(fs, source, target) {
              assert Core.EvidenceNamesSame(
                  sourceEntry, targetEntry
                );
            } else if Spec.SameInode(fs, source, target) {
              assert sourceMetadata.key == targetMetadata.key;
            } else {
              assert Spec.SourceSymlinkReferentHasTargetName(
                  fs, preCwd, source, target
                );
              assert Core.ReferentEvidenceNamesTarget(
                  sourceReferentEntry, targetEntry
                );
            }
          }
        }
        assert capturedReject ==> Spec.SameFileMustBeRejected(
              cmd, fs, preCwd, source, target
            ) by {
          if capturedReject {
            if Core.EvidenceNamesSame(sourceEntry, targetEntry) {
              assert Spec.SameDirectoryEntry(fs, source, target);
            } else if sourceMetadata.key == targetMetadata.key {
              assert Spec.SameInode(fs, source, target);
            } else {
              assert Core.ReferentEvidenceNamesTarget(
                  sourceReferentEntry, targetEntry
                );
              match sourceReferentEntry {
                case SomeEntryNameEvidence(
                  resolvedPath, referentEntry
                  ) =>
        assert Spec.SourceSymlinkReferentHasTargetName(
            fs, preCwd, source, target
          );
                case _ =>
              }
            }
          }
        }
        assert Spec.SameFileMustBeRejected(
            cmd, fs, preCwd, source, target
          ) == capturedReject;
        assert (decision == Core.RejectSameFile) == Spec.SameFileMustBeRejected(cmd, fs, preCwd, source, target);
    }
  }

  lemma BackupCollisionEvidenceImpliesSpec(
    cmd: Schema.MvCmd,
    fs: BW.FileSystem,
    source: string,
    target: string,
    sourceMetadata: Core.MetadataEvidence,
    sourceEntry: Core.EntryNameEvidence,
    targetEntry: Core.EntryNameEvidence,
    collision: Core.BackupCollisionEvidence
  )
    requires Core.MetadataEvidenceFor(
               fs, source, false, sourceMetadata
             )
    requires sourceMetadata.ok
    requires Core.EntryNameEvidenceFor(fs, source, sourceEntry)
    requires Core.EntryNameEvidenceFor(fs, target, targetEntry)
    requires Core.BackupCollisionEvidenceFor(
               cmd,
               fs,
               source,
               target,
               sourceMetadata,
               sourceEntry,
               targetEntry,
               collision
             )
    requires collision.CheckedBackupCollision? ==>
               collision.simpleCandidateFollowed.ok ||
               !Spec.StatusExistsOutcomeFields(fs, BasenameSpec.SimpleBackupPathSpec(target, cmd.backupSuffix), true, true, 0)
    ensures Core.BackupCollisionDetected(collision) ==
            Spec.BackupWouldDestroySource(cmd, fs, source, target)
  {
    hide Core.MetadataEvidenceFor(), Core.EntryNameEvidenceFor(), Core.StatusCallsFor(), Spec.StatusCallsFor();
    EntryNameEvidenceImpliesPathRelations(
      fs, source, sourceEntry
    );
    EntryNameEvidenceImpliesPathRelations(
      fs, target, targetEntry
    );
    match collision {
      case NoBackupCollisionCheck =>
        if Spec.BackupWouldDestroySource(cmd, fs, source, target) {
          var sourceLeaf, targetLeaf :|
            BasenameSpec.BasenameRelation(source, sourceLeaf) &&
            BasenameSpec.BasenameRelation(target, targetLeaf) &&
            sourceLeaf == targetLeaf + cmd.backupSuffix;
          BasenameRelationFunctional(
            source, sourceEntry.leaf, sourceLeaf
          );
          BasenameRelationFunctional(
            target, targetEntry.leaf, targetLeaf
          );
        }
      case CheckedBackupCollision(sourceNoFollow, candidateFollowed) =>
        var candidate :=
          BasenameSpec.SimpleBackupPathSpec(target, cmd.backupSuffix);
        assert sourceNoFollow == sourceMetadata;
        assert BasenameSpec.SimpleBackupPathSpec(target, cmd.backupSuffix) ==
               candidate;
        if Core.BackupCollisionDetected(collision) {
          MetadataEvidenceKeysImplySameResolvedObject(
            fs,
            source,
            candidate,
            false,
            true,
            sourceMetadata,
            candidateFollowed
          );
        }
        if Spec.BackupWouldDestroySource(cmd, fs, source, target) {
          assert candidateFollowed.ok;
          SameResolvedObjectImpliesMetadataKeysEqual(
            fs,
            source,
            candidate,
            false,
            true,
            sourceMetadata,
            candidateFollowed
          );
        }
    }
  }

  lemma BackupChecksImplyNumberedTarget(
    target: string,
    fs: BW.FileSystem,
    checks: seq<Core.BackupCheckEvidence>,
    path: string
  )
    requires Core.BackupChecksFor(target, 1, fs, checks)
    requires path == checks[|checks| - 1].candidate
    ensures Spec.NumberedBackupTargetSpecFields(
              fs, target, path
            )
  {
    var index: nat := |checks|;
    assert path == BasenameSpec.NumberedBackupPathSpec(target, index);
    assert Spec.StatusExistsOutcomeFields(
        fs, path, false, false, checks[|checks| - 1].err
      );
    assert forall j: nat | 1 <= j < index ::
        Spec.StatusExistsOutcomeFields(
          fs,
          BasenameSpec.NumberedBackupPathSpec(target, j),
          false,
          true,
          0
        ) by {
      forall j: nat | 1 <= j < index
        ensures Spec.StatusExistsOutcomeFields(
                  fs,
                  BasenameSpec.NumberedBackupPathSpec(target, j),
                  false,
                  true,
                  0
                )
      {
        var i: nat := j - 1;
        assert i + 1 < |checks|;
        assert checks[i].found;
        assert checks[i].candidate ==
               BasenameSpec.NumberedBackupPathSpec(target, j);
        assert Spec.StatusExistsOutcomeFields(
            fs, checks[i].candidate, false, true, checks[i].err
          );
        assert checks[i].err == 0;
      }
    }
  }

  lemma BackupSelectionEvidenceImpliesSpec(
    target: string,
    mode: Schema.BackupMode,
    suffix: string,
    fs: BW.FileSystem,
    evidence: Core.BackupSelectionEvidence
  )
    requires Core.BackupSelectionEvidenceFor(
               target, mode, suffix, fs, evidence
             )
    ensures Spec.BackupTargetSpecFields(
              fs, target, mode, suffix,
              match evidence
              case NoBackupSelection => ""
              case SelectedBackup(path, _, _, _, _) => path
            )
  {
    match evidence {
      case NoBackupSelection =>
      case SelectedBackup(
        path,
        checks,
        existingFirstCheckCalled,
        existingFirstFound,
        existingFirstErr
        ) =>
        if mode == Schema.BackupNumbered || (mode == Schema.BackupExisting && existingFirstFound) {
          BackupChecksImplyNumberedTarget(
            target, fs, checks, path
          );
          assert Spec.NumberedBackupTargetSpecFields(
              fs, target, path
            );
        }
    }
  }

  lemma RenameEvidenceImpliesRelation(
    source: string,
    target: string,
    sourceIsDir: bool,
    targetWasFound: bool,
    backupPath: string,
    verbose: bool,
    debug: bool,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    outcome: Spec.MoveOutcome,
    calls: seq<Core.RenameCallEvidence>,
    backupFs: BW.FileSystem
  )
    requires Core.RenameEvidenceFor(
               source, target, sourceIsDir,
               targetWasFound, backupPath, verbose, debug,
               beforeFs, preCwd, afterFs, outcome, calls, backupFs
             )
    requires backupPath != "" || targetWasFound ==
                                 Spec.StatusExistsOutcomeFields(beforeFs, target, false, true, 0)
    ensures StateModel.ValueRenameEffectRelation(
              source, target, backupPath, verbose, debug,
              beforeFs, preCwd, afterFs, outcome
            )
  {
    if backupPath != "" && |calls| == 2 && !calls[1].ok {
      assert backupFs == afterFs by {
        reveal Core.RenameEvidenceFor(), IOContract.RenamePathContractFields();
      }
    }
  }

  lemma RenameNativeEvidenceImpliesObservedRelation(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence, backupPath: string
  )
    requires Core.RenameEvidenceFor(source, target, step.sourceIsDir, step.targetFound,
                                    backupPath, cmd.verbose, cmd.debug, step.beforeFs, cwd, step.afterFs,
                                    step.outcome, step.renames, step.backupFs)
    requires Core.RenameNativeObservationsFor(source, target, step)
    requires if backupPath == "" then step.backup.NoBackupSelection?
             else step.backup.SelectedBackup? && step.backup.backupPath == backupPath
    ensures StateModel.ValueObservedRenameEffectRelation(source, target, backupPath, cmd,
                                                         step.sourceIsDir, step.targetFound, step.inputs, step.beforeFs, step.afterFs, step.outcome)
  {
    reveal Core.RenameEvidenceFor(), Core.RenameNativeObservationsFor();
    if backupPath == "" {
      assert |step.renames| == 1;
      assert step.renames[0].ok ==> step.renames[0].err == 0;
    } else {
      assert step.renames[0].ok ==> step.renames[0].err == 0;
      if |step.renames| == 2 {
        assert step.renames[1].ok ==> step.renames[1].err == 0;
        if !step.renames[1].ok {
          assert step.backupFs == step.afterFs by { reveal IOContract.RenamePathContractFields(); }
        }
      }
    }
    hide IOContract.RenamePathSpec(), IOContract.RenamePathContractFields();
    reveal StateModel.ValueObservedRenameEffectRelation(), Spec.ObservedRenameAllowed();
  }

  lemma BackupSelectionCallsImpliesObservedPath(
    cmd: Schema.MvCmd, fs: BW.FileSystem, target: string,
    evidence: Core.BackupSelectionEvidence, calls: seq<Spec.StatusCallEvidence>
  )
    requires Core.BackupSelectionFromStatusCallsFor(cmd.backupMode, cmd.backupSuffix,
                                                    fs, target, evidence, calls)
    ensures Spec.BackupPathFromObservations(cmd, fs, target, calls,
                                            if evidence.SelectedBackup? then evidence.backupPath else "")
  {
    BackupStatusSuffixCoreImpliesSpec(cmd.backupMode, fs, target, calls);
  }

  lemma ExistingTargetRenameEvidenceImpliesRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BW.Path,
    evidence: Core.StepEvidence
  )
    requires Core.ExistingTargetRenameEvidenceFor(
               source, target, cmd, preCwd, evidence
             )
    requires evidence.targetFound ==
             Spec.StatusExistsOutcomeFields(evidence.beforeFs, target, false, true, 0)
    requires evidence.sameFile.CheckedSameFile?
    requires evidence.sameFile.backupCollision.CheckedBackupCollision? ==>
               evidence.sameFile.backupCollision.simpleCandidateFollowed.ok ||
               !Spec.StatusExistsOutcomeFields(evidence.beforeFs, BasenameSpec.SimpleBackupPathSpec(target, cmd.backupSuffix), true, true, 0)
    ensures StateModel.ValueExistingTargetRenameEffectRelation(
              source,
              target,
              cmd,
              evidence.beforeFs,
              preCwd,
              evidence.afterFs,
              evidence.outcome
            )
  {
    hide Core.RenameEvidenceFor(), Core.MetadataEvidenceFor(), Core.EntryNameEvidenceFor();
    hide Core.StatusCallsFor(), Spec.StatusCallsFor();
    reveal Core.SameFileEvidenceFor();
    match evidence.sameFile {
      case NoSameFileCheck =>
      case CheckedSameFile(
        sourceMetadata,
        _,
        _,
        sourceEntry,
        targetEntry,
        _,
        collision,
        _
        ) =>
        BackupCollisionEvidenceImpliesSpec(
          cmd,
          evidence.beforeFs,
          source,
          target,
          sourceMetadata,
          sourceEntry,
          targetEntry,
          collision
        );
        if !Core.BackupCollisionDetected(collision) {
          if cmd.backupMode == Schema.BackupOff {
            RenameEvidenceImpliesRelation(
              source,
              target,
              evidence.sourceIsDir,
              evidence.targetFound,
              "",
              cmd.verbose,
              cmd.debug,
              evidence.beforeFs,
              preCwd,
              evidence.afterFs,
              evidence.outcome,
              evidence.renames,
              evidence.backupFs
            );
          } else {
            match evidence.backup {
              case NoBackupSelection =>
              case SelectedBackup(path, _, _, _, _) =>
                BackupSelectionEvidenceImpliesSpec(
                  target,
                  cmd.backupMode,
                  cmd.backupSuffix,
                  evidence.beforeFs,
                  evidence.backup
                );
                RenameEvidenceImpliesRelation(
                  source,
                  target,
                  evidence.sourceIsDir,
                  evidence.targetFound,
                  path,
                  cmd.verbose,
                  cmd.debug,
                  evidence.beforeFs,
                  preCwd,
                  evidence.afterFs,
                  evidence.outcome,
                  evidence.renames,
                  evidence.backupFs
                );
            }
          }
        }
    }
  }

  lemma ParentMetadataFailureEvidenceImpliesEffect(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision.FailedParentStat?
    requires step.sameFile.sourceReferentEntry.NoEntryNameEvidence?
    ensures StateModel.ValueParentMetadataFailureEffect(source, target, cmd,
                                                        step.beforeFs, step.afterFs, step.outcome)
  {
    reveal Core.StepEvidenceFor();
    reveal Core.SameFileEvidenceFor();
    DirectParentDecisionFields(source,target,cmd,step.beforeFs,cwd,step.sameFile);
    var sourceEntry := step.sameFile.sourceEntry;
    var targetEntry := step.sameFile.targetEntry;
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, sourceEntry);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, targetEntry);
    assert cmd.overwriteMode != Schema.OverwriteSkip &&
           cmd.updateMode != Schema.UpdateNone && cmd.updateMode != Schema.UpdateNoneFail;
    assert sourceEntry.leaf == targetEntry.leaf;
    assert !sourceEntry.parentMetadata.ok || !targetEntry.parentMetadata.ok;
    assert step.afterFs == step.beforeFs;
    assert step.outcome == Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(
                                              if !sourceEntry.parentMetadata.ok then sourceEntry.parent else targetEntry.parent,
                                              if !sourceEntry.parentMetadata.ok then sourceEntry.parentMetadata.err else targetEntry.parentMetadata.err), true);
    assert Core.MetadataEvidenceFor(step.beforeFs, sourceEntry.parent, false, sourceEntry.parentMetadata);
    assert Core.MetadataEvidenceFor(step.beforeFs, targetEntry.parent, false, targetEntry.parentMetadata);
    if !sourceEntry.parentMetadata.ok {
      assert IOContract.FileStatusStructureContractFields(step.beforeFs, sourceEntry.parent,
                                                          false, false, sourceEntry.parentMetadata.rawStatus, sourceEntry.parentMetadata.err);
      assert sourceEntry.parentMetadata.err > 0;
      hide *;
      reveal StateModel.ValueParentMetadataFailureEffect(), Spec.ParentMetadataFailure();
      assert exists sp: string, tp: string, failedPath: string,
          status: BW.FileStatus, err: int, leaf: string ::
          sp == sourceEntry.parent && tp == targetEntry.parent && leaf == sourceEntry.leaf &&
          failedPath == sp && status == sourceEntry.parentMetadata.rawStatus &&
          err == sourceEntry.parentMetadata.err &&
          DirnameSpec.DirnameRelation(source, sp) && DirnameSpec.DirnameRelation(target, tp) &&
          BasenameSpec.BasenameRelation(source, leaf) && BasenameSpec.BasenameRelation(target, leaf) &&
          failedPath in {sp, tp} &&
          IOContract.FileStatusStructureContractFields(step.beforeFs, failedPath, false, false, status, err) &&
          err > 0 && step.afterFs == step.beforeFs &&
          step.outcome == Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(failedPath, err), true);
    } else {
      assert !targetEntry.parentMetadata.ok;
      assert IOContract.FileStatusStructureContractFields(step.beforeFs, targetEntry.parent,
                                                          false, false, targetEntry.parentMetadata.rawStatus, targetEntry.parentMetadata.err);
      assert targetEntry.parentMetadata.err > 0;
      hide *;
      reveal StateModel.ValueParentMetadataFailureEffect(), Spec.ParentMetadataFailure();
      assert exists sp: string, tp: string, failedPath: string,
          status: BW.FileStatus, err: int, leaf: string ::
          sp == sourceEntry.parent && tp == targetEntry.parent && leaf == sourceEntry.leaf &&
          failedPath == tp && status == targetEntry.parentMetadata.rawStatus &&
          err == targetEntry.parentMetadata.err &&
          DirnameSpec.DirnameRelation(source, sp) && DirnameSpec.DirnameRelation(target, tp) &&
          BasenameSpec.BasenameRelation(source, leaf) && BasenameSpec.BasenameRelation(target, leaf) &&
          failedPath in {sp, tp} &&
          IOContract.FileStatusStructureContractFields(step.beforeFs, failedPath, false, false, status, err) &&
          err > 0 && step.afterFs == step.beforeFs &&
          step.outcome == Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(failedPath, err), true);
    }
  }

  lemma ParentMetadataFailureStatusImpliesOutcome(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision.FailedParentStat?
    requires step.sameFile.sourceReferentEntry.NoEntryNameEvidence?
    ensures StateModel.ValueObservedParentFailureOutcome(source, target, cmd, step.beforeFs, cwd,
                                                         step.afterFs, step.outcome, step.statusCalls)
    ensures StateModel.ValueObservedMoveOutcome(source, target, cmd, step.beforeFs, cwd,
                                                step.afterFs, step.outcome, step.statusCalls, step.inputs)
  {
    hide *;
    StepEvidenceImpliesObservedOutcome(source, target, cmd, cwd, step);
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    reveal Core.MetadataStatusCall(), Spec.StatusRequest();
    DirectParentDecisionFields(source, target, cmd, step.beforeFs, cwd, step.sameFile);
    var sourceEntry := step.sameFile.sourceEntry;
    var targetEntry := step.sameFile.targetEntry;
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, sourceEntry);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, targetEntry);
    assert sourceEntry.leaf == targetEntry.leaf;
    assert |step.statusCalls| == 4;
    assert step.statusCalls[0].ok && step.statusCalls[1].ok;
    assert !step.statusCalls[2].ok || !step.statusCalls[3].ok;
    assert exists leaf: string :: BasenameSpec.BasenameRelation(source, leaf) &&
                                  BasenameSpec.BasenameRelation(target, leaf);
    assert step.afterFs == step.beforeFs;
    assert step.outcome == Spec.MoveOutcome([], Spec.ParentStatFailureMessageSpec(
                                              if !step.statusCalls[2].ok then sourceEntry.parent else targetEntry.parent,
                                              if !step.statusCalls[2].ok then step.statusCalls[2].err else step.statusCalls[3].err), true);
    assert Spec.StatusRequest(step.statusCalls[2], step.beforeFs, sourceEntry.parent, false);
    assert Spec.StatusRequest(step.statusCalls[3], step.beforeFs, targetEntry.parent, false);
    hide *;
    reveal StateModel.ValueObservedParentFailureOutcome();
  }

  lemma ParentMetadataFailureEvidenceImpliesObservedStep(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence, observations: Spec.NativeStatusInputs
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires Core.StatusCallsFor(observations, step.firstStatus, step.statusCalls)
    requires step.inputs == observations
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision.FailedParentStat?
    requires step.sameFile.sourceReferentEntry.NoEntryNameEvidence?
    ensures StateModel.ValueObservedStepRelation(source, target, cmd, step.beforeFs, cwd,
                                                 step.afterFs, step.outcome, observations, step.firstStatus,
                                                 step.firstStatus + |step.statusCalls|, step.statusCalls)
  {
    hide *;
    StepStatusEvidenceImpliesObservedStep(source, target, cmd, cwd, step, observations);
  }

  lemma DirectParentDecisionFields(
    source: string, target: string, cmd: Schema.MvCmd, fs: BW.FileSystem, cwd: BW.Path,
    same: Core.SameFileEvidence
  )
    requires Core.SameFileEvidenceFor(cmd, fs, cwd, source, target, same)
    requires same.CheckedSameFile?
    ensures (same.sourceEntry.leaf == same.targetEntry.leaf &&
             (!same.sourceEntry.parentMetadata.ok || !same.targetEntry.parentMetadata.ok)) ==
            (same.decision.FailedParentStat? && same.sourceReferentEntry.NoEntryNameEvidence?)
  {
    hide *;
    reveal Core.SameFileEvidenceFor();
  }

  lemma FailedParentDecisionImpliesObservedFault(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision.FailedParentStat?
    ensures Spec.ObservedMetadataFault(source, step.beforeFs, cwd, step.statusCalls, step.inputs)
  {
    hide *;
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    reveal Core.MetadataEvidenceFor(), Core.MetadataStatusCall();
    var same := step.sameFile;
    DirectParentDecisionFields(source, target, cmd, step.beforeFs, cwd, same);
    if same.sourceReferentEntry.NoEntryNameEvidence? {
      EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, same.sourceEntry);
      EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, same.targetEntry);
      assert same.sourceEntry.leaf == same.targetEntry.leaf;
      assert step.statusCalls[1].path == target;
      assert exists leaf: string :: leaf == same.sourceEntry.leaf &&
                                    BasenameSpec.BasenameRelation(source, leaf) && BasenameSpec.BasenameRelation(target, leaf);
    } else {
      assert same.sourceReferentEntry.SomeEntryNameEvidence?;
      assert |step.statusCalls| >= 6;
      assert !step.statusCalls[3].ok || !step.statusCalls[5].ok;
    }
    reveal Spec.ObservedMetadataFault();
  }

  lemma {:isolate_assertions} StepEvidenceImpliesOriginalEffectWithoutFault(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BW.Path,
    evidence: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(
               source, target, cmd, preCwd, evidence
             )
    requires !Spec.ObservedMetadataFault(source, evidence.beforeFs, preCwd,
                                         evidence.statusCalls, evidence.inputs)
    ensures StateModel.ValueOriginalMoveEffectRelation(source, target, cmd,
                                                       evidence.beforeFs, preCwd, evidence.afterFs, evidence.outcome)
  {
    hide Spec.RenameAllowed(), Spec.ExistingTargetRenameAllowed(), Spec.SameFileMustBeRejected();
    reveal StateModel.ValueRenameEffectRelation(), StateModel.ValueExistingTargetRenameEffectRelation();
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    reveal Core.SourceResolutionObservationFor(), IOContract.ResolvePathIdentitySpec();
    reveal IOContract.NativeFailureContractFields();
    assert (forall i: nat | i < |evidence.statusCalls| :: evidence.statusCalls[i].ok ||
                                                          !Spec.StatusExistsOutcomeFields(evidence.statusCalls[i].fs, evidence.statusCalls[i].path,
                                                                                          evidence.statusCalls[i].followSymlink, true, 0));
    assert IOContract.IsDirectoryStrictContractFields(evidence.beforeFs, source, false,
                                                      evidence.sourceOk, evidence.sourceIsDir, evidence.sourceErr);
    if !evidence.sourceOk {
      assert evidence.afterFs == evidence.beforeFs && evidence.outcome == Spec.MoveOutcome([],
                                                                                           Spec.SourceStatFailureMessageSpec(source, evidence.sourceErr), true);
    } else {
      assert Spec.StatusExistsOutcomeFields(evidence.beforeFs, target, false,
                                            evidence.targetFound, evidence.targetExistsErr);
      if !evidence.targetFound {
        RenameEvidenceImpliesRelation(source, target, evidence.sourceIsDir, false, "",
                                      cmd.verbose, cmd.debug, evidence.beforeFs, preCwd, evidence.afterFs,
                                      evidence.outcome, evidence.renames, evidence.backupFs);
      } else if cmd.overwriteMode == Schema.OverwriteSkip || cmd.updateMode == Schema.UpdateNone {
        assert evidence.afterFs == evidence.beforeFs && evidence.outcome ==
                                                        Spec.MoveOutcome(Spec.SkipStdoutSpec(target, cmd.debug), [], false);
      } else if cmd.updateMode == Schema.UpdateNoneFail {
        assert evidence.afterFs == evidence.beforeFs && evidence.outcome ==
                                                        Spec.MoveOutcome([], Spec.NotReplacingMessageSpec(target), true);
      } else {
        assert evidence.sameFile.CheckedSameFile?;
        var same := evidence.sameFile;
        if same.decision.FailedParentStat? {
          FailedParentDecisionImpliesObservedFault(source, target, cmd, preCwd, evidence);
          assert false;
        }
        assert same.source.isSymlink ==> same.sourceReferentEntry.SomeEntryNameEvidence?;
        SameFileEvidenceImpliesPolicy(cmd, evidence.beforeFs, preCwd, source, target, same);
        if same.decision == Core.RejectSameFile {
          assert evidence.afterFs == evidence.beforeFs && evidence.outcome ==
                                                          Spec.MoveOutcome([], Spec.SameFileMessageSpec(source, target), true);
        } else if cmd.updateMode == Schema.UpdateOlder && !Spec.SourceNewerSpec(
                    same.source.times.mtimeSec, same.source.times.mtimeNsec,
                    same.target.times.mtimeSec, same.target.times.mtimeNsec) {
          assert evidence.afterFs == evidence.beforeFs && evidence.outcome ==
                                                          Spec.MoveOutcome(Spec.SkipStdoutSpec(target, cmd.debug), [], false);
          assert !Spec.SourceNewerSpec(same.source.times.mtimeSec, same.source.times.mtimeNsec,
                                       same.target.times.mtimeSec, same.target.times.mtimeNsec);
        } else {
          ExistingTargetRenameEvidenceImpliesRelation(source, target, cmd, preCwd, evidence);
          if cmd.updateMode == Schema.UpdateOlder {
            assert Spec.SourceNewerSpec(same.source.times.mtimeSec, same.source.times.mtimeNsec,
                                        same.target.times.mtimeSec, same.target.times.mtimeNsec);
          }
        }
      }
    }
    hide *;
    reveal StateModel.ValueOriginalMoveEffectRelation(), Spec.OriginalMoveAllowed();
    reveal StateModel.ValueRenameEffectRelation(), StateModel.ValueExistingTargetRenameEffectRelation();
    assert StateModel.ValueOriginalMoveEffectRelation(source, target, cmd,
                                                      evidence.beforeFs, preCwd, evidence.afterFs, evidence.outcome);
  }

  lemma StepEvidenceImpliesMoveEffect(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    ensures StateModel.ValueMoveEffectRelation(source, target, cmd,
                                               step.beforeFs, cwd, step.afterFs, step.outcome)
    ensures !Spec.ObservedMetadataFault(source, step.beforeFs, cwd, step.statusCalls, step.inputs) ==>
              StateModel.ValueOriginalMoveEffectRelation(source, target, cmd, step.beforeFs, cwd, step.afterFs, step.outcome)
  {
    reveal Core.StepEvidenceFor();
    if Spec.ObservedMetadataFault(source, step.beforeFs, cwd, step.statusCalls, step.inputs) {
      StepEvidenceImpliesObservedOutcome(source, target, cmd, cwd, step);
      reveal Core.StepEvidenceFor();
      assert exists inputs: Spec.NativeStatusInputs, first: nat, calls: seq<Spec.StatusCallEvidence> ::
          inputs == step.inputs && first == step.firstStatus && calls == step.statusCalls &&
          Spec.StatusCallsFor(inputs, first, calls) &&
          StateModel.ValueObservedMoveOutcome(source, target, cmd, step.beforeFs, cwd, step.afterFs, step.outcome, calls, inputs) &&
          Spec.ObservedMetadataFault(source, step.beforeFs, cwd, calls, inputs);
    } else {
      StepEvidenceImpliesOriginalEffectWithoutFault(source, target, cmd, cwd, step);
    }
  }

  lemma CapturedSameFileDecisionScalarFields(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    fs: BW.FileSystem, same: Core.SameFileEvidence
  )
    requires Core.SameFileEvidenceFor(cmd,fs,cwd,source,target,same)
    requires same.CheckedSameFile?
    requires !same.decision.FailedParentStat? || same.sourceReferentEntry.SomeEntryNameEvidence?
    ensures same.decision.FailedParentStat? ==
            (same.sourceReferentEntry.SomeEntryNameEvidence? &&
             same.sourceReferentEntry.value.leaf == same.targetEntry.leaf &&
             (!same.sourceReferentEntry.value.parentMetadata.ok || !same.targetEntry.parentMetadata.ok))
    ensures !same.decision.FailedParentStat? ==>
              (same.decision == Core.RejectSameFile) ==
              (Core.EvidenceNamesSame(same.sourceEntry,same.targetEntry) ||
               (cmd.backupMode == Schema.BackupOff &&
                (same.source.key == same.target.key ||
                 Core.ReferentEvidenceNamesTarget(same.sourceReferentEntry,same.targetEntry))))
  {
    hide *;
    DirectParentDecisionFields(source,target,cmd,fs,cwd,same);
    reveal Core.SameFileEvidenceFor();
  }

  lemma CapturedSameFileDecisionMatchesObservations(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires step.sameFile.CheckedSameFile?
    requires !step.sameFile.decision.FailedParentStat? ||
             step.sameFile.sourceReferentEntry.SomeEntryNameEvidence?
    ensures
      var referent := step.sameFile.sourceReferentEntry;
      var resolved := if referent.SomeEntryNameEvidence? then referent.resolvedPath else "";
      Spec.ObservedReferentParentFailure(step.statusCalls, step.sameFile.targetEntry.leaf,
                                         referent.SomeEntryNameEvidence?, resolved) == step.sameFile.decision.FailedParentStat?
    ensures !step.sameFile.decision.FailedParentStat? ==>
              var referent := step.sameFile.sourceReferentEntry;
              var resolved := if referent.SomeEntryNameEvidence? then referent.resolvedPath else "";
              Spec.ObservedSameFileRejection(cmd, step.statusCalls, step.sameFile.sourceEntry.leaf,
                                             step.sameFile.targetEntry.leaf, referent.SomeEntryNameEvidence?, resolved) ==
              (step.sameFile.decision == Core.RejectSameFile)
  {
    hide IOContract.GetFileStatusResultFields(), IOContract.FileStatusStructureContractFields();
    hide Core.StatusCallsFor(), Spec.StatusCallsFor();
    hide Core.SourceResolutionObservationFor(), Core.RenameNativeObservationsFor();
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    CapturedSameFileDecisionScalarFields(source,target,cmd,cwd,step.beforeFs,step.sameFile);
    var sourceEntry := step.sameFile.sourceEntry;
    var targetEntry := step.sameFile.targetEntry;
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, sourceEntry);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, targetEntry);
    assert |step.statusCalls| >= 4;
    assert step.sameFile.source.key == step.statusCalls[0].status.hostKey;
    assert step.sameFile.target.key == step.statusCalls[1].status.hostKey;
    assert Core.EvidenceNamesSame(sourceEntry, targetEntry) ==
           (sourceEntry.leaf == targetEntry.leaf && step.statusCalls[2].ok && step.statusCalls[3].ok &&
            step.statusCalls[2].status.hostKey == step.statusCalls[3].status.hostKey);
    assert targetEntry.parentMetadata.ok == step.statusCalls[3].ok;
    if step.sameFile.sourceReferentEntry.SomeEntryNameEvidence? {
      var referent := step.sameFile.sourceReferentEntry;
      EntryNameEvidenceImpliesPathRelations(step.beforeFs, referent.resolvedPath, referent.value);
      assert |step.statusCalls| >= 6;
      assert referent.value.parentMetadata.ok == step.statusCalls[5].ok;
      assert BasenameSpec.BasenameRelation(referent.resolvedPath,referent.value.leaf);
      assert forall leaf: string | BasenameSpec.BasenameRelation(referent.resolvedPath, leaf) ::
          leaf == referent.value.leaf by {
        forall leaf: string | BasenameSpec.BasenameRelation(referent.resolvedPath, leaf)
          ensures leaf == referent.value.leaf
        {
          BasenameRelationFunctional(referent.resolvedPath, referent.value.leaf, leaf);
        }
      }
    }
    if step.sameFile.sourceReferentEntry.SomeEntryNameEvidence? {
      var referent := step.sameFile.sourceReferentEntry;
      assert (exists leaf: string :: BasenameSpec.BasenameRelation(referent.resolvedPath,leaf) &&
                                     leaf == targetEntry.leaf) == (referent.value.leaf == targetEntry.leaf) by {
        hide *;
      }
    }
    var referent := step.sameFile.sourceReferentEntry;
    var resolved := if referent.SomeEntryNameEvidence? then referent.resolvedPath else "";
    assert Core.ReferentEvidenceNamesTarget(referent, targetEntry) ==
           (referent.SomeEntryNameEvidence? && |step.statusCalls| >= 6 &&
            step.statusCalls[3].ok && step.statusCalls[5].ok &&
            step.statusCalls[3].status.hostKey == step.statusCalls[5].status.hostKey &&
            (exists leaf: string :: BasenameSpec.BasenameRelation(resolved, leaf) && leaf == targetEntry.leaf));
    assert Spec.ObservedReferentParentFailure(step.statusCalls, targetEntry.leaf,
                                              referent.SomeEntryNameEvidence?, resolved) == step.sameFile.decision.FailedParentStat? by {
      hide *;
      reveal Spec.ObservedReferentParentFailure();
    }
    if !step.sameFile.decision.FailedParentStat? {
      assert Spec.ObservedSameFileRejection(cmd, step.statusCalls, sourceEntry.leaf,
                                            targetEntry.leaf, referent.SomeEntryNameEvidence?, resolved) ==
             (step.sameFile.decision == Core.RejectSameFile) by {
        hide *;
        reveal Spec.ObservedSameFileRejection();
      }
    }
    hide *;

  }

  lemma ContinuingStepStatusTail(
    source: string, target: string, cmd: Schema.MvCmd, step: Core.StepEvidence
  )
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires step.sourceOk && step.targetFound
    requires cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
             cmd.updateMode != Schema.UpdateNoneFail
    requires step.sameFile.CheckedSameFile? && step.sameFile.decision == Core.ContinueMove
    requires cmd.updateMode != Schema.UpdateOlder || Spec.SourceNewerSpec(
               step.sameFile.source.times.mtimeSec, step.sameFile.source.times.mtimeNsec,
               step.sameFile.target.times.mtimeSec, step.sameFile.target.times.mtimeNsec)
    ensures
      var same := step.sameFile;
      var afterEntries := if same.source.isSymlink then
                            (if same.sourceReferentEntry.SomeEntryNameEvidence? then 6 else 5) else 4;
      var collisionNeeded :=
        (cmd.backupMode == Schema.BackupSimple || cmd.backupMode == Schema.BackupExisting) &&
        same.sourceEntry.leaf == same.targetEntry.leaf + cmd.backupSuffix;
      var afterCollision := afterEntries + (if collisionNeeded then 1 else 0);
      afterCollision <= |step.statusCalls| &&
      (collisionNeeded ==>
         same.backupCollision.CheckedBackupCollision? &&
         step.statusCalls[afterEntries] == Core.MetadataStatusCall(step.beforeFs,
                                                                   BasenameSpec.SimpleBackupPathSpec(target, cmd.backupSuffix), true,
                                                                   same.backupCollision.simpleCandidateFollowed)) &&
      (!Core.BackupCollisionDetected(same.backupCollision) ==>
         Core.BackupSelectionFromStatusCallsFor(cmd.backupMode, cmd.backupSuffix,
                                                step.beforeFs, target, step.backup, step.statusCalls[afterCollision..]))
  {
    hide *;
    reveal Core.StepStatusEvidenceFor();
  }

  lemma DirectParentEvidenceImpliesComparisonObservations(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires Core.SameFileEvidenceFor(cmd, step.beforeFs, cwd, source, target, step.sameFile)
    requires step.sourceOk && step.targetFound && step.sameFile.CheckedSameFile?
    requires cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
             cmd.updateMode != Schema.UpdateNoneFail
    requires step.sameFile.decision.FailedParentStat? &&
             step.sameFile.sourceReferentEntry.NoEntryNameEvidence?
    ensures Spec.MoveComparisonObservations(step.beforeFs, cwd, source, target,
                                            step.statusCalls, step.sameFile.sourceEntry.parent, step.sameFile.targetEntry.parent,
                                            step.sameFile.sourceEntry.leaf, step.sameFile.targetEntry.leaf,
                                            false, "", 0, 4, step.inputs)
  {
    hide *;
    reveal Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    reveal Core.MetadataStatusCall(), Spec.StatusRequest();
    var same := step.sameFile;
    var sourceEntry := same.sourceEntry;
    var targetEntry := same.targetEntry;
    DirectParentDecisionFields(source, target, cmd, step.beforeFs, cwd, same);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, sourceEntry);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, targetEntry);
    assert |step.statusCalls| == 4;
    assert step.statusCalls[0].ok && step.statusCalls[1].ok;
    assert sourceEntry.leaf == targetEntry.leaf;
    assert !step.statusCalls[2].ok || !step.statusCalls[3].ok;
    assert Spec.StatusRequest(step.statusCalls[2], step.beforeFs, sourceEntry.parent, false);
    assert Spec.StatusRequest(step.statusCalls[3], step.beforeFs, targetEntry.parent, false);
    reveal Spec.MoveComparisonObservations();
  }

  lemma ComparisonEvidenceImpliesStatusObservations(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires Core.SameFileEvidenceFor(cmd, step.beforeFs, cwd, source, target, step.sameFile)
    requires Core.SourceResolutionObservationFor(source, cwd, step)
    requires step.sourceOk && step.targetFound && step.sameFile.CheckedSameFile?
    requires cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
             cmd.updateMode != Schema.UpdateNoneFail
    requires !step.sameFile.decision.FailedParentStat? ||
             !step.sameFile.sourceReferentEntry.NoEntryNameEvidence?
    requires |step.statusCalls| >= 4
    requires step.sameFile.source.isSymlink ==
             (step.statusCalls[0].status.kind == BW.SymlinkKind)
    ensures
      var same := step.sameFile;
      var referent := same.sourceReferentEntry;
      var resolveOk := referent.SomeEntryNameEvidence?;
      var resolved := if resolveOk then referent.resolvedPath else "";
      var resolveErr := if referent.FailedEntryNameEvidence? then referent.err else 0;
      var afterEntries := if same.source.isSymlink then (if resolveOk then 6 else 5) else 4;
      Spec.MoveComparisonObservations(step.beforeFs, cwd, source, target, step.statusCalls,
                                      same.sourceEntry.parent, same.targetEntry.parent, same.sourceEntry.leaf, same.targetEntry.leaf,
                                      resolveOk, resolved, resolveErr, afterEntries, step.inputs)
  {
    hide *;
    reveal Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    reveal Core.SourceResolutionObservationFor(), Core.MetadataStatusCall();
    reveal Spec.StatusRequest();
    var same := step.sameFile;
    var sourceEntry := same.sourceEntry;
    var targetEntry := same.targetEntry;
    DirectParentDecisionFields(source, target, cmd, step.beforeFs, cwd, same);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, sourceEntry);
    EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, targetEntry);
    assert sourceEntry.leaf != targetEntry.leaf ||
           (sourceEntry.parentMetadata.ok && targetEntry.parentMetadata.ok);
    if same.source.isSymlink {
      match same.sourceReferentEntry {
        case SomeEntryNameEvidence(resolved, referentEntry) =>
          EntryNameEvidenceImpliesPathRelations(step.beforeFs, resolved, referentEntry);
          assert exists parent: string :: parent == referentEntry.parent &&
                                          DirnameSpec.DirnameRelation(resolved, parent) &&
                                          Spec.StatusRequest(step.statusCalls[5], step.beforeFs, parent, false);
        case FailedEntryNameEvidence(_) =>
        case NoEntryNameEvidence =>
      }
    }
    reveal Spec.MoveComparisonObservations();
  }

  lemma CheckedStepImpliesObservedClassification(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    requires step.sameFile.CheckedSameFile?
    ensures
      var same := step.sameFile;
      var referent := same.sourceReferentEntry;
      var resolveOk := referent.SomeEntryNameEvidence?;
      var resolved := if resolveOk then referent.resolvedPath else "";
      var resolveErr := if referent.FailedEntryNameEvidence? then referent.err else 0;
      var afterEntries := if same.decision.FailedParentStat? && referent.NoEntryNameEvidence? then 4
                          else if same.source.isSymlink then (if resolveOk then 6 else 5) else 4;
      StateModel.ValueObservedClassificationOutcome(source, target, cmd, step.beforeFs, cwd,
                                                    step.afterFs, step.outcome, step.statusCalls, step.inputs,
                                                    (same.sourceEntry.parent, same.targetEntry.parent, same.sourceEntry.leaf, same.targetEntry.leaf),
                                                    resolveOk, resolved, resolveErr, afterEntries)
  {
    hide IOContract.GetFileStatusResultFields(), IOContract.FileStatusStructureContractFields();
    hide Core.StatusCallsFor(), Spec.StatusCallsFor(), Core.RenameNativeObservationsFor();
    hide Core.RenameEvidenceFor(), Core.BackupSelectionFromStatusCallsFor();
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor(), Core.SameFileEvidenceFor();
    assert |step.statusCalls| >= 4;
    var same := step.sameFile;
    var referent := same.sourceReferentEntry;
    var resolveOk := referent.SomeEntryNameEvidence?;
    var resolved := if resolveOk then referent.resolvedPath else "";
    var resolveErr := if referent.FailedEntryNameEvidence? then referent.err else 0;
    var afterEntries: nat := if same.decision.FailedParentStat? && referent.NoEntryNameEvidence? then 4
    else if same.source.isSymlink then (if resolveOk then 6 else 5) else 4;
    if same.decision.FailedParentStat? && referent.NoEntryNameEvidence? {
      DirectParentEvidenceImpliesComparisonObservations(source, target, cmd, cwd, step);
    } else {
      CapturedSameFileDecisionMatchesObservations(source, target, cmd, cwd, step);
      ComparisonEvidenceImpliesStatusObservations(source, target, cmd, cwd, step);
    }
    if same.decision.FailedParentStat? || same.decision == Core.RejectSameFile ||
       (cmd.updateMode == Schema.UpdateOlder && !Spec.SourceNewerSpec(
          same.source.times.mtimeSec, same.source.times.mtimeNsec,
          same.target.times.mtimeSec, same.target.times.mtimeNsec)) {
      assert |step.statusCalls| == afterEntries;
    }
    if same.decision.FailedParentStat? {
      if referent.SomeEntryNameEvidence? {
        EntryNameEvidenceImpliesPathRelations(step.beforeFs, referent.resolvedPath, referent.value);
      }
    } else if same.decision == Core.ContinueMove &&
              (cmd.updateMode != Schema.UpdateOlder || Spec.SourceNewerSpec(
                 same.source.times.mtimeSec, same.source.times.mtimeNsec,
                 same.target.times.mtimeSec, same.target.times.mtimeNsec)) {
      reveal Core.ExistingTargetRenameEvidenceFor();
      ContinuingStepStatusTail(source, target, cmd, step);
      var collisionNeeded :=
        (cmd.backupMode == Schema.BackupSimple || cmd.backupMode == Schema.BackupExisting) &&
        same.sourceEntry.leaf == same.targetEntry.leaf + cmd.backupSuffix;
      var afterCollision := afterEntries + (if collisionNeeded then 1 else 0);
      if collisionNeeded {
        assert Spec.StatusRequest(step.statusCalls[afterEntries], step.beforeFs,
                                  BasenameSpec.SimpleBackupPathSpec(target, cmd.backupSuffix), true);
        assert Core.BackupCollisionDetected(same.backupCollision) ==
               (step.statusCalls[afterEntries].ok &&
                step.statusCalls[afterEntries].status.hostKey == step.statusCalls[0].status.hostKey);
      } else {
        assert !Core.BackupCollisionDetected(same.backupCollision);
      }
      if Core.BackupCollisionDetected(same.backupCollision) {
        assert |step.statusCalls| == afterCollision;
      } else {
        assert Core.BackupSelectionFromStatusCallsFor(
            cmd.backupMode, cmd.backupSuffix, step.beforeFs, target,
            step.backup, step.statusCalls[afterCollision..]);
        assert Spec.BackupStatusSuffix(cmd.backupMode, step.beforeFs, target,
                                       step.statusCalls[afterCollision..]) by {
          reveal Core.BackupSelectionFromStatusCallsFor();
          BackupStatusSuffixCoreImpliesSpec(cmd.backupMode, step.beforeFs, target,
                                            step.statusCalls[afterCollision..]);
        }
        BackupSelectionCallsImpliesObservedPath(cmd, step.beforeFs, target,
                                                step.backup, step.statusCalls[afterCollision..]);
        var backupPath := if step.backup.SelectedBackup? then step.backup.backupPath else "";
        RenameNativeEvidenceImpliesObservedRelation(source, target, cmd, cwd, step, backupPath);
      }
    }
  }

  lemma StepEvidenceImpliesObservedOutcome(
    source: string, target: string, cmd: Schema.MvCmd, cwd: BW.Path,
    step: Core.StepEvidence
  )
    requires Core.StepEvidenceFor(source, target, cmd, cwd, step)
    ensures StateModel.ValueObservedMoveOutcome(source, target, cmd, step.beforeFs, cwd,
                                                step.afterFs, step.outcome, step.statusCalls, step.inputs)
  {
    reveal Core.StepEvidenceFor(), Core.StepStatusEvidenceFor();
    if step.sourceOk && !step.targetFound {
      RenameNativeEvidenceImpliesObservedRelation(source, target, cmd, cwd, step, "");
    } else if step.sourceOk && step.targetFound &&
              cmd.overwriteMode != Schema.OverwriteSkip && cmd.updateMode != Schema.UpdateNone &&
              cmd.updateMode != Schema.UpdateNoneFail {
      assert Spec.EntryNameSpec(source) ==
               Spec.EntryName(step.sameFile.sourceEntry.parent, step.sameFile.sourceEntry.leaf) &&
             Spec.EntryNameSpec(target) ==
               Spec.EntryName(step.sameFile.targetEntry.parent, step.sameFile.targetEntry.leaf) by {
        reveal Core.SameFileEvidenceFor();
        EntryNameEvidenceImpliesPathRelations(step.beforeFs, source, step.sameFile.sourceEntry);
        EntryNameEvidenceImpliesPathRelations(step.beforeFs, target, step.sameFile.targetEntry);
      }
      CheckedStepImpliesObservedClassification(source, target, cmd, cwd, step);
    }
  }

  lemma {:isolate_assertions} StepStatusEvidenceImpliesObservedStep(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    preCwd: BW.Path,
    step: Core.StepEvidence,
    observations: Spec.NativeStatusInputs
  )
    requires Core.StepEvidenceFor(source, target, cmd, preCwd, step)
    requires Core.StepStatusEvidenceFor(source, target, cmd, step)
    requires Core.StatusCallsFor(
               observations, step.firstStatus, step.statusCalls)
    requires step.inputs == observations
    ensures StateModel.ValueObservedStepRelation(
              source, target, cmd, step.beforeFs, preCwd,
              step.afterFs, step.outcome, observations,
              step.firstStatus,
              step.firstStatus + |step.statusCalls|,
              step.statusCalls
            )
  {
    StepEvidenceImpliesMoveEffect(source, target, cmd, preCwd, step);
    StepEvidenceImpliesObservedOutcome(source, target, cmd, preCwd, step);
  }

  lemma BatchStepEvidenceImpliesMoveEffect(
    source: string,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    outcome: Spec.MoveOutcome,
    stdoutFragment: BW.Bytes,
    stderrFragment: BW.Bytes,
    step: Core.StepEvidence
  )
    requires Core.BatchStepEvidenceFor(
               source,
               directory,
               cmd,
               beforeFs,
               preCwd,
               afterFs,
               outcome,
               stdoutFragment,
               stderrFragment,
               step
             )
    ensures
      var normalized :=
        Spec.NormalizeSourceSpec(
          source, cmd.stripTrailingSlashes
        );
      StateModel.ValueMoveEffectRelation(
        normalized,
        Spec.TargetInDirectorySpec(directory, normalized),
        cmd,
        beforeFs,
        preCwd,
        afterFs,
        outcome
      ) &&
      stdoutFragment == outcome.stdoutFragment &&
      stderrFragment == outcome.stderrFragment
  {
    reveal Core.BatchStepEvidenceFor();
    var normalizedCore :=
      Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes);
    StepEvidenceImpliesMoveEffect(
      normalizedCore,
      Spec.TargetInDirectorySpec(directory, normalizedCore),
      cmd,
      preCwd,
      step
    );
  }

  lemma BatchMoveComponentsImplyWitnessRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    hadError: bool,
    out: BW.Bytes,
    err: BW.Bytes,
    fsBounds: seq<BW.FileSystem>,
    outcomes: seq<Spec.MoveOutcome>,
    stdoutFragments: seq<BW.Bytes>,
    stderrFragments: seq<BW.Bytes>
  )
    requires |fsBounds| == |sources| + 1
    requires |outcomes| == |sources|
    requires |stdoutFragments| == |sources|
    requires |stderrFragments| == |sources|
    requires fsBounds[0] == beforeFs
    requires fsBounds[|fsBounds| - 1] == afterFs
    requires forall i: nat | i < |sources| ::
               var normalizedSource :=
                 Spec.NormalizeSourceSpec(
                   sources[i], cmd.stripTrailingSlashes
                 );
               StateModel.ValueMoveEffectRelation(
                 normalizedSource,
                 Spec.TargetInDirectorySpec(directory, normalizedSource),
                 cmd,
                 fsBounds[i],
                 preCwd,
                 fsBounds[i + 1],
                 outcomes[i]
               )
    requires forall i: nat | i < |sources| ::
               stdoutFragments[i] == outcomes[i].stdoutFragment
    requires forall i: nat | i < |sources| ::
               stderrFragments[i] == outcomes[i].stderrFragment
    requires Spec.ConcatenateFragments(stdoutFragments) == out
    requires Spec.ConcatenateFragments(stderrFragments) == err
    requires hadError <==>
             exists i: nat :: i < |outcomes| && outcomes[i].failed
    ensures StateModel.ValueBatchMoveWitnessRelation(
              sources,
              directory,
              cmd,
              beforeFs,
              preCwd,
              afterFs,
              hadError,
              out,
              err,
              fsBounds,
              outcomes,
              stdoutFragments,
              stderrFragments
            )
  {
    hide StateModel.ValueMoveEffectRelation;
    forall i: nat {:trigger stdoutFragments[i]} | i < |sources|
      ensures
        var normalizedSource :=
          Spec.NormalizeSourceSpec(
            sources[i], cmd.stripTrailingSlashes
          );
        StateModel.ValueMoveEffectRelation(
          normalizedSource,
          Spec.TargetInDirectorySpec(directory, normalizedSource),
          cmd,
          fsBounds[i],
          preCwd,
          fsBounds[i + 1],
          outcomes[i]
        ) &&
        stdoutFragments[i] == outcomes[i].stdoutFragment &&
        stderrFragments[i] == outcomes[i].stderrFragment
    {
      var normalizedSource :=
        Spec.NormalizeSourceSpec(
          sources[i], cmd.stripTrailingSlashes
        );
      assert StateModel.ValueMoveEffectRelation(
          normalizedSource,
          Spec.TargetInDirectorySpec(directory, normalizedSource),
          cmd,
          fsBounds[i],
          preCwd,
          fsBounds[i + 1],
          outcomes[i]
        );
      assert stdoutFragments[i] == outcomes[i].stdoutFragment;
      assert stderrFragments[i] == outcomes[i].stderrFragment;
    }
    reveal StateModel.ValueBatchMoveWitnessRelation();
  }

  lemma {:vcs_split_on_every_assert} BatchEvidenceImpliesMoveRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    hadError: bool,
    out: BW.Bytes,
    err: BW.Bytes,
    evidence: Core.BatchEvidence
  )
    requires Core.BatchEvidenceFor(
               sources, directory, cmd, beforeFs, preCwd, afterFs,
               hadError, out, err, evidence
             )
    ensures StateModel.ValueBatchMoveRelation(
              sources, directory, cmd, beforeFs, preCwd, afterFs,
              hadError, out, err
            )
    ensures StateModel.ValueBatchMoveWitnessRelation(
              sources, directory, cmd, beforeFs, preCwd, afterFs,
              hadError, out, err,
              evidence.fsBounds, evidence.outcomes,
              evidence.stdoutFragments, evidence.stderrFragments
            )
  {
    reveal Core.BatchEvidenceFor();
    assert |evidence.steps| == |sources|;
    assert |evidence.fsBounds| == |sources| + 1;
    assert |evidence.outcomes| == |sources|;
    assert |evidence.stdoutFragments| == |sources|;
    assert |evidence.stderrFragments| == |sources|;
    assert evidence.fsBounds[0] == beforeFs;
    assert evidence.fsBounds[|evidence.fsBounds| - 1] == afterFs;
    assert Spec.ConcatenateFragments(
        evidence.stdoutFragments
      ) == out;
    assert Spec.ConcatenateFragments(
        evidence.stderrFragments
      ) == err;
    assert hadError <==>
           exists i: nat ::
             i < |evidence.outcomes| &&
             evidence.outcomes[i].failed;
    hide StateModel.ValueMoveEffectRelation;
    forall i: nat | i < |sources|
      ensures
        var normalizedSpec :=
          Spec.NormalizeSourceSpec(
            sources[i], cmd.stripTrailingSlashes
          );
        StateModel.ValueMoveEffectRelation(
          normalizedSpec,
          Spec.TargetInDirectorySpec(
            directory, normalizedSpec
          ),
          cmd,
          evidence.fsBounds[i],
          preCwd,
          evidence.fsBounds[i + 1],
          evidence.outcomes[i]
        )
      ensures evidence.stdoutFragments[i] ==
              evidence.outcomes[i].stdoutFragment
      ensures evidence.stderrFragments[i] ==
              evidence.outcomes[i].stderrFragment
    {
      assert Core.BatchStepEvidenceFor(
          sources[i],
          directory,
          cmd,
          evidence.fsBounds[i],
          preCwd,
          evidence.fsBounds[i + 1],
          evidence.outcomes[i],
          evidence.stdoutFragments[i],
          evidence.stderrFragments[i],
          evidence.steps[i]
        );
      BatchStepEvidenceImpliesMoveEffect(
        sources[i],
        directory,
        cmd,
        evidence.fsBounds[i],
        preCwd,
        evidence.fsBounds[i + 1],
        evidence.outcomes[i],
        evidence.stdoutFragments[i],
        evidence.stderrFragments[i],
        evidence.steps[i]
      );
      var normalizedSource :=
        Spec.NormalizeSourceSpec(
          sources[i], cmd.stripTrailingSlashes
        );
      assert StateModel.ValueMoveEffectRelation(
          normalizedSource,
          Spec.TargetInDirectorySpec(directory, normalizedSource),
          cmd,
          evidence.fsBounds[i],
          preCwd,
          evidence.fsBounds[i + 1],
          evidence.outcomes[i]
        );
      assert evidence.stdoutFragments[i] ==
             evidence.outcomes[i].stdoutFragment;
      assert evidence.stderrFragments[i] ==
             evidence.outcomes[i].stderrFragment;
    }
    {
      hide *;
      BatchMoveComponentsImplyWitnessRelation(
        sources,
        directory,
        cmd,
        beforeFs,
        preCwd,
        afterFs,
        hadError,
        out,
        err,
        evidence.fsBounds,
        evidence.outcomes,
        evidence.stdoutFragments,
        evidence.stderrFragments
      );
    }
    BatchMovesFromWitness(sources, directory, cmd, beforeFs, preCwd, afterFs,
                          Spec.MoveOutcome(out, err, hadError), evidence.fsBounds, evidence.outcomes,
                          evidence.stdoutFragments, evidence.stderrFragments);
    reveal StateModel.ValueBatchMoveRelation();
    assert StateModel.ValueBatchMoveRelation(
        sources, directory, cmd, beforeFs, preCwd, afterFs,
        hadError, out, err
      );
  }

  lemma {:induction false} BatchStatusStepInterval(
    observations: Spec.NativeStatusInputs,
    batch: Core.BatchEvidence,
    i: nat
  )
    requires i < |batch.steps|
    requires Core.BatchStatusEvidenceFor(observations, batch)
    ensures Core.StatusCallsFor(
              observations, batch.firstStatus, batch.statusCalls)
    ensures i + 1 < |batch.statusBounds|
    ensures batch.firstStatus <= batch.statusBounds[i] <= batch.statusBounds[i + 1] <=
            batch.firstStatus + |batch.statusCalls|
    ensures batch.steps[i].inputs == observations
    ensures batch.steps[i].firstStatus == batch.statusBounds[i]
    ensures batch.statusBounds[i + 1] ==
            batch.steps[i].firstStatus + |batch.steps[i].statusCalls|
    ensures batch.statusCalls[
            batch.statusBounds[i] - batch.firstStatus ..
            batch.statusBounds[i + 1] - batch.firstStatus] == batch.steps[i].statusCalls
  {
    hide *;
    reveal Core.BatchStatusEvidenceFor();
  }

  lemma {:isolate_assertions} {:induction false} BatchStatusStepImpliesObserved(
    source: string,
    directory: string,
    cmd: Schema.MvCmd,
    preCwd: BW.Path,
    observations: Spec.NativeStatusInputs,
    batch: Core.BatchEvidence,
    i: nat
  )
    requires i < |batch.steps|
    requires i + 1 < |batch.fsBounds|
    requires i < |batch.outcomes|
    requires i < |batch.stdoutFragments|
    requires i < |batch.stderrFragments|
    requires Core.BatchStepEvidenceFor(
               source, directory, cmd, batch.fsBounds[i], preCwd,
               batch.fsBounds[i + 1], batch.outcomes[i],
               batch.stdoutFragments[i], batch.stderrFragments[i], batch.steps[i])
    requires Core.StepStatusEvidenceFor(
               Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes),
               Spec.TargetInDirectorySpec(
                 directory, Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes)),
               cmd, batch.steps[i])
    requires Core.BatchStatusEvidenceFor(observations, batch)
    ensures StateModel.ValueObservedStepRelation(
              Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes),
              Spec.TargetInDirectorySpec(
                directory, Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes)),
              cmd, batch.fsBounds[i], preCwd, batch.fsBounds[i + 1],
              batch.outcomes[i], observations,
              batch.statusBounds[i], batch.statusBounds[i + 1],
              batch.statusCalls[
              batch.statusBounds[i] - batch.firstStatus ..
              batch.statusBounds[i + 1] - batch.firstStatus])
  {
    hide *;
    hide StateModel.ValueObservedStepRelation();
    hide Core.BatchStatusEvidenceFor();
    BatchStatusStepInterval(observations, batch, i);
    var normalizedSource := Spec.NormalizeSourceSpec(
      source, cmd.stripTrailingSlashes);
    reveal Core.BatchStepEvidenceFor();
    assert Core.StepEvidenceFor(
        normalizedSource, Spec.TargetInDirectorySpec(directory, normalizedSource),
        cmd, preCwd, batch.steps[i]);
    assert batch.steps[i].beforeFs == batch.fsBounds[i];
    assert batch.steps[i].afterFs == batch.fsBounds[i + 1];
    assert batch.steps[i].outcome == batch.outcomes[i];
    assert Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes) == normalizedSource;
    assert Spec.TargetInDirectorySpec(directory, normalizedSource) ==
           Spec.TargetInDirectorySpec(directory, normalizedSource);
    var lo := batch.statusBounds[i] - batch.firstStatus;
    var hi := batch.statusBounds[i + 1] - batch.firstStatus;
    assert batch.statusCalls[lo..hi] == batch.steps[i].statusCalls;
    assert batch.steps[i].firstStatus == batch.statusBounds[i];
    assert batch.statusBounds[i + 1] ==
           batch.steps[i].firstStatus + |batch.steps[i].statusCalls|;
    assert Core.StatusCallsFor(
        observations, batch.steps[i].firstStatus,
        batch.steps[i].statusCalls) by {
      hide *;
      reveal Core.StepEvidenceFor();
    }
    StepStatusEvidenceImpliesObservedStep(
      normalizedSource, Spec.TargetInDirectorySpec(directory, normalizedSource),
      cmd, preCwd, batch.steps[i], observations);
    assert StateModel.ValueObservedStepRelation(
        normalizedSource, Spec.TargetInDirectorySpec(directory, normalizedSource),
        cmd, batch.steps[i].beforeFs, preCwd, batch.steps[i].afterFs,
        batch.steps[i].outcome, observations, batch.steps[i].firstStatus,
        batch.steps[i].firstStatus + |batch.steps[i].statusCalls|,
        batch.steps[i].statusCalls);
    assert StateModel.ValueObservedStepRelation(
        Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes),
        Spec.TargetInDirectorySpec(directory, Spec.NormalizeSourceSpec(source, cmd.stripTrailingSlashes)),
        cmd, batch.fsBounds[i], preCwd, batch.fsBounds[i + 1], batch.outcomes[i],
        observations, batch.statusBounds[i], batch.statusBounds[i + 1], batch.statusCalls[lo..hi]);
  }

  lemma {:isolate_assertions} {:induction false} ObservedBatchComponentsImplyRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    hadError: bool,
    out: BW.Bytes,
    err: BW.Bytes,
    observations: Spec.NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<Spec.StatusCallEvidence>,
    fsBounds: seq<BW.FileSystem>,
    outcomes: seq<Spec.MoveOutcome>,
    stdoutFragments: seq<BW.Bytes>,
    stderrFragments: seq<BW.Bytes>,
    statusBounds: seq<nat>
  )
    requires afterStatus == firstStatus + |calls|
    requires Spec.StatusCallsFor(observations, firstStatus, calls)
    requires StateModel.ValueBatchMoveWitnessRelation(
               sources, directory, cmd, beforeFs, preCwd, afterFs,
               hadError, out, err, fsBounds, outcomes, stdoutFragments, stderrFragments)
    requires |fsBounds| == |sources| + 1
    requires |outcomes| == |sources|
    requires |statusBounds| == |sources| + 1
    requires statusBounds[0] == firstStatus
    requires statusBounds[|sources|] == afterStatus
    requires forall i: nat {:trigger statusBounds[i]} | i < |sources| ::
               firstStatus <= statusBounds[i] <= statusBounds[i + 1] <= afterStatus &&
               StateModel.ValueObservedStepRelation(
                 Spec.NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes),
                 Spec.TargetInDirectorySpec(
                   directory, Spec.NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes)),
                 cmd, fsBounds[i], preCwd, fsBounds[i + 1], outcomes[i], observations,
                 statusBounds[i], statusBounds[i + 1],
                 calls[statusBounds[i] - firstStatus .. statusBounds[i + 1] - firstStatus])
    ensures StateModel.ValueObservedBatchRelation(
              sources, directory, cmd, beforeFs, preCwd, afterFs,
              hadError, out, err, observations, firstStatus, afterStatus, calls)
  {
    hide *;
    reveal ObservedBatchIntervals();
    ObservedBatchMovesFromWitness(
      sources, directory, cmd, beforeFs, preCwd, afterFs, Spec.MoveOutcome(out, err, hadError),
      fsBounds, outcomes, stdoutFragments, stderrFragments, observations, firstStatus, calls, statusBounds);
    reveal StateModel.ValueObservedBatchRelation();
  }

  lemma {:isolate_assertions} {:induction false} BatchStatusEvidenceImpliesObservedBatch(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    hadError: bool,
    out: BW.Bytes,
    err: BW.Bytes,
    observations: Spec.NativeStatusInputs,
    batch: Core.BatchEvidence
  )
    requires Core.BatchEvidenceFor(
               sources, directory, cmd, beforeFs, preCwd, afterFs,
               hadError, out, err, batch)
    requires Core.BatchMoveStatusEvidenceFor(
               sources, directory, cmd, observations, batch)
    ensures StateModel.ValueObservedBatchRelation(
              sources, directory, cmd, beforeFs, preCwd, afterFs,
              hadError, out, err, observations,
              batch.firstStatus,
              batch.firstStatus + |batch.statusCalls|,
              batch.statusCalls)
  {
    hide *;
    reveal Core.StatusCallsFor();
    BatchEvidenceImpliesMoveRelation(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      hadError, out, err, batch
    );
    reveal Core.BatchMoveStatusEvidenceFor();
    reveal Core.BatchStatusEvidenceFor();
    reveal Core.BatchEvidenceFor();
    forall i: nat {:trigger batch.statusBounds[i]} | i < |sources|
      ensures batch.firstStatus <= batch.statusBounds[i] <=
              batch.statusBounds[i + 1] <= batch.firstStatus + |batch.statusCalls|
      ensures StateModel.ValueObservedStepRelation(
                Spec.NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes),
                Spec.TargetInDirectorySpec(
                  directory,
                  Spec.NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes)
                ),
                cmd,
                batch.fsBounds[i], preCwd, batch.fsBounds[i + 1],
                batch.outcomes[i], observations,
                batch.statusBounds[i], batch.statusBounds[i + 1],
                batch.statusCalls[
                batch.statusBounds[i] - batch.firstStatus ..
                batch.statusBounds[i + 1] - batch.firstStatus]
              )
    {
      assert Core.BatchStepEvidenceFor(
          sources[i], directory, cmd, batch.fsBounds[i], preCwd,
          batch.fsBounds[i + 1], batch.outcomes[i],
          batch.stdoutFragments[i], batch.stderrFragments[i], batch.steps[i]);
      BatchStatusStepImpliesObserved(
        sources[i], directory, cmd, preCwd, observations, batch, i);
    }
    ObservedBatchComponentsImplyRelation(
      sources, directory, cmd, beforeFs, preCwd, afterFs,
      hadError, out, err, observations,
      batch.firstStatus, batch.firstStatus + |batch.statusCalls|,
      batch.statusCalls, batch.fsBounds, batch.outcomes,
      batch.stdoutFragments, batch.stderrFragments, batch.statusBounds);
  }

  lemma RunIntoDirectoryEvidenceImpliesCandidate(
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    preStdout: BW.Bytes,
    preStderr: BW.Bytes,
    stdout2: BW.Bytes,
    stderr2: BW.Bytes,
    exit: int
  )
    requires Core.RunIntoDirectoryEvidenceFields(
               sources, directory, explicitTargetDirectory, cmd,
               beforeFs, preCwd, afterFs, preStdout, preStderr,
               stdout2, stderr2, exit
             )
    ensures StateModel.ValueCandidateRunIntoDirectoryFields(
              sources, directory, explicitTargetDirectory, cmd,
              beforeFs, preCwd, afterFs, preStdout, preStderr,
              stdout2, stderr2, exit
            )
  {
    forall ok: bool, directoryErr: int
      ensures Core.TargetDirectoryCheckSummaryFields(
                directory, beforeFs, ok, directoryErr
              )
              ==> Spec.TargetDirectoryCheckSpecFields(
                  directory, beforeFs, ok, directoryErr
                )
    {
      if Core.TargetDirectoryCheckSummaryFields(
          directory, beforeFs, ok, directoryErr
        ) {
        TargetDirectoryCheckSummaryFieldsImpliesSpec(
          directory, beforeFs, ok, directoryErr
        );
      }
    }
    forall
    hadError: bool,
      out: BW.Bytes,
      err: BW.Bytes,
      evidence: Core.BatchEvidence
      ensures Core.BatchEvidenceFor(
                sources, directory, cmd, beforeFs, preCwd, afterFs,
                hadError, out, err, evidence
              )
              ==> StateModel.ValueBatchMoveRelation(
                  sources, directory, cmd, beforeFs, preCwd, afterFs,
                  hadError, out, err
                )
    {
      if Core.BatchEvidenceFor(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err, evidence
        ) {
        BatchEvidenceImpliesMoveRelation(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err, evidence
        );
      }
    }
  }

  lemma RunTwoOperandEvidenceImpliesCandidate(
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    preStdout: BW.Bytes,
    preStderr: BW.Bytes,
    stdout2: BW.Bytes,
    stderr2: BW.Bytes,
    exit: int
  )
    requires |cmd.operands| == 2
    requires Core.RunTwoOperandEvidenceFields(
               cmd, beforeFs, preCwd, afterFs, preStdout, preStderr,
               stdout2, stderr2, exit
             )
    ensures StateModel.ValueCandidateRunTwoOperandFields(
              cmd, beforeFs, preCwd, afterFs, preStdout, preStderr,
              stdout2, stderr2, exit
            )
  {
    var sourceCore :=
      Spec.NormalizeSourceSpec(
        cmd.operands[0], cmd.stripTrailingSlashes
      );
    forall step: Core.StepEvidence
      ensures Core.StepEvidenceFor(
                sourceCore, cmd.operands[1], cmd, preCwd, step
              )
              ==> StateModel.ValueMoveEffectRelation(
                  sourceCore,
                  cmd.operands[1],
                  cmd,
                  step.beforeFs,
                  preCwd,
                  step.afterFs,
                  step.outcome
                )
    {
      if Core.StepEvidenceFor(
          sourceCore, cmd.operands[1], cmd, preCwd, step
        ) {
        StepEvidenceImpliesMoveEffect(
          sourceCore, cmd.operands[1], cmd, preCwd, step
        );
      }
    }
    forall
    hadError: bool,
      out: BW.Bytes,
      err: BW.Bytes,
      evidence: Core.BatchEvidence
      ensures Core.BatchEvidenceFor(
                [cmd.operands[0]],
                cmd.operands[1],
                cmd,
                beforeFs,
                preCwd,
                afterFs,
                hadError,
                out,
                err,
                evidence
              )
              ==> StateModel.ValueMoveEffectRelation(
                  sourceCore, Spec.TargetInDirectorySpec(cmd.operands[1], sourceCore), cmd,
                  beforeFs, preCwd, afterFs, Spec.MoveOutcome(out, err, hadError)
                )
    {
      if Core.BatchEvidenceFor(
          [cmd.operands[0]],
          cmd.operands[1],
          cmd,
          beforeFs,
          preCwd,
          afterFs,
          hadError,
          out,
          err,
          evidence
        ) {
        BatchEvidenceImpliesMoveRelation(
          [cmd.operands[0]],
          cmd.operands[1],
          cmd,
          beforeFs,
          preCwd,
          afterFs,
          hadError,
          out,
          err,
          evidence
        );
        reveal StateModel.ValueBatchMoveRelation(), StateModel.ValueMoveEffectRelation();
        SingletonBatchIsMove(cmd.operands[0], cmd.operands[1], cmd, beforeFs, preCwd, afterFs,
                             Spec.MoveOutcome(out, err, hadError));
      }
    }
  }

  lemma TargetDirectoryCheckSummaryFieldsImpliesSpec(directory: string, preFs: BW.FileSystem, ok: bool, err: int)
    requires Core.TargetDirectoryCheckSummaryFields(directory, preFs, ok, err)
    ensures Spec.TargetDirectoryCheckSpecFields(directory, preFs, ok, err)
  {
  }

  lemma PreparedSummaryIOImpliesCandidateSpecFields(
    raw: Schema.MvCmdRaw,
    preFs: BW.FileSystem,
    preCwd: BW.Path,
    preStdout: BW.Bytes,
    preStderr: BW.Bytes,
    io: BenchIO.IO,
    exit: int,
    plannedStdout: BW.Bytes,
    plannedStderr: BW.Bytes
  )
    requires Core.PreparedSummaryIO(
               raw,
               preFs,
               preCwd,
               preStdout,
               preStderr,
               io,
               exit, plannedStdout, plannedStderr
             )
    ensures StateModel.ValueCandidateSpecFields(
              raw,
              preFs,
              preCwd,
              preStdout,
              preStderr,
              io.fs(), plannedStdout, plannedStderr,
              exit
            )
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup {
    } else if cmd.mode == Schema.ModeInvalidUpdate {
    } else if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else if cmd.targetDirectory != "" &&
              cmd.noTargetDirectory {
    } else if |cmd.operands| == 0 {
    } else if cmd.targetDirectory != "" {
      RunIntoDirectoryEvidenceImpliesCandidate(
        cmd.operands,
        cmd.targetDirectory,
        true,
        cmd,
        preFs,
        preCwd,
        io.fs(),
        preStdout,
        preStderr,
        plannedStdout,
        plannedStderr,
        exit
      );
    } else if |cmd.operands| == 1 {
    } else if cmd.noTargetDirectory && |cmd.operands| > 2 {
    } else if |cmd.operands| == 2 {
      RunTwoOperandEvidenceImpliesCandidate(
        cmd,
        preFs,
        preCwd,
        io.fs(),
        preStdout,
        preStderr,
        plannedStdout,
        plannedStderr,
        exit
      );
    } else {
      RunIntoDirectoryEvidenceImpliesCandidate(
        cmd.operands[..|cmd.operands| - 1],
        cmd.operands[|cmd.operands| - 1],
        false,
        cmd,
        preFs,
        preCwd,
        io.fs(),
        preStdout,
        preStderr,
        plannedStdout,
        plannedStderr,
        exit
      );
    }
  }

  lemma {:isolate_assertions} ObservedBatchIntervalSubstitution(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    hadError: bool,
    out: BW.Bytes,
    err: BW.Bytes,
    observations: Spec.NativeStatusInputs,
    batch: Core.BatchEvidence,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<Spec.StatusCallEvidence>
  )
    requires batch.firstStatus == firstStatus + 1
    requires afterStatus == batch.firstStatus + |batch.statusCalls|
    requires |calls| >= 1
    requires calls[1..] == batch.statusCalls
    requires StateModel.ValueObservedBatchRelation(
               sources, directory, cmd, beforeFs, preCwd, afterFs,
               hadError, out, err, observations,
               batch.firstStatus,
               batch.firstStatus + |batch.statusCalls|,
               batch.statusCalls)
    ensures StateModel.ValueObservedBatchRelation(
              sources, directory, cmd, beforeFs, preCwd, afterFs,
              hadError, out, err, observations,
              firstStatus + 1, afterStatus, calls[1..])
  {
    hide StateModel.ValueObservedBatchRelation;
  }

  lemma {:isolate_assertions} DirectoryStatusEvidenceImpliesObservedDirectory(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    beforeStdout: BW.Bytes,
    afterStdout: BW.Bytes,
    beforeStderr: BW.Bytes,
    afterStderr: BW.Bytes,
    exit: int,
    observations: Spec.NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<Spec.StatusCallEvidence>,
    evidence: Core.DirectoryStatusEvidence
  )
    requires afterStatus == firstStatus + |calls|
    requires Core.DirectoryStatusEvidenceFor(
               sources, directory, cmd, beforeFs, preCwd, afterFs,
               beforeStdout, afterStdout, beforeStderr, afterStderr,
               exit, observations, firstStatus, calls, evidence)
    ensures |calls| >= 1
    ensures Spec.StatusRequest(calls[0], beforeFs, directory, true)
    ensures if calls[0].ok &&
               calls[0].status.kind == BW.DirectoryKind then
              exists hadError: bool, out: BW.Bytes, err: BW.Bytes
                {:trigger StateModel.ValueObservedBatchRelation(
                  sources, directory, cmd, beforeFs, preCwd, afterFs,
                  hadError, out, err, observations,
                  firstStatus + 1, afterStatus, calls[1..])} ::
                StateModel.ValueObservedBatchRelation(
                  sources, directory, cmd, beforeFs, preCwd, afterFs,
                  hadError, out, err, observations,
                  firstStatus + 1, afterStatus, calls[1..]) &&
                exit == (if hadError then 1 else 0) &&
                afterStdout == beforeStdout + out &&
                afterStderr == beforeStderr + err
            else |calls| == 1
  {
    reveal Core.DirectoryStatusEvidenceFor();
    match evidence {
      case FailedDirectoryStatus(_) =>
      case SuccessfulDirectoryStatus(dirCall, batch) =>
        var hadError, out, err :|
          Core.BatchEvidenceFor(
            sources, directory, cmd, beforeFs, preCwd, afterFs,
            hadError, out, err, batch) &&
          exit == (if hadError then 1 else 0) &&
          afterStdout == beforeStdout + out &&
          afterStderr == beforeStderr + err;
        BatchStatusEvidenceImpliesObservedBatch(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err, observations, batch);
        assert calls == [dirCall] + batch.statusCalls;
        assert calls[1..] == batch.statusCalls;
        assert batch.firstStatus == firstStatus + 1;
        assert afterStatus ==
               batch.firstStatus + |batch.statusCalls|;
        ObservedBatchIntervalSubstitution(
          sources, directory, cmd, beforeFs, preCwd, afterFs,
          hadError, out, err, observations, batch,
          firstStatus, afterStatus, calls);
    }
  }

  lemma {:isolate_assertions} RunStatusEvidenceImpliesObservedStatusSpec(
    raw: Schema.MvCmdRaw,
    beforeFs: BW.FileSystem,
    preCwd: BW.Path,
    afterFs: BW.FileSystem,
    beforeStdout: BW.Bytes,
    afterStdout: BW.Bytes,
    beforeStderr: BW.Bytes,
    afterStderr: BW.Bytes,
    exit: int,
    observations: Spec.NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<Spec.StatusCallEvidence>,
    evidence: Core.RunStatusEvidence
  )
    requires Core.RunStatusEvidenceFor(
               raw, beforeFs, preCwd, afterFs,
               beforeStdout, afterStdout, beforeStderr, afterStderr,
               exit, observations, firstStatus, afterStatus, calls, evidence)
    ensures StateModel.ValueObservedStatusSpec(
              raw, beforeFs, preCwd, afterFs,
              beforeStdout, afterStdout, beforeStderr, afterStderr,
              exit, observations, firstStatus, afterStatus, calls)
  {
    hide *;
    reveal Core.StatusCallsFor();
    reveal StateModel.ValueObservedStatusSpec();
    var cmd := Schema.Command(raw);
    reveal Core.RunStatusEvidenceFor();
    if cmd.mode != Schema.ModeRun ||
       (cmd.targetDirectory != "" && cmd.noTargetDirectory) ||
       |cmd.operands| == 0 ||
       (cmd.targetDirectory == "" && |cmd.operands| == 1) ||
       (cmd.targetDirectory == "" && cmd.noTargetDirectory &&
        |cmd.operands| > 2) {
      return;
    }
    if cmd.targetDirectory != "" {
      match evidence {
        case DirectoryRunStatus(directoryEvidence) =>
          DirectoryStatusEvidenceImpliesObservedDirectory(
            cmd.operands, cmd.targetDirectory, cmd,
            beforeFs, preCwd, afterFs,
            beforeStdout, afterStdout, beforeStderr, afterStderr,
            exit, observations, firstStatus, afterStatus, calls,
            directoryEvidence);
        case _ =>
      }
    } else if |cmd.operands| == 2 {
      var source := Spec.NormalizeSourceSpec(
        cmd.operands[0], cmd.stripTrailingSlashes
      );
      match evidence {
        case DirectMoveStatus(step) =>
          StepStatusEvidenceImpliesObservedStep(
            source, cmd.operands[1], cmd, preCwd, step, observations
          );
        case ProbedMoveStatus(call, step) =>
          var target :=
            if call.ok && call.status.kind == BW.DirectoryKind then
              Spec.TargetInDirectorySpec(cmd.operands[1], source)
            else cmd.operands[1];
          if call.ok && call.status.kind == BW.DirectoryKind {
          }
          assert !cmd.noTargetDirectory;
          assert step.firstStatus == firstStatus + 1;
          assert |calls| == 1 + |step.statusCalls|;
          assert calls[1..] == step.statusCalls;
          assert Core.StatusCallsFor(observations, step.firstStatus, step.statusCalls) by {
            hide *;
            reveal Core.RunStatusEvidenceFor(), Core.StepEvidenceFor();
          }
          StepStatusEvidenceImpliesObservedStep(
            source, target, cmd, preCwd, step, observations
          );
        case _ =>
      }
    } else {
      match evidence {
        case DirectoryRunStatus(directoryEvidence) =>
          DirectoryStatusEvidenceImpliesObservedDirectory(
            cmd.operands[..|cmd.operands| - 1],
            cmd.operands[|cmd.operands| - 1], cmd,
            beforeFs, preCwd, afterFs,
            beforeStdout, afterStdout, beforeStderr, afterStderr,
            exit, observations, firstStatus, afterStatus, calls,
            directoryEvidence);
        case _ =>
      }
    }
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.MvCmdRaw, io: BenchIO.IO, exit: int,
    calls: seq<Spec.StatusCallEvidence>, evidence: Core.RunStatusEvidence,
    plan: Core.PlannedOutput
  )
    requires Core.CoreSummary(raw, io, exit, plan)
    requires Core.RunStatusSummary(io, raw, plan.stdout, plan.stderr, plan.normalExit, calls, evidence)
    ensures Spec.Spec(raw, io, exit)
  {
    assert Core.RunStatusEvidenceFor(raw, old(io.fs()), old(io.cwd()), io.fs(),
                                     [], plan.stdout, [], plan.stderr, plan.normalExit,
                                     Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                                     old(io.statusCursor()), io.statusCursor(), calls, evidence) by {
      reveal Core.RunStatusSummary(), Core.RunStatusEvidenceFor();
    }

    reveal Core.PreparedSummary();
    hide Core.PreparedSummaryIO;
    hide Core.RunStatusEvidenceFor;
    hide StateModel.ValueCandidateSpecFields;
    hide StateModel.ValueObservedStatusSpec;
    assert Core.PreparedSummaryIO(raw, old(io.fs()), old(io.cwd()), [], [], io,
                                  plan.normalExit, plan.stdout, plan.stderr) by {
      reveal Core.CandidateSummary(), Core.PreparedSummaryIO();
    }
    PreparedSummaryIOImpliesCandidateSpecFields(raw, old(io.fs()), old(io.cwd()),
                                                [], [], io, plan.normalExit, plan.stdout, plan.stderr);
    RunStatusEvidenceImpliesObservedStatusSpec(raw, old(io.fs()), old(io.cwd()), io.fs(),
                                               [], plan.stdout, [], plan.stderr, plan.normalExit, Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()),
                                               old(io.statusCursor()), io.statusCursor(), calls, evidence);
    CandidateSpecFieldsImpliesSpec(io, raw, plan.stdout, plan.stderr, plan.normalExit);
    ObservedStatusFieldsImpliesSpec(io, raw, plan.stdout, plan.stderr, plan.normalExit,
                                   Spec.NativeStatusInputs(io.statusObservations(), io.trustedNativeFailures(), io.now()), calls);
    reveal Spec.Spec();
  }
}


// Snapshot judgments for composing intermediate implementation evidence.
module MvTransitionModel {
  import opened Spec = MvSpec
  import Errno = Errnos
  import Result = Results
  import BenchIO
  import IOContract
  import BenchWorld
  import Basename = MvPathSpec
  import Quote = StringEscaping
  import Dirname = MvPathSpec
  import Schema = MvSchema
  import Utf8 = Utf8Semantics
  import SE = StringEscaping

  ghost predicate ValueObservedUpdateDecision(
    cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    source: string,
    target: string,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome,
    calls: seq<StatusCallEvidence>
  )
  {
    if cmd.updateMode == Schema.UpdateOlder &&
       cmd.overwriteMode != Schema.OverwriteSkip &&
       |calls| >= 2 && calls[0].ok && calls[1].ok &&
       !(|calls| >= 4 && (!calls[2].ok || !calls[3].ok) &&
         (exists leaf: string :: Basename.BasenameRelation(source, leaf) &&
                                 Basename.BasenameRelation(target, leaf))) &&
       !SameFileMustBeRejected(cmd, fs, cwd, source, target) then
      |calls| >= 2 &&
      StatusRequest(calls[0], fs, source, false) &&
      StatusRequest(calls[1], fs, target, false) &&
      calls[0].ok && calls[1].ok &&
      (if !SourceNewerSpec(
            calls[0].status.times.mtimeSec,
            calls[0].status.times.mtimeNsec,
            calls[1].status.times.mtimeSec,
            calls[1].status.times.mtimeNsec
          ) then
         afterFs == fs &&
         outcome == MoveOutcome(SkipStdoutSpec(target, cmd.debug), [], false)
       else
         ValueExistingTargetRenameEffectRelation(
           source, target, cmd, fs, cwd, afterFs, outcome
         ))
    else
      true
  }

  ghost predicate ValueRenameEffectRelation(
    source: string,
    target: string,
    backupPath: string,
    verbose: bool,
    debug: bool,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    Spec.RenameAllowed(MoveEdge(beforeFs, MoveStep(afterFs, outcome)), source, target, backupPath, verbose, debug)
  }

  ghost predicate ValueObservedRenameEffectRelation(
    source: string, target: string, backupPath: string, cmd: Schema.MvCmd,
    sourceIsDir: bool, targetWasFound: bool, inputs: NativeStatusInputs,
    beforeFs: BenchWorld.FileSystem, afterFs: BenchWorld.FileSystem, outcome: MoveOutcome
  )
  {
    Spec.ObservedRenameAllowed(MoveEdge(beforeFs, MoveStep(afterFs, outcome)), source, target, backupPath, cmd, sourceIsDir, targetWasFound, inputs)
  }

  ghost predicate ValueExistingTargetRenameEffectRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    Spec.ExistingTargetRenameAllowed(MoveEdge(beforeFs, MoveStep(afterFs, outcome)), source, target, cmd)
  }

  ghost predicate ValueParentMetadataFailureEffect(
    source: string, target: string, cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem, afterFs: BenchWorld.FileSystem, outcome: MoveOutcome
  )
  {
    Spec.ParentMetadataFailure(MoveEdge(fs, MoveStep(afterFs, outcome)), source, target, cmd)
  }

  ghost predicate ValueOriginalMoveEffectRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome
  )
  {
    Spec.OriginalMoveAllowed(MoveEdge(beforeFs, MoveStep(afterFs, outcome)), source, target, cmd, preCwd)
  }

  ghost predicate ValueMoveEffectRelation(
    source: string, target: string, cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem, outcome: MoveOutcome
  )
  {
    Spec.MoveAllowed(MoveEdge(beforeFs, MoveStep(afterFs, outcome)), source, target, cmd, cwd)
  }

  ghost predicate ValueBatchMoveWitnessRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    fsBounds: seq<BenchWorld.FileSystem>,
    outcomes: seq<MoveOutcome>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>
  )
  {
    |fsBounds| == |sources| + 1 &&
    |outcomes| == |sources| &&
    |stdoutFragments| == |sources| &&
    |stderrFragments| == |sources| &&
    fsBounds[0] == beforeFs &&
    fsBounds[|fsBounds| - 1] == afterFs &&
    (forall i: nat {:trigger fsBounds[i]} {:split false} | i < |sources| ::
       var normalizedSource :=
         NormalizeSourceSpec(sources[i], cmd.stripTrailingSlashes);
       ValueMoveEffectRelation(
         normalizedSource,
         TargetInDirectorySpec(directory, normalizedSource),
         cmd,
         fsBounds[i],
         preCwd,
         fsBounds[i + 1],
         outcomes[i]
       ) &&
       stdoutFragments[i] == outcomes[i].stdoutFragment &&
       stderrFragments[i] == outcomes[i].stderrFragment) &&
    ConcatenateFragments(stdoutFragments) == out &&
    ConcatenateFragments(stderrFragments) == err &&
    (hadError <==>
     exists i: nat :: i < |outcomes| && outcomes[i].failed)
  }

  ghost predicate ValueBatchMoveRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes
  )
  {
    Spec.BatchMovesAllowed(sources, directory, cmd, beforeFs, preCwd, afterFs,
                           MoveOutcome(out, err, hadError))
  }

  ghost predicate ValueCandidateRunIntoDirectoryFields(
    sources: seq<string>,
    directory: string,
    explicitTargetDirectory: bool,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
  {
    (exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes ::
       TargetDirectoryCheckSpecFields(directory, beforeFs, true, 0) &&
       ValueBatchMoveRelation(
         sources, directory, cmd,
         beforeFs, preCwd, afterFs, hadError, out, err
       ) &&
       exit == (if hadError then 1 else 0) &&
       stdout2 == preStdout + out &&
       stderr2 == preStderr + err) ||
    (exists directoryErr: int ::
       TargetDirectoryCheckSpecFields(
         directory, beforeFs, false, directoryErr
       ) &&
       afterFs == beforeFs &&
       exit == 1 &&
       stdout2 == preStdout &&
       stderr2 == preStderr +
       TargetFailureMessageSpec(
         directory, explicitTargetDirectory, directoryErr
       ))
  }

  ghost predicate ValueCandidateRunTwoOperandFields(
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
    requires |cmd.operands| == 2
  {
    var source :=
      NormalizeSourceSpec(cmd.operands[0], cmd.stripTrailingSlashes);
    var destination := cmd.operands[1];
    if cmd.noTargetDirectory then
      exists outcome: MoveOutcome ::
        ValueMoveEffectRelation(
          source, destination, cmd,
          beforeFs, preCwd, afterFs, outcome
        ) &&
        exit == (if outcome.failed then 1 else 0) &&
        stdout2 == preStdout + outcome.stdoutFragment &&
        stderr2 == preStderr + outcome.stderrFragment
    else
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, true, true, directoryErr
         ) &&
         ValueMoveEffectRelation(
           source, TargetInDirectorySpec(destination, source), cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, true, false, directoryErr
         ) &&
         ValueMoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, false, directoryErr
         ) &&
         ValueMoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment) ||
      (exists directoryErr: int, outcome: MoveOutcome ::
         IOContract.IsDirectoryContractFields(
           beforeFs, destination, true, false, true, directoryErr
         ) &&
         ValueMoveEffectRelation(
           source, destination, cmd,
           beforeFs, preCwd, afterFs, outcome
         ) &&
         exit == (if outcome.failed then 1 else 0) &&
         stdout2 == preStdout + outcome.stdoutFragment &&
         stderr2 == preStderr + outcome.stderrFragment)
  }

  ghost predicate ValueCandidateSpecFields(
    raw: Schema.MvCmdRaw,
    preFs: BenchWorld.FileSystem,
    preCwd: BenchWorld.Path,
    preStdout: BenchWorld.Bytes,
    preStderr: BenchWorld.Bytes,
    afterFs: BenchWorld.FileSystem,
    plannedStdout: BenchWorld.Bytes,
    plannedStderr: BenchWorld.Bytes,
    exit: int
  )
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidBackup then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr ==
      preStderr + InvalidBackupArgumentMessageSpec(cmd.invalidBackupArg)
    else if cmd.mode == Schema.ModeInvalidUpdate then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr ==
      preStderr + InvalidUpdateArgumentMessageSpec(cmd.invalidUpdateArg)
    else if cmd.mode == Schema.ModeHelp then
      afterFs == preFs &&
      exit == 0 &&
      plannedStdout == preStdout + HelpTextSpec() &&
      plannedStderr == preStderr
    else if cmd.mode == Schema.ModeVersion then
      afterFs == preFs &&
      exit == 0 &&
      plannedStdout == preStdout + VersionTextSpec() &&
      plannedStderr == preStderr
    else if cmd.targetDirectory != "" && cmd.noTargetDirectory then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + TargetDirectoryConflictMessageSpec()
    else if |cmd.operands| == 0 then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + MissingFileOperandMessageSpec()
    else if cmd.targetDirectory != "" then
      ValueCandidateRunIntoDirectoryFields(
        cmd.operands, cmd.targetDirectory, true, cmd,
        preFs, preCwd, afterFs,
        preStdout, preStderr, plannedStdout, plannedStderr, exit
      )
    else if |cmd.operands| == 1 then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr ==
      preStderr + MissingDestinationMessageSpec(cmd.operands[0])
    else if cmd.noTargetDirectory && |cmd.operands| > 2 then
      afterFs == preFs &&
      exit == 1 &&
      plannedStdout == preStdout &&
      plannedStderr == preStderr + ExtraOperandMessageSpec(cmd.operands[2])
    else if |cmd.operands| == 2 then
      ValueCandidateRunTwoOperandFields(
        cmd, preFs, preCwd, afterFs,
        preStdout, preStderr, plannedStdout, plannedStderr, exit
      )
    else
      ValueCandidateRunIntoDirectoryFields(
        cmd.operands[..|cmd.operands| - 1],
        cmd.operands[|cmd.operands| - 1],
        false,
        cmd,
        preFs,
        preCwd,
        afterFs,
        preStdout,
        preStderr,
        plannedStdout,
        plannedStderr,
        exit
      )
  }

  ghost predicate ValueObservedParentFailureOutcome(
    source: string, target: string, cmd: Schema.MvCmd, fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem, outcome: MoveOutcome,
    calls: seq<StatusCallEvidence>
  )
  {
    if |calls| >= 4 && calls[0].ok && calls[1].ok &&
       (!calls[2].ok || !calls[3].ok) &&
       (exists leaf: string :: Basename.BasenameRelation(source, leaf) &&
                               Basename.BasenameRelation(target, leaf)) then
      |calls| == 4 && afterFs == fs &&
      (exists sourceParent: string, targetParent: string ::
         Dirname.DirnameRelation(source, sourceParent) &&
         Dirname.DirnameRelation(target, targetParent) &&
         StatusRequest(calls[2], fs, sourceParent, false) &&
         StatusRequest(calls[3], fs, targetParent, false) &&
         outcome == MoveOutcome([], ParentStatFailureMessageSpec(
                                  if !calls[2].ok then sourceParent else targetParent,
                                  if !calls[2].ok then calls[2].err else calls[3].err), true))
    else ValueOriginalMoveEffectRelation(source, target, cmd, fs, cwd, afterFs, outcome)
  }

  ghost predicate ValueObservedClassificationOutcome(
    source: string, target: string, cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem, outcome: MoveOutcome,
    calls: seq<StatusCallEvidence>, inputs: NativeStatusInputs,
    names: (string, string, string, string),
    resolveOk: bool, resolvedSource: string, resolveErr: int, afterEntries: nat
  )
  {
    Spec.ObservedClassificationAllowed(MoveEdge(fs, MoveStep(afterFs, outcome)), source, target, cmd, cwd, calls, inputs, EntryName(names.0, names.2), EntryName(names.1, names.3), resolveOk, resolvedSource, resolveErr, afterEntries)
  }

  ghost predicate ValueObservedMoveOutcome(
    source: string, target: string, cmd: Schema.MvCmd,
    fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem, outcome: MoveOutcome,
    calls: seq<StatusCallEvidence>, inputs: NativeStatusInputs
  )
  {
    Spec.ObservedMoveAllowed(MoveEdge(fs, MoveStep(afterFs, outcome)), source, target, cmd, cwd, calls, inputs)
  }

  ghost predicate ValueObservedStepRelation(
    source: string,
    target: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    outcome: MoveOutcome,
    observations: NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<StatusCallEvidence>
  )
  {
    Spec.ObservedStepAllowed(MoveEdge(beforeFs, MoveStep(afterFs, outcome)), source, target, cmd, cwd, observations, firstStatus, afterStatus, calls)
  }

  ghost predicate ValueObservedBatchRelation(
    sources: seq<string>,
    directory: string,
    cmd: Schema.MvCmd,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    err: BenchWorld.Bytes,
    observations: NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<StatusCallEvidence>
  )
  {
    afterStatus == firstStatus + |calls| &&
    StatusCallsFor(observations, firstStatus, calls) &&
    Spec.ObservedBatchMovesAllowed(sources, directory, cmd, beforeFs, cwd, afterFs,
                                   MoveOutcome(out, err, hadError), observations, firstStatus, calls)
  }

  ghost predicate ValueObservedStatusSpec(
    raw: Schema.MvCmdRaw,
    beforeFs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    afterFs: BenchWorld.FileSystem,
    beforeStdout: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes,
    beforeStderr: BenchWorld.Bytes,
    afterStderr: BenchWorld.Bytes,
    exit: int,
    observations: NativeStatusInputs,
    firstStatus: nat,
    afterStatus: nat,
    calls: seq<StatusCallEvidence>
  )
  {
    var cmd := Schema.Command(raw);
    afterStatus == firstStatus + |calls| &&
    StatusCallsFor(observations, firstStatus, calls) &&
    (if cmd.mode != Schema.ModeRun ||
        (cmd.targetDirectory != "" && cmd.noTargetDirectory) ||
        |cmd.operands| == 0 ||
        (cmd.targetDirectory == "" && |cmd.operands| == 1) ||
        (cmd.targetDirectory == "" && cmd.noTargetDirectory &&
         |cmd.operands| > 2) then
       |calls| == 0
     else if cmd.targetDirectory != "" then
       |calls| >= 1 &&
       StatusRequest(calls[0], beforeFs, cmd.targetDirectory, true) &&
       (if calls[0].ok &&
           calls[0].status.kind == BenchWorld.DirectoryKind then
          exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes
            {:trigger ValueObservedBatchRelation(
              cmd.operands, cmd.targetDirectory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..])} ::
            ValueObservedBatchRelation(
              cmd.operands, cmd.targetDirectory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..]
            ) &&
            exit == (if hadError then 1 else 0) &&
            afterStdout == beforeStdout + out &&
            afterStderr == beforeStderr + err
        else
          |calls| == 1)
     else if |cmd.operands| == 2 then
       var source := NormalizeSourceSpec(
                       cmd.operands[0], cmd.stripTrailingSlashes
                     );
       var destination := cmd.operands[1];
       (if cmd.noTargetDirectory then
          exists outcome: MoveOutcome ::
            ValueObservedStepRelation(
              source, destination, cmd, beforeFs, cwd, afterFs, outcome,
              observations, firstStatus, afterStatus, calls
            ) &&
            exit == (if outcome.failed then 1 else 0) &&
            afterStdout == beforeStdout + outcome.stdoutFragment &&
            afterStderr == beforeStderr + outcome.stderrFragment
        else
          |calls| >= 1 &&
          StatusRequest(calls[0], beforeFs, destination, true) &&
          var target :=
            if calls[0].ok &&
               calls[0].status.kind == BenchWorld.DirectoryKind then
              TargetInDirectorySpec(destination, source)
            else destination;
          exists outcome: MoveOutcome ::
            ValueObservedStepRelation(
              source, target, cmd, beforeFs, cwd, afterFs, outcome,
              observations, firstStatus + 1, afterStatus, calls[1..]
            ) &&
            exit == (if outcome.failed then 1 else 0) &&
            afterStdout == beforeStdout + outcome.stdoutFragment &&
            afterStderr == beforeStderr + outcome.stderrFragment)
     else
       var directory := cmd.operands[|cmd.operands| - 1];
       var sources := cmd.operands[..|cmd.operands| - 1];
       |calls| >= 1 &&
       StatusRequest(calls[0], beforeFs, directory, true) &&
       (if calls[0].ok &&
           calls[0].status.kind == BenchWorld.DirectoryKind then
          exists hadError: bool, out: BenchWorld.Bytes, err: BenchWorld.Bytes
            {:trigger ValueObservedBatchRelation(
              sources, directory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..])} ::
            ValueObservedBatchRelation(
              sources, directory, cmd,
              beforeFs, cwd, afterFs, hadError, out, err,
              observations, firstStatus + 1, afterStatus, calls[1..]
            ) &&
            exit == (if hadError then 1 else 0) &&
            afterStdout == beforeStdout + out &&
            afterStderr == beforeStderr + err
        else
          |calls| == 1))
  }
}
