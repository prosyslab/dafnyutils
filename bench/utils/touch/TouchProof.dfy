include "../../core/World.dfy"
include "TouchSchema.dfy"
include "TouchCore.dfy"
include "TouchSpec.dfy"

module TouchProof {
  import Utf8 = Utf8Semantics
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = TouchSchema
  import Core = TouchCore
  import Spec = TouchSpec

  lemma ParseErrorMessageImpliesSpec(e: CliTypes.ParseError)
    ensures Utf8.Encode(Schema.ParseErrorText(e)) == Spec.ParseErrorMessageSpec(e)
  {
  }

  lemma ParseFailurePlanImpliesSpec(
    e: CliTypes.ParseError,
    plan: CliTypes.CliPlan<Schema.TouchCmdRaw>
  )
    requires plan == CliTypes.CliEarlyExit(1, [], Utf8.Encode(Schema.ParseErrorText(e)))
    ensures Spec.ParseFailureSpec(e, plan)
  {
    ParseErrorMessageImpliesSpec(e);
  }

  lemma RunStepSummaryFieldsImpliesSpec(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    path: BenchWorld.Path,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    hadError: bool,
    errOut: BenchWorld.Bytes
  )
    requires Core.RunStepSummaryFields(
               observations, path, noCreate, followSymlink, selection, source,
               preFs, preNow, preStdout, preStdoutTarget,
               fs2, stdout2, stdoutTarget2, hadError, errOut
             )
    ensures Spec.RunStepSpecFields(
              observations, path, noCreate, followSymlink, selection, source,
              preFs, preNow, preStdout, preStdoutTarget,
              fs2, stdout2, stdoutTarget2, hadError, errOut
            )
  {
    reveal Spec.RunStepSpecFields();
  }

  lemma EmptyRunFilesSummary(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    hadError: bool,
    errOut: BenchWorld.Bytes
  )
    requires Core.RunFilesSummaryFields(
               observations, [], noCreate, followSymlink, selection, source,
               preFs, preNow, preStdout, preStdoutTarget,
               fs2, stdout2, stdoutTarget2, hadError, errOut
             )
    ensures fs2 == preFs
    ensures stdout2 == preStdout
    ensures stdoutTarget2 == preStdoutTarget
    ensures !hadError
    ensures errOut == []
  {
    reveal Core.RunFilesSummaryFields();
  }

  lemma SplitRunFilesSummary(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    files: seq<BenchWorld.Path>,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    hadError: bool,
    errOut: BenchWorld.Bytes
  ) returns (
      prefixFs: BenchWorld.FileSystem,
      prefixStdout: BenchWorld.Bytes,
      prefixStdoutTarget: BenchWorld.StdoutTimestampState,
      prefixError: bool,
      stepError: bool,
      prefixOut: BenchWorld.Bytes,
      stepOut: BenchWorld.Bytes
    )
    requires 0 < |files|
    requires Core.RunFilesSummaryFields(
               observations, files, noCreate, followSymlink, selection, source,
               preFs, preNow, preStdout, preStdoutTarget,
               fs2, stdout2, stdoutTarget2, hadError, errOut
             )
    ensures Core.RunFilesSummaryFields(
              observations, files[..|files| - 1], noCreate,
              followSymlink, selection, source,
              preFs, preNow, preStdout, preStdoutTarget,
              prefixFs, prefixStdout, prefixStdoutTarget, prefixError, prefixOut
            )
    ensures Core.RunStepSummaryFields(
              observations, files[|files| - 1], noCreate,
              followSymlink, selection, source,
              prefixFs, preNow, prefixStdout, prefixStdoutTarget,
              fs2, stdout2, stdoutTarget2, stepError, stepOut
            )
    ensures hadError == (prefixError || stepError)
    ensures errOut == prefixOut + stepOut
  {
    reveal Core.RunFilesSummaryFields();
    prefixFs, prefixStdout, prefixStdoutTarget,
      prefixError, stepError, prefixOut, stepOut :|
      Core.RunFilesSummaryFields(
        observations, files[..|files| - 1], noCreate,
        followSymlink, selection, source,
        preFs, preNow, preStdout, preStdoutTarget,
        prefixFs, prefixStdout, prefixStdoutTarget, prefixError, prefixOut
      ) &&
      Core.RunStepSummaryFields(
        observations, files[|files| - 1], noCreate,
        followSymlink, selection, source,
        prefixFs, preNow, prefixStdout, prefixStdoutTarget,
        fs2, stdout2, stdoutTarget2, stepError, stepOut
      ) &&
      hadError == (prefixError || stepError) &&
      errOut == prefixOut + stepOut;
  }

  lemma CoreStepImpliesTransition(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    path: BenchWorld.Path,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preNow: int,
    before: Spec.FileState,
    after: Spec.FileState,
    stepError: bool,
    stepOut: BenchWorld.Bytes
  )
    requires Core.RunStepSummaryFields(
               observations, path, noCreate, followSymlink, selection, source,
               before.fs, preNow, before.stdout, before.stdoutTarget,
               after.fs, after.stdout, after.stdoutTarget, stepError, stepOut
             )
    requires after.hadError == (before.hadError || stepError)
    requires after.errOut == before.errOut + stepOut
    ensures Spec.FileTransitionRelation(
              observations, path, noCreate, followSymlink,
              selection, source, preNow, before, after
            )
  {
    RunStepSummaryFieldsImpliesSpec(
      observations, path, noCreate, followSymlink, selection, source,
      before.fs, preNow, before.stdout, before.stdoutTarget,
      after.fs, after.stdout, after.stdoutTarget, stepError, stepOut
    );
    reveal Spec.FileTransitionRelation();
  }

  lemma FileStatesWitnessImpliesSpec(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    files: seq<BenchWorld.Path>,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    hadError: bool,
    errOut: BenchWorld.Bytes,
    states: seq<Spec.FileState>
  )
    requires |states| == |files| + 1
    requires states[0] == Spec.FileState(preFs, preStdout, preStdoutTarget, false, [])
    requires states[|files|] == Spec.FileState(fs2, stdout2, stdoutTarget2, hadError, errOut)
    requires forall i {:trigger Spec.FileTransitionRelation(observations, files[i], noCreate, followSymlink, selection, source, preNow, states[i], states[i + 1])} ::
               0 <= i < |files| ==>
                 Spec.FileTransitionRelation(
                   observations, files[i], noCreate, followSymlink, selection, source,
                   preNow, states[i], states[i + 1]
                 )
    ensures Spec.RunFilesSpecFields(
              observations, files, noCreate, followSymlink, selection, source,
              preFs, preNow, preStdout, preStdoutTarget,
              fs2, stdout2, stdoutTarget2, hadError, errOut
            )
  {
    reveal Spec.RunFilesSpecFields();
  }

  lemma ExtendFileStates(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    files: seq<BenchWorld.Path>,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preNow: int,
    prefixStates: seq<Spec.FileState>,
    after: Spec.FileState
  ) returns (states: seq<Spec.FileState>)
    requires 0 < |files|
    requires |prefixStates| == |files|
    requires forall i {:trigger Spec.FileTransitionRelation(observations, files[i], noCreate, followSymlink, selection, source, preNow, prefixStates[i], prefixStates[i + 1])} ::
               0 <= i < |files| - 1 ==>
                 Spec.FileTransitionRelation(
                   observations, files[i], noCreate, followSymlink, selection, source,
                   preNow, prefixStates[i], prefixStates[i + 1]
                 )
    requires Spec.FileTransitionRelation(
               observations, files[|files| - 1], noCreate,
               followSymlink, selection, source,
               preNow, prefixStates[|files| - 1], after
             )
    ensures states == prefixStates + [after]
    ensures forall i {:trigger Spec.FileTransitionRelation(observations, files[i], noCreate, followSymlink, selection, source, preNow, states[i], states[i + 1])} ::
              0 <= i < |files| ==>
                Spec.FileTransitionRelation(
                  observations, files[i], noCreate, followSymlink, selection, source,
                  preNow, states[i], states[i + 1]
                )
  {
    states := prefixStates + [after];
    forall i {:trigger Spec.FileTransitionRelation(observations, files[i], noCreate, followSymlink, selection, source, preNow, states[i], states[i + 1])} |
      0 <= i < |files|
      ensures Spec.FileTransitionRelation(
                observations, files[i], noCreate, followSymlink, selection, source,
                preNow, states[i], states[i + 1]
              )
    {
      if i == |files| - 1 {
        assert states[i] == prefixStates[i];
        assert states[i + 1] == after;
      } else {
        assert states[i] == prefixStates[i];
        assert states[i + 1] == prefixStates[i + 1];
      }
    }
  }

  lemma {:vcs_split_on_every_assert} RunFilesSummaryFieldsImpliesSpec(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    files: seq<BenchWorld.Path>,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    hadError: bool,
    errOut: BenchWorld.Bytes
  ) returns (states: seq<Spec.FileState>)
    requires Core.RunFilesSummaryFields(
               observations, files, noCreate, followSymlink, selection, source,
               preFs, preNow, preStdout, preStdoutTarget,
               fs2, stdout2, stdoutTarget2, hadError, errOut
             )
    ensures |states| == |files| + 1
    ensures states[0] == Spec.FileState(preFs, preStdout, preStdoutTarget, false, [])
    ensures states[|files|] == Spec.FileState(fs2, stdout2, stdoutTarget2, hadError, errOut)
    ensures forall i {:trigger Spec.FileTransitionRelation(observations, files[i], noCreate, followSymlink, selection, source, preNow, states[i], states[i + 1])} ::
              0 <= i < |files| ==>
                Spec.FileTransitionRelation(
                  observations, files[i], noCreate, followSymlink, selection, source,
                  preNow, states[i], states[i + 1]
                )
    ensures Spec.RunFilesSpecFields(
              observations, files, noCreate, followSymlink, selection, source,
              preFs, preNow, preStdout, preStdoutTarget,
              fs2, stdout2, stdoutTarget2, hadError, errOut
            )
    decreases |files|
  {
    if |files| == 0 {
      EmptyRunFilesSummary(
        observations, noCreate, followSymlink, selection, source,
        preFs, preNow, preStdout, preStdoutTarget,
        fs2, stdout2, stdoutTarget2, hadError, errOut
      );
      states := [Spec.FileState(preFs, preStdout, preStdoutTarget, false, [])];
      FileStatesWitnessImpliesSpec(
        observations, files, noCreate, followSymlink, selection, source,
        preFs, preNow, preStdout, preStdoutTarget,
        fs2, stdout2, stdoutTarget2, hadError, errOut, states
      );
    } else {
      var prefixFs, prefixStdout, prefixStdoutTarget,
          prefixError, stepError, prefixOut, stepOut :=
        SplitRunFilesSummary(
          observations, files, noCreate, followSymlink, selection, source,
          preFs, preNow, preStdout, preStdoutTarget,
          fs2, stdout2, stdoutTarget2, hadError, errOut
        );
      var prefixStates := RunFilesSummaryFieldsImpliesSpec(
        observations, files[..|files| - 1], noCreate,
        followSymlink, selection, source,
        preFs, preNow, preStdout, preStdoutTarget,
        prefixFs, prefixStdout, prefixStdoutTarget, prefixError, prefixOut
      );
      var before := Spec.FileState(
        prefixFs, prefixStdout, prefixStdoutTarget, prefixError, prefixOut
      );
      var after := Spec.FileState(
        fs2, stdout2, stdoutTarget2, hadError, errOut
      );
      assert prefixStates[|files| - 1] == before;
      CoreStepImpliesTransition(
        observations, files[|files| - 1], noCreate,
        followSymlink, selection, source,
        preNow, before, after, stepError, stepOut
      );
      states := ExtendFileStates(
        observations, files, noCreate, followSymlink, selection, source,
        preNow, prefixStates, after
      );
      FileStatesWitnessImpliesSpec(
        observations, files, noCreate, followSymlink, selection, source,
        preFs, preNow, preStdout, preStdoutTarget,
        fs2, stdout2, stdoutTarget2, hadError, errOut, states
      );
    }
  }

  twostate lemma ResolvedRunSummaryFieldsImpliesSpec(
    cmd: Schema.TouchCmd,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.ResolvedRunSummaryFields(cmd, io, exit)
    ensures Spec.ResolvedRunSpecFields(cmd, io, exit)
  {
    var selection: Schema.TimeSelection, source: Schema.TimeSource :|
      Spec.RequestedSelection(cmd, selection) &&
      Spec.RequestedSourceFields(
        old(io.trustedFilesystem()), cmd, old(io.fs()), old(io.now()),
        old(io.trustedTimeParses()), source
      ) &&
      (if |cmd.files| == 0 then
         io.fs() == old(io.fs()) &&
         io.stdout() == old(io.stdout()) &&
         io.stderr() == old(io.stderr()) + Spec.MissingOperandMessageSpec() &&
         exit == 1
       else
         exists hadError: bool, errOut: BenchWorld.Bytes ::
           exit == (if hadError then 1 else 0) &&
           Core.RunFilesSummaryFields(
             old(io.trustedFilesystem()), cmd.files, cmd.noCreate,
             cmd.followSymlink, selection, source,
             old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
             io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
           ) &&
           io.stderr() == old(io.stderr()) + errOut);
    if |cmd.files| > 0 {
      var hadError: bool, errOut: BenchWorld.Bytes :|
        exit == (if hadError then 1 else 0) &&
        Core.RunFilesSummaryFields(
          old(io.trustedFilesystem()), cmd.files, cmd.noCreate,
          cmd.followSymlink, selection, source,
          old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
          io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
        ) &&
        io.stderr() == old(io.stderr()) + errOut;
      var states := RunFilesSummaryFieldsImpliesSpec(
        old(io.trustedFilesystem()), cmd.files, cmd.noCreate,
        cmd.followSymlink, selection, source,
        old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
        io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
      );
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.TouchCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    reveal Spec.Spec();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeRun &&
       !(cmd.timeArg != "" && Schema.ClassifyTimeWord(cmd.timeArg) == Schema.TimeWordAmbiguous) &&
       !(cmd.timeArg != "" && Schema.ClassifyTimeWord(cmd.timeArg) == Schema.TimeWordInvalid) {
      if Core.ResolvedRunSummaryFields(cmd, io, exit) {
        ResolvedRunSummaryFieldsImpliesSpec(cmd, io, exit);
      }
    }
  }
}
