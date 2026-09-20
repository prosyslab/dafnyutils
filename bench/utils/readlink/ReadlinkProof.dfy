include "../../core/World.dfy"
include "ReadlinkSchema.dfy"
include "ReadlinkCore.dfy"
include "ReadlinkSpec.dfy"

module ReadlinkProof {
  import BenchIO
  import BenchWorld
  import Schema = ReadlinkSchema
  import Core = ReadlinkCore
  import Spec = ReadlinkSpec

  lemma ReadOneSummaryImpliesFragment(
    cmd: Schema.ReadlinkCmd,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
    requires Core.ReadOneSummaryFields(cmd, path, fs, cwd, hadError, out, errOut)
    ensures Spec.ReadObservationRelation(
              fs,
              cwd,
              path,
              Core.ReadlinkResultFields(fs, cwd, path)
            )
    ensures Spec.ReadFragmentRelation(
              cmd,
              path,
              Core.ReadlinkResultFields(fs, cwd, path),
              out,
              errOut
            )
    ensures hadError == Core.ReadlinkResultFields(fs, cwd, path).Err?
  {
    match Core.ReadlinkResultFields(fs, cwd, path)
    case Ok(_) =>
    case Err(_) =>
  }

  lemma OutputFragmentCutsSnoc(
    fragments: seq<BenchWorld.Bytes>,
    output: BenchWorld.Bytes,
    cuts: seq<nat>,
    fragment: BenchWorld.Bytes
  )
    requires Spec.OutputFragmentCutsRelation(fragments, output, cuts)
    ensures Spec.OutputFragmentCutsRelation(
              fragments + [fragment],
              output + fragment,
              cuts + [|output + fragment|]
            )
  {
    assert |cuts| == |fragments| + 1;
    assert cuts[|fragments|] == |output|;
    assert forall i: nat {:trigger (cuts + [|output + fragment|])[i],
        (cuts + [|output + fragment|])[i + 1]}
        | i < |fragments + [fragment]| ::
        (cuts + [|output + fragment|])[i] <=
        (cuts + [|output + fragment|])[i + 1] <= |output + fragment| &&
        (output + fragment)[
        (cuts + [|output + fragment|])[i]..
        (cuts + [|output + fragment|])[i + 1]
        ] == (fragments + [fragment])[i] by {
      forall i: nat
        {:trigger (cuts + [|output + fragment|])[i],
        (cuts + [|output + fragment|])[i + 1]}
    | i < |fragments + [fragment]|
        ensures
          (cuts + [|output + fragment|])[i] <=
          (cuts + [|output + fragment|])[i + 1] <= |output + fragment| &&
          (output + fragment)[
          (cuts + [|output + fragment|])[i]..
          (cuts + [|output + fragment|])[i + 1]
          ] == (fragments + [fragment])[i]
      {
        if i < |fragments| {
          assert cuts[i + 1] <= |output|;
          assert output[cuts[i]..cuts[i + 1]] == fragments[i];
          assert (output + fragment)[cuts[i]..cuts[i + 1]] ==
                 output[cuts[i]..cuts[i + 1]];
        } else {
          assert i == |fragments|;
          assert (cuts + [|output + fragment|])[i] == |output|;
          assert (cuts + [|output + fragment|])[i + 1] == |output + fragment|;
          assert (output + fragment)[|output|..|output + fragment|] == fragment;
        }
      }
    }
  }

  lemma RunFilesWitnessImpliesRelation(
    cmd: Schema.ReadlinkCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    observations: seq<BenchWorld.Result<BenchWorld.Path>>,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>,
    stdoutCuts: seq<nat>,
    stderrCuts: seq<nat>,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
    requires Spec.RunFilesWitnessRelation(
      cmd, files, fs, cwd, observations, stdoutFragments, stderrFragments,
      stdoutCuts, stderrCuts, hadError, out, errOut
    )
    ensures Spec.RunFilesRelation(cmd, files, fs, cwd, hadError, out, errOut)
  {
  }

  lemma RunFilesSummaryImpliesRelation(
    cmd: Schema.ReadlinkCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
    requires Core.RunFilesSummaryFields(cmd, files, fs, cwd, hadError, out, errOut)
    ensures Spec.RunFilesRelation(cmd, files, fs, cwd, hadError, out, errOut)
    decreases |files|
  {
    var outputEnd: nat := |out|;
    var errorEnd: nat := |errOut|;
    if |files| == 0 {
      assert Spec.OutputFragmentCutsRelation([], [], [0]);
      assert Spec.RunFilesWitnessRelation(
          cmd, files, fs, cwd, [], [], [], [0], [0], hadError, out, errOut
        );
      RunFilesWitnessImpliesRelation(
        cmd, files, fs, cwd, [], [], [], [0], [0], hadError, out, errOut
      );
    } else {
      var prefixError: bool, prefixOut: BenchWorld.Bytes, prefixErrOut: BenchWorld.Bytes :|
        Core.RunFilesSummaryFields(
          cmd,
          files[..|files| - 1],
          fs,
          cwd,
          prefixError,
          prefixOut,
          prefixErrOut
        ) &&
        exists stepError: bool, stepOut: BenchWorld.Bytes, stepErrOut: BenchWorld.Bytes
          {:trigger Core.ReadOneSummaryFields(
            cmd,
            files[|files| - 1],
            fs,
            cwd,
            stepError,
            stepOut,
            stepErrOut
          )} ::
          Core.ReadOneSummaryFields(
            cmd,
            files[|files| - 1],
            fs,
            cwd,
            stepError,
            stepOut,
            stepErrOut
          ) &&
          hadError == (prefixError || stepError) &&
          out == prefixOut + stepOut &&
          errOut == prefixErrOut + stepErrOut;
      var stepError: bool, stepOut: BenchWorld.Bytes, stepErrOut: BenchWorld.Bytes :|
        Core.ReadOneSummaryFields(
          cmd,
          files[|files| - 1],
          fs,
          cwd,
          stepError,
          stepOut,
          stepErrOut
        ) &&
        hadError == (prefixError || stepError) &&
        out == prefixOut + stepOut &&
        errOut == prefixErrOut + stepErrOut;
      RunFilesSummaryImpliesRelation(
        cmd,
        files[..|files| - 1],
        fs,
        cwd,
        prefixError,
        prefixOut,
        prefixErrOut
      );
      var observations: seq<BenchWorld.Result<BenchWorld.Path>>,
          stdoutFragments: seq<BenchWorld.Bytes>,
          stderrFragments: seq<BenchWorld.Bytes>,
          stdoutCuts: seq<nat>,
          stderrCuts: seq<nat> :|
        Spec.RunFilesWitnessRelation(
          cmd,
          files[..|files| - 1],
          fs,
          cwd,
          observations,
          stdoutFragments,
          stderrFragments,
          stdoutCuts,
          stderrCuts,
          prefixError,
          prefixOut,
          prefixErrOut
        );
      var path := files[|files| - 1];
      var observation := Core.ReadlinkResultFields(fs, cwd, path);
      ReadOneSummaryImpliesFragment(
        cmd, path, fs, cwd, stepError, stepOut, stepErrOut
      );
      assert prefixError ==
             (exists i: nat :: i < |observations| && observations[i].Err?);
      assert stepError == observation.Err?;
      OutputFragmentCutsSnoc(stdoutFragments, prefixOut, stdoutCuts, stepOut);
      OutputFragmentCutsSnoc(stderrFragments, prefixErrOut, stderrCuts, stepErrOut);
      assert files == files[..|files| - 1] + [path];
      assert forall i: nat | i < |files| ::
        Spec.ReadObservationRelation(fs, cwd, files[i], (observations + [observation])[i]) &&
        Spec.ReadFragmentRelation(cmd, files[i], (observations + [observation])[i],
          (stdoutFragments + [stepOut])[i], (stderrFragments + [stepErrOut])[i]) by {
        forall i: nat | i < |files|
          ensures Spec.ReadObservationRelation(fs, cwd, files[i], (observations + [observation])[i]) &&
            Spec.ReadFragmentRelation(cmd, files[i], (observations + [observation])[i],
              (stdoutFragments + [stepOut])[i], (stderrFragments + [stepErrOut])[i])
        {
          if i < |files| - 1 {
            assert files[i] == files[..|files| - 1][i];
            assert Spec.ReadObservationRelation(fs, cwd, files[i], observations[i]);
            assert Spec.ReadFragmentRelation(cmd, files[i], observations[i],
              stdoutFragments[i], stderrFragments[i]);
          } else {
            assert i == |files| - 1;
          }
        }
      }
      assert hadError ==
             (exists i: nat ::
                i < |observations + [observation]| &&
                (observations + [observation])[i].Err?) by {
        if hadError {
          if prefixError {
            var i: nat :| i < |observations| && observations[i].Err?;
            assert (observations + [observation])[i] == observations[i];
            assert exists j: nat ::
                j < |observations + [observation]| &&
                (observations + [observation])[j].Err?;
          } else {
            assert stepError;
            assert observation.Err?;
            assert (observations + [observation])[|observations|] == observation;
            assert exists j: nat ::
                j < |observations + [observation]| &&
                (observations + [observation])[j].Err?;
          }
        }
        if exists i: nat ::
            i < |observations + [observation]| &&
            (observations + [observation])[i].Err?
        {
          var i: nat :|
            i < |observations + [observation]| &&
            (observations + [observation])[i].Err?;
          if i < |observations| {
            assert (observations + [observation])[i] == observations[i];
            assert exists j: nat :: j < |observations| && observations[j].Err?;
            assert prefixError;
          } else {
            assert i == |observations|;
            assert (observations + [observation])[i] == observation;
            assert stepError;
          }
          assert hadError == (prefixError || stepError);
          assert hadError;
        }
      }
      assert Spec.RunFilesWitnessRelation(
          cmd,
          files,
          fs,
          cwd,
          observations + [observation],
          stdoutFragments + [stepOut],
          stderrFragments + [stepErrOut],
          stdoutCuts + [outputEnd],
          stderrCuts + [errorEnd],
          hadError,
          out,
          errOut
        );
      RunFilesWitnessImpliesRelation(
        cmd, files, fs, cwd, observations + [observation],
        stdoutFragments + [stepOut], stderrFragments + [stepErrOut],
        stdoutCuts + [outputEnd], stderrCuts + [errorEnd], hadError, out, errOut
      );
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.ReadlinkCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeRun && |cmd.operands| > 0 {
      var hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes :|
        Core.RunFilesSummaryFields(
          cmd,
          cmd.operands,
          old(io.fs()),
          old(io.cwd()),
          hadError,
          out,
          errOut
        ) &&
        io.stdout() == old(io.stdout()) + out &&
        io.stderr() == old(io.stderr()) + Spec.InitialWarningSpec(cmd) + errOut &&
        exit == (if hadError then 1 else 0);
      RunFilesSummaryImpliesRelation(
        cmd,
        cmd.operands,
        old(io.fs()),
        old(io.cwd()),
        hadError,
        out,
        errOut
      );
    }
  }
}
