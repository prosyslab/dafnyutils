include "../../core/World.dfy"
include "../../core/IO.dfy"
include "StatSchema.dfy"
include "StatSpec.dfy"
include "StatCore.dfy"

module StatProof {
  import BenchWorld
  import BenchIO
  import IOContract
  import Schema = StatSchema
  import Spec = StatSpec
  import Core = StatCore

  lemma FileStepSummaryImpliesFragment(
    cmd: Schema.StatCmd,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
    requires Core.FileStepSummaryFields(cmd, path, fs, hadError, out, errOut)
    ensures Spec.StatusObservationRelation(
              fs, path, cmd.followSymlink,
              IOContract.GetFileStatusResultFields(fs, path, cmd.followSymlink)
            )
    ensures Spec.FileFragmentRelation(
              cmd.format,
              path,
              IOContract.GetFileStatusResultFields(fs, path, cmd.followSymlink),
              out,
              errOut
            )
    ensures hadError == IOContract.GetFileStatusResultFields(
                          fs, path, cmd.followSymlink
                        ).Err?
  {
    match IOContract.GetFileStatusResultFields(fs, path, cmd.followSymlink)
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
              fragments + [fragment], output + fragment, cuts + [|output + fragment|]
            )
  {
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
          assert cuts[i] <= cuts[i + 1] <= |output| &&
                 output[cuts[i]..cuts[i + 1]] == fragments[i];
          assert (output + fragment)[cuts[i]..cuts[i + 1]] ==
                 output[cuts[i]..cuts[i + 1]];
        } else {
          assert i == |fragments|;
          assert cuts[i] == |output|;
          assert (output + fragment)[|output|..|output + fragment|] == fragment;
        }
      }
    }
  }

  lemma ConcatPiecesSnoc(
    pieces: seq<BenchWorld.Bytes>,
    piece: BenchWorld.Bytes
  )
    ensures Spec.ConcatPiecesSpec(pieces + [piece]) ==
            Spec.ConcatPiecesSpec(pieces) + piece
    decreases |pieces|
  {
    if |pieces| > 0 {
      ConcatPiecesSnoc(pieces[1..], piece);
      assert pieces + [piece] == [pieces[0]] + (pieces[1..] + [piece]);
    }
  }

  lemma ErrorExistsSnoc(
    cmd: Schema.StatCmd,
    prefix: seq<BenchWorld.Path>,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    prefixError: bool,
    stepError: bool
  )
    requires prefixError == (exists i: nat ::
                               i < |prefix| &&
                               IOContract.GetFileStatusResultFields(fs, prefix[i], cmd.followSymlink).Err?)
    requires stepError == IOContract.GetFileStatusResultFields(
                            fs, path, cmd.followSymlink
                          ).Err?
    ensures (prefixError || stepError) == (exists i: nat ::
                                             i < |prefix + [path]| &&
                                             IOContract.GetFileStatusResultFields(
                                               fs, (prefix + [path])[i], cmd.followSymlink
                                             ).Err?)
  {
    if prefixError || stepError {
      if prefixError {
        var i: nat :|
          i < |prefix| &&
          IOContract.GetFileStatusResultFields(fs, prefix[i], cmd.followSymlink).Err?;
        assert (prefix + [path])[i] == prefix[i];
      } else {
        assert (prefix + [path])[|prefix|] == path;
      }
    }
    if (exists i: nat ::
          i < |prefix + [path]| &&
          IOContract.GetFileStatusResultFields(
            fs, (prefix + [path])[i], cmd.followSymlink
          ).Err?)
    {
      var i: nat :|
        i < |prefix + [path]| &&
        IOContract.GetFileStatusResultFields(
          fs, (prefix + [path])[i], cmd.followSymlink
        ).Err?;
      if i < |prefix| {
        assert exists j: nat ::
            j < |prefix| &&
            IOContract.GetFileStatusResultFields(fs, prefix[j], cmd.followSymlink).Err?;
      } else {
        assert i == |prefix|;
        assert (prefix + [path])[i] == path;
      }
    }
  }

  lemma FileFragmentsSnoc(
    cmd: Schema.StatCmd,
    prefix: seq<BenchWorld.Path>,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    stdoutFragments: seq<BenchWorld.Bytes>,
    stderrFragments: seq<BenchWorld.Bytes>,
    stepOut: BenchWorld.Bytes,
    stepErrOut: BenchWorld.Bytes
  )
    requires |stdoutFragments| == |prefix|
    requires |stderrFragments| == |prefix|
    requires forall i: nat | i < |prefix| ::
               Spec.FileFragmentRelation(
                 cmd.format,
                 prefix[i],
                 IOContract.GetFileStatusResultFields(fs, prefix[i], cmd.followSymlink),
                 stdoutFragments[i],
                 stderrFragments[i]
               )
    requires Spec.FileFragmentRelation(
               cmd.format,
               path,
               IOContract.GetFileStatusResultFields(fs, path, cmd.followSymlink),
               stepOut,
               stepErrOut
             )
    ensures forall i: nat | i < |prefix + [path]| ::
              Spec.FileFragmentRelation(
                cmd.format,
                (prefix + [path])[i],
                IOContract.GetFileStatusResultFields(
                  fs, (prefix + [path])[i], cmd.followSymlink
                ),
                (stdoutFragments + [stepOut])[i],
                (stderrFragments + [stepErrOut])[i]
              )
  {
    forall i: nat | i < |prefix + [path]|
      ensures Spec.FileFragmentRelation(
                cmd.format,
                (prefix + [path])[i],
                IOContract.GetFileStatusResultFields(
                  fs, (prefix + [path])[i], cmd.followSymlink
                ),
                (stdoutFragments + [stepOut])[i],
                (stderrFragments + [stepErrOut])[i]
              )
    {
      if i < |prefix| {
        assert (prefix + [path])[i] == prefix[i];
      } else {
        assert i == |prefix|;
        assert (prefix + [path])[i] == path;
      }
    }
  }

  lemma RunFilesRelationSnoc(
    cmd: Schema.StatCmd,
    prefix: seq<BenchWorld.Path>,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    prefixError: bool,
    prefixOut: BenchWorld.Bytes,
    prefixErrOut: BenchWorld.Bytes,
    stepError: bool,
    stepOut: BenchWorld.Bytes,
    stepErrOut: BenchWorld.Bytes
  )
    requires Spec.RunFilesRelation(cmd, prefix, fs, prefixError, prefixOut, prefixErrOut)
    requires Core.FileStepSummaryFields(cmd, path, fs, stepError, stepOut, stepErrOut)
    ensures Spec.RunFilesRelation(
              cmd,
              prefix + [path],
              fs,
              prefixError || stepError,
              prefixOut + stepOut,
              prefixErrOut + stepErrOut
            )
  {
    var stdoutFragments: seq<BenchWorld.Bytes>,
        stderrFragments: seq<BenchWorld.Bytes> :|
      |stdoutFragments| == |prefix| &&
      |stderrFragments| == |prefix| &&
      (forall i: nat | i < |prefix| ::
         Spec.FileFragmentRelation(
           cmd.format,
           prefix[i],
           IOContract.GetFileStatusResultFields(fs, prefix[i], cmd.followSymlink),
           stdoutFragments[i], stderrFragments[i]
         )) &&
      prefixError == (exists i: nat ::
                        i < |prefix| &&
                        IOContract.GetFileStatusResultFields(fs, prefix[i], cmd.followSymlink).Err?) &&
      prefixOut == Spec.ConcatPiecesSpec(stdoutFragments) &&
      prefixErrOut == Spec.ConcatPiecesSpec(stderrFragments);

    var observation := IOContract.GetFileStatusResultFields(fs, path, cmd.followSymlink);
    FileStepSummaryImpliesFragment(cmd, path, fs, stepError, stepOut, stepErrOut);
    ConcatPiecesSnoc(stdoutFragments, stepOut);
    ConcatPiecesSnoc(stderrFragments, stepErrOut);
    ErrorExistsSnoc(cmd, prefix, path, fs, prefixError, stepError);
    FileFragmentsSnoc(
      cmd,
      prefix,
      path,
      fs,
      stdoutFragments,
      stderrFragments,
      stepOut,
      stepErrOut
    );
  }

  lemma {:isolate_assertions} RunFilesSummaryImpliesRelation(
    cmd: Schema.StatCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
    requires Core.RunFilesSummaryFields(cmd, files, fs, hadError, out, errOut)
    ensures Spec.RunFilesRelation(cmd, files, fs, hadError, out, errOut)
    decreases |files|
  {
    if |files| == 0 {
      assert Spec.ConcatPiecesSpec([]) == [];
    } else {
      var prefixError: bool, prefixOut: BenchWorld.Bytes, prefixErrOut: BenchWorld.Bytes,
          stepError: bool, stepOut: BenchWorld.Bytes, stepErrOut: BenchWorld.Bytes :|
        Core.RunFilesSummaryFields(
          cmd, files[..|files| - 1], fs, prefixError, prefixOut, prefixErrOut
        ) &&
        Core.FileStepSummaryFields(
          cmd, files[|files| - 1], fs, stepError, stepOut, stepErrOut
        ) &&
        hadError == (prefixError || stepError) &&
        out == prefixOut + stepOut && errOut == prefixErrOut + stepErrOut;

      RunFilesSummaryImpliesRelation(
        cmd, files[..|files| - 1], fs, prefixError, prefixOut, prefixErrOut
      );
      var path := files[|files| - 1];
      RunFilesRelationSnoc(
        cmd,
        files[..|files| - 1],
        path,
        fs,
        prefixError,
        prefixOut,
        prefixErrOut,
        stepError,
        stepOut,
        stepErrOut
      );
      assert files[|files| - 1..] == [path];
      calc {
         files;
      == files[..|files| - 1] + files[|files| - 1..];
      == files[..|files| - 1] + [path];
      }
    }
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.StatCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeRun {
      var hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes :|
        Core.RunFilesSummaryFields(cmd, cmd.files, old(io.fs()), hadError, out, errOut) &&
        io.stdout() == old(io.stdout()) + out && io.stderr() == old(io.stderr()) + errOut &&
        exit == (if hadError then 1 else 0);
      RunFilesSummaryImpliesRelation(cmd, cmd.files, old(io.fs()), hadError, out, errOut);
    }
  }
}
