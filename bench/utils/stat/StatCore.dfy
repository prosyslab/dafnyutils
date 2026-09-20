include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "StatSchema.dfy"
include "StatSpec.dfy"

module StatCore {
  import BenchWorld
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import Schema = StatSchema
  import Spec = StatSpec

  ghost predicate PrefixRenderingRelation(
    format: string,
    status: BenchWorld.FileStatus,
    end: nat,
    rendered: BenchWorld.Bytes,
    cuts: seq<nat>,
    pieces: seq<BenchWorld.Bytes>
  )
  {
    Spec.PrefixRenderingWitnessRelation(format, status, end, rendered, cuts, pieces)
  }

  lemma ConcatPiecesSnoc(pieces: seq<BenchWorld.Bytes>, piece: BenchWorld.Bytes)
    ensures Spec.ConcatPiecesSpec(pieces + [piece]) == Spec.ConcatPiecesSpec(pieces) + piece
    decreases |pieces|
  {
    if |pieces| > 0 {
      ConcatPiecesSnoc(pieces[1..], piece);
      assert pieces + [piece] == [pieces[0]] + (pieces[1..] + [piece]);
    }
  }

  method RenderFormat(
    format: string,
    status: BenchWorld.FileStatus
  ) returns (
      rendered: BenchWorld.Bytes,
      cuts: seq<nat>,
      pieces: seq<BenchWorld.Bytes>
    )
    ensures Spec.FormatRenderingRelation(format, status, rendered)
    ensures Spec.RenderingWitnessRelation(format, status, rendered, cuts, pieces)
  {
    var index: nat := 0;
    rendered := [];
    cuts := [0];
    pieces := [];

    while index < |format|
      invariant index <= |format|
      invariant PrefixRenderingRelation(format, status, index, rendered, cuts, pieces)
      decreases |format| - index
    {
      var nextIndex: nat;
      var piece: BenchWorld.Bytes;
      if format[index] != '%' {
        nextIndex := index + 1;
        piece := Utf8.EncodeChar(format[index]);
      } else if index + 1 == |format| {
        nextIndex := index + 1;
        piece := "%";
      } else {
        var directive := format[index + 1];
        nextIndex := index + 2;
        piece := Spec.DirectiveTextSpec(directive, status);
      }
      assert Spec.FormatStepRelation(format, status, index, nextIndex, piece);
      ConcatPiecesSnoc(pieces, piece);
      ghost var oldPieces := pieces;
      ghost var oldCuts := cuts;
      assert forall i: nat {:trigger oldCuts[i], oldCuts[i + 1]} | i < |oldPieces| ::
          Spec.FormatStepRelation(
            format, status, oldCuts[i], oldCuts[i + 1], oldPieces[i]
          ) by {
        forall i: nat {:trigger oldCuts[i], oldCuts[i + 1]} | i < |oldPieces|
          ensures Spec.FormatStepRelation(
                    format, status, oldCuts[i], oldCuts[i + 1], oldPieces[i]
                  )
        {
          assert oldCuts == cuts;
          assert oldPieces == pieces;
          assert Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i]);
        }
      }
      pieces := pieces + [piece];
      cuts := cuts + [nextIndex];
      rendered := rendered + piece;
      assert forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < |pieces| ::
          Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i]) by {
        forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < |pieces|
          ensures Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i])
        {
          if i < |oldPieces| {
            assert Spec.FormatStepRelation(
                format, status, oldCuts[i], oldCuts[i + 1], oldPieces[i]
              );
            assert cuts[i] == oldCuts[i];
            assert cuts[i + 1] == oldCuts[i + 1];
            assert pieces[i] == oldPieces[i];
          } else {
            assert i == |oldPieces|;
            assert cuts[i] == index;
            assert cuts[i + 1] == nextIndex;
            assert pieces[i] == piece;
          }
        }
      }
      index := nextIndex;
    }

    assert Spec.RenderingWitnessRelation(format, status, rendered, cuts, pieces);
    assert Spec.FormatRenderingRelation(format, status, rendered);
  }

  method RenderUsingTemplate(
    format: string,
    status: BenchWorld.FileStatus,
    templateText: BenchWorld.Bytes,
    cuts: seq<nat>,
    templatePieces: seq<BenchWorld.Bytes>
  ) returns (rendered: BenchWorld.Bytes)
    requires Spec.RenderingWitnessRelation(
               format, BenchWorld.DEFAULT_FILE_STATUS, templateText, cuts, templatePieces
             )
    ensures Spec.FormatRenderingRelation(format, status, rendered)
  {
    assert Spec.PrefixRenderingWitnessRelation(
      format, BenchWorld.DEFAULT_FILE_STATUS, |format|, templateText, cuts, templatePieces
    );
    rendered := "";
    ghost var pieces: seq<BenchWorld.Bytes> := [];
    var step: nat := 0;
    while step + 1 < |cuts|
      invariant step < |cuts|
      invariant |pieces| == step
      invariant rendered == Spec.ConcatPiecesSpec(pieces)
      invariant forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < step ::
                  Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i])
      decreases |cuts| - step
    {
      var lo := cuts[step];
      var hi := cuts[step + 1];
      assert Spec.FormatStepRelation(
          format, BenchWorld.DEFAULT_FILE_STATUS, lo, hi, templatePieces[step]
        );
      var piece :=
        if format[lo] != '%' then Utf8.EncodeChar(format[lo])
        else if lo + 1 == hi then "%"
        else Spec.DirectiveTextSpec(format[lo + 1], status);
      assert Spec.FormatStepRelation(format, status, lo, hi, piece);
      ConcatPiecesSnoc(pieces, piece);
      ghost var oldPieces := pieces;
      pieces := pieces + [piece];
      rendered := rendered + piece;
      assert forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < step + 1 ::
          Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i]) by {
        forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < step + 1
          ensures Spec.FormatStepRelation(format, status, cuts[i], cuts[i + 1], pieces[i])
        {
          if i < step {
            assert pieces[i] == oldPieces[i];
          } else {
            assert i == step;
          }
        }
      }
      step := step + 1;
    }
    assert step + 1 == |cuts|;
    assert Spec.RenderingWitnessRelation(format, status, rendered, cuts, pieces);
  }

  lemma RenderingIgnoresRawMetadata(
    format: string,
    observed: BenchWorld.FileStatus,
    expected: BenchWorld.FileStatus,
    rendered: BenchWorld.Bytes
  )
    requires observed == expected
    requires Spec.FormatRenderingRelation(format, observed, rendered)
    ensures Spec.FormatRenderingRelation(format, expected, rendered)
  {
  }

  ghost predicate FileStepSummaryFields(
    cmd: Schema.StatCmd,
    path: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
  {
    var observation := IOContract.GetFileStatusResultFields(fs, path, cmd.followSymlink);
    match observation
    case Ok(status) =>
      !hadError && errOut == "" &&
      exists rendered: BenchWorld.Bytes ::
        Spec.FormatRenderingRelation(cmd.format, status, rendered) &&
        out == rendered + "\n"
    case Err(error) =>
      hadError && out == "" &&
      errOut == Spec.ErrorMessageSpec(path, IOContract.IOErrorErrno(error))
  }

  ghost predicate RunFilesSummaryFields(
    cmd: Schema.StatCmd,
    files: seq<BenchWorld.Path>,
    fs: BenchWorld.FileSystem,
    hadError: bool,
    out: BenchWorld.Bytes,
    errOut: BenchWorld.Bytes
  )
    decreases |files|
  {
    if |files| == 0 then
      !hadError && out == "" && errOut == ""
    else
      exists prefixError: bool, prefixOut: BenchWorld.Bytes, prefixErrOut: BenchWorld.Bytes,
        stepError: bool, stepOut: BenchWorld.Bytes, stepErrOut: BenchWorld.Bytes
        {:trigger RunFilesSummaryFields(
          cmd, files[..|files| - 1], fs, prefixError, prefixOut, prefixErrOut
        ), FileStepSummaryFields(
          cmd, files[|files| - 1], fs, stepError, stepOut, stepErrOut
        )} ::
        RunFilesSummaryFields(
          cmd, files[..|files| - 1], fs, prefixError, prefixOut, prefixErrOut
        ) &&
        FileStepSummaryFields(
          cmd, files[|files| - 1], fs, stepError, stepOut, stepErrOut
        ) &&
        hadError == (prefixError || stepError) &&
        out == prefixOut + stepOut && errOut == prefixErrOut + stepErrOut
  }

  twostate predicate CoreSummary(raw: Schema.StatCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion, io.stdoutRegion, io.stderrRegion
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() && io.stderr() == old(io.stderr()) && exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() && io.stderr() == old(io.stderr()) && exit == 0
    else if cmd.mode == Schema.ModeMissingFormat then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MissingFormatMessageSpec() && exit == 1
    else if cmd.mode == Schema.ModeMissingOperand then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MissingOperandMessageSpec() && exit == 1
    else
      Spec.FormatValidSpec(cmd.format) &&
      exists hadError: bool, out: BenchWorld.Bytes, errOut: BenchWorld.Bytes ::
        RunFilesSummaryFields(cmd, cmd.files, old(io.fs()), hadError, out, errOut) &&
        io.stdout() == old(io.stdout()) + out && io.stderr() == old(io.stderr()) + errOut &&
        exit == (if hadError then 1 else 0)
  }

  method RunCore(raw: Schema.StatCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Schema.Command(raw);

    if cmd.mode == Schema.ModeHelp {
      io.AppendStdout(Spec.HelpTextSpec());
      return 0;
    }
    if cmd.mode == Schema.ModeVersion {
      io.AppendStdout(Spec.VersionTextSpec());
      return 0;
    }
    if cmd.mode == Schema.ModeMissingFormat {
      io.AppendStderr(Spec.MissingFormatMessageSpec());
      return 1;
    }
    if cmd.mode == Schema.ModeMissingOperand {
      io.AppendStderr(Spec.MissingOperandMessageSpec());
      return 1;
    }

    var templateText, validCuts, templatePieces := RenderFormat(
      cmd.format, BenchWorld.DEFAULT_FILE_STATUS
    );
    assert Spec.FormatValidSpec(cmd.format);

    var output: BenchWorld.Bytes := "";
    var errors: BenchWorld.Bytes := "";
    var hadError := false;
    var index := 0;
    while index < |cmd.files|
      invariant 0 <= index <= |cmd.files|
      invariant io.stdout() == preStdout && io.stderr() == preStderr
      invariant RunFilesSummaryFields(
                  cmd, cmd.files[..index], preFs, hadError, output, errors
                )
      decreases |cmd.files| - index
    {
      var path := cmd.files[index];
      var ok, status, errno := io.GetFileStatus(path, cmd.followSymlink);
      var stepError := false;
      var stepOut: BenchWorld.Bytes := "";
      var stepErrOut: BenchWorld.Bytes := "";
      if ok {
        var text := RenderUsingTemplate(
          cmd.format, status, templateText, validCuts, templatePieces
        );
        ghost var expected := IOContract.GetFileStatusResultFields(
          preFs, path, cmd.followSymlink
        );
        RenderingIgnoresRawMetadata(cmd.format, status, expected.v, text);
        stepOut := text + "\n";
        assert FileStepSummaryFields(cmd, path, preFs, stepError, stepOut, stepErrOut);
      } else {
        stepError := true;
        stepErrOut := Spec.ErrorMessageSpec(path, errno);
        assert FileStepSummaryFields(cmd, path, preFs, stepError, stepOut, stepErrOut);
      }
      ghost var prefixError := hadError;
      ghost var prefixOut := output;
      ghost var prefixErrOut := errors;
      ghost var prefixFiles := cmd.files[..index];
      hadError := hadError || stepError;
      output := output + stepOut;
      errors := errors + stepErrOut;
      index := index + 1;
      assert cmd.files[..index] == prefixFiles + [path];
      ghost var nextFiles := cmd.files[..index];
      assert |nextFiles| > 0;
      assert nextFiles[..|nextFiles| - 1] == prefixFiles;
      assert nextFiles[|nextFiles| - 1] == path;
      assert RunFilesSummaryFields(
          cmd, nextFiles, preFs, hadError, output, errors
        ) by {
        assert exists priorError: bool,
            priorOut: BenchWorld.Bytes,
            priorErrOut: BenchWorld.Bytes,
            finalError: bool,
            finalOut: BenchWorld.Bytes,
            finalErrOut: BenchWorld.Bytes
            {:trigger RunFilesSummaryFields(
              cmd, prefixFiles, preFs, priorError, priorOut, priorErrOut
            ), FileStepSummaryFields(
              cmd, path, preFs, finalError, finalOut, finalErrOut
            )} ::
            RunFilesSummaryFields(cmd, prefixFiles, preFs, priorError, priorOut, priorErrOut) &&
            FileStepSummaryFields(cmd, path, preFs, finalError, finalOut, finalErrOut) &&
            hadError == (priorError || finalError) &&
            output == priorOut + finalOut && errors == priorErrOut + finalErrOut;
      }
    }

    assert cmd.files[..|cmd.files|] == cmd.files;
    assert RunFilesSummaryFields(cmd, cmd.files, preFs, hadError, output, errors);
    io.AppendStdout(output);
    assert io.stdout() == preStdout + output;
    assert io.stderr() == preStderr;
    io.AppendStderr(errors);
    assert io.stdout() == preStdout + output;
    assert io.stderr() == preStderr + errors;
    exit := if hadError then 1 else 0;
    assert exists finalHadError: bool,
        finalOut: BenchWorld.Bytes,
        finalErrOut: BenchWorld.Bytes
        {:trigger RunFilesSummaryFields(
          cmd, cmd.files, preFs, finalHadError, finalOut, finalErrOut
        )} ::
        RunFilesSummaryFields(
          cmd, cmd.files, preFs, finalHadError, finalOut, finalErrOut
        ) &&
        io.stdout() == preStdout + finalOut &&
        io.stderr() == preStderr + finalErrOut &&
        exit == (if finalHadError then 1 else 0);
    assert CoreSummary(raw, io, exit);
  }
}
