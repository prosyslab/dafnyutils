include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "TouchSchema.dfy"
include "TouchSpec.dfy"

module TouchCore {
  import BenchIO
  import IOContract
  import BenchWorld
  import Utf8 = Utf8Semantics
  import Schema = TouchSchema
  import Spec = TouchSpec

  const ENOENT: int := 2

  ghost predicate SetPathTimesSummaryFields(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    path: BenchWorld.Path,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    fs2: BenchWorld.FileSystem,
    ok: bool,
    err: int
  )
  {
    Spec.SetPathTimesSpecFields(
      observations, path, followSymlink, selection, source,
      preFs, preNow, fs2, ok, err
    )
  }

  ghost predicate SetStdoutTimesSummaryFields(
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preNow: int,
    beforeTarget: BenchWorld.StdoutTimestampState,
    afterTarget: BenchWorld.StdoutTimestampState,
    ok: bool,
    err: int
  )
  {
    Spec.SetStdoutTimesSpecFields(
      selection, source, preNow, beforeTarget, afterTarget, ok, err
    )
  }

  ghost predicate RunStepSummaryFields(
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
  {
    if path == "-" then
      fs2 == preFs &&
      stdout2 == preStdout &&
      exists okStdout: bool, stdoutErr: int ::
        SetStdoutTimesSummaryFields(
          selection, source, preNow, preStdoutTarget, stdoutTarget2,
          okStdout, stdoutErr
        ) &&
        hadError == !okStdout &&
        errOut == (if okStdout then [] else Spec.StdoutErrorMessageSpec(stdoutErr))
    else
      stdout2 == preStdout &&
      stdoutTarget2 == preStdoutTarget &&
      exists found: bool, existsErr: int ::
        IOContract.TrustedPathExistsContractFields(
          observations, preFs, path, followSymlink, found, existsErr
        ) &&
        if found then
          exists okSet: bool, setErr: int ::
            SetPathTimesSummaryFields(
              observations, path, followSymlink, selection, source,
              preFs, preNow, fs2, okSet, setErr
            ) &&
            hadError == !okSet &&
            errOut == (if okSet then [] else Spec.TouchErrorMessageSpec(path, setErr))
        else if noCreate then
          fs2 == preFs &&
          hadError == (existsErr != ENOENT) &&
          errOut == (if existsErr == ENOENT then [] else Spec.TouchErrorMessageSpec(path, existsErr))
        else if !followSymlink then
          fs2 == preFs &&
          hadError == true &&
          errOut == Spec.SetTimesErrorMessageSpec(path, existsErr)
        else
          exists okCreate: bool, createErr: int, createFs: BenchWorld.FileSystem ::
            IOContract.TrustedCreateFileContractFields(
              observations, preFs, preNow, path,
              okCreate, createErr, createFs
            ) &&
            if okCreate then
              if source == Schema.TimeSourceCurrent && selection == Schema.TimeBoth then
                fs2 == createFs &&
                hadError == false &&
                errOut == []
              else
                exists okSet: bool, setErr: int ::
                  SetPathTimesSummaryFields(
                    observations, path, followSymlink, selection, source,
                    createFs, preNow, fs2, okSet, setErr
                  ) &&
                  hadError == !okSet &&
                  errOut == (if okSet then [] else Spec.TouchErrorMessageSpec(path, setErr))
            else
              fs2 == createFs &&
              hadError == true &&
              errOut == Spec.TouchErrorMessageSpec(path, createErr)
  }

  opaque ghost predicate RunFilesSummaryFields(
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
  )
    decreases |files|
  {
    if |files| == 0 then
      fs2 == preFs &&
      stdout2 == preStdout &&
      stdoutTarget2 == preStdoutTarget &&
      hadError == false &&
      errOut == []
    else
      exists fs1: BenchWorld.FileSystem, stdout1: BenchWorld.Bytes,
        stdoutTarget1: BenchWorld.StdoutTimestampState,
        prefixError: bool, stepError: bool, prefixOut: BenchWorld.Bytes, stepOut: BenchWorld.Bytes
        {:trigger RunFilesSummaryFields(observations, files[..|files| - 1], noCreate, followSymlink, selection, source, preFs, preNow, preStdout, preStdoutTarget, fs1, stdout1, stdoutTarget1, prefixError, prefixOut),
        RunStepSummaryFields(observations, files[|files| - 1], noCreate, followSymlink, selection, source, fs1, preNow, stdout1, stdoutTarget1, fs2, stdout2, stdoutTarget2, stepError, stepOut)} ::
        RunFilesSummaryFields(
          observations, files[..|files| - 1], noCreate, followSymlink, selection, source,
          preFs, preNow, preStdout, preStdoutTarget,
          fs1, stdout1, stdoutTarget1, prefixError, prefixOut
        ) &&
        RunStepSummaryFields(
          observations, files[|files| - 1], noCreate, followSymlink, selection, source,
          fs1, preNow, stdout1, stdoutTarget1,
          fs2, stdout2, stdoutTarget2, stepError, stepOut
        ) &&
        hadError == (prefixError || stepError) &&
        errOut == prefixOut + stepOut
  }


  lemma RunFilesSummaryFieldsEmpty(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState
  )
    ensures RunFilesSummaryFields(
              observations, [], noCreate, followSymlink, selection, source,
              preFs, preNow, preStdout, preStdoutTarget,
              preFs, preStdout, preStdoutTarget, false, []
            )
  {
    reveal RunFilesSummaryFields();
  }

  lemma RunFilesSummaryFieldsAppend(
    observations: (BenchWorld.TrustedFilesystemRequest) -> BenchWorld.TrustedFilesystemResult,
    files: seq<BenchWorld.Path>,
    path: BenchWorld.Path,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    preFs: BenchWorld.FileSystem,
    preNow: int,
    preStdout: BenchWorld.Bytes,
    preStdoutTarget: BenchWorld.StdoutTimestampState,
    fs1: BenchWorld.FileSystem,
    stdout1: BenchWorld.Bytes,
    stdoutTarget1: BenchWorld.StdoutTimestampState,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stdoutTarget2: BenchWorld.StdoutTimestampState,
    prefixError: bool,
    stepError: bool,
    prefixOut: BenchWorld.Bytes,
    stepOut: BenchWorld.Bytes
  )
    requires RunFilesSummaryFields(observations, files, noCreate, followSymlink, selection, source, preFs, preNow, preStdout, preStdoutTarget, fs1, stdout1, stdoutTarget1, prefixError, prefixOut)
    requires RunStepSummaryFields(observations, path, noCreate, followSymlink, selection, source, fs1, preNow, stdout1, stdoutTarget1, fs2, stdout2, stdoutTarget2, stepError, stepOut)
    ensures RunFilesSummaryFields(observations, files + [path], noCreate, followSymlink, selection, source, preFs, preNow, preStdout, preStdoutTarget, fs2, stdout2, stdoutTarget2, prefixError || stepError, prefixOut + stepOut)
  {
    reveal RunFilesSummaryFields();
    assert |files + [path]| > 0;
    assert (files + [path])[..|files + [path]| - 1] == files;
    assert (files + [path])[|files + [path]| - 1] == path;
  }

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpTextSpec()
  {
    out := Spec.HelpTextSpec();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionTextSpec()
  {
    out := Spec.VersionTextSpec();
  }

  method GetTouchErrorMessage(path: BenchWorld.Path, err: int, io: BenchIO.IO)
      returns (out: BenchWorld.Bytes)
    ensures out == Spec.TouchErrorMessageSpec(path, err)
  {
    var quoted := io.QuoteafPath(path);
    var errnoText := io.GetCLocaleErrnoText(err);
    out := Utf8.Encode("touch: cannot touch ") + quoted
      + Utf8.Encode(": " + errnoText + "\n");
  }

  method GetReferenceErrorMessage(path: BenchWorld.Path, err: int, io: BenchIO.IO)
      returns (out: BenchWorld.Bytes)
    ensures out == Spec.ReferenceErrorMessageSpec(path, err)
  {
    var quoted := io.QuoteafPath(path);
    var errnoText := io.GetCLocaleErrnoText(err);
    out := Utf8.Encode("touch: failed to get attributes of ") + quoted
      + Utf8.Encode(": " + errnoText + "\n");
  }

  method GetSetTimesErrorMessage(path: BenchWorld.Path, err: int, io: BenchIO.IO)
      returns (out: BenchWorld.Bytes)
    ensures out == Spec.SetTimesErrorMessageSpec(path, err)
  {
    var quoted := io.QuoteafPath(path);
    var errnoText := io.GetCLocaleErrnoText(err);
    out := Utf8.Encode("touch: setting times of ") + quoted
      + Utf8.Encode(": " + errnoText + "\n");
  }

  method GetStdoutErrorMessage(err: int, io: BenchIO.IO) returns (out: BenchWorld.Bytes)
    ensures out == Spec.StdoutErrorMessageSpec(err)
  {
    var errnoText := io.GetCLocaleErrnoText(err);
    out := Utf8.Encode("touch: setting times of standard output: "
      + errnoText + "\n");
  }

  method GetMissingOperandMessage() returns (out: string)
    ensures out == Spec.MissingOperandMessageSpec()
  {
    out := Spec.MissingOperandMessageSpec();
  }

  method GetInvalidTimeMessage(value: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.InvalidTimeMessageSpec(value)
  {
    out := Spec.InvalidTimeMessageSpec(value);
  }

  method GetAmbiguousTimeMessage(value: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.AmbiguousTimeMessageSpec(value)
  {
    out := Spec.AmbiguousTimeMessageSpec(value);
  }

  method GetInvalidDateMessage(value: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.InvalidDateMessageSpec(value)
  {
    out := Spec.InvalidDateMessageSpec(value);
  }

  twostate predicate ResolvedRunSummaryFields(
    cmd: Schema.TouchCmd,
    io: BenchIO.IO,
    exit: int
  )
    reads io.Footprint()
  {
    exists selection: Schema.TimeSelection, source: Schema.TimeSource ::
      Spec.RequestedSelection(cmd, selection) &&
      Spec.RequestedSourceFields(
        old(io.trustedFilesystem()), cmd, old(io.fs()), old(io.now()),
        old(io.trustedTimeParses()), source
      ) &&
      if |cmd.files| == 0 then
        io.fs() == old(io.fs()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) + Spec.MissingOperandMessageSpec() &&
        exit == 1
      else
        exists hadError: bool, errOut: BenchWorld.Bytes ::
          exit == (if hadError then 1 else 0) &&
          RunFilesSummaryFields(
            old(io.trustedFilesystem()), cmd.files, cmd.noCreate,
            cmd.followSymlink, selection, source,
            old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
            io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
          ) &&
          io.stderr() == old(io.stderr()) + errOut
  }

  twostate predicate CoreSummary(raw: Schema.TouchCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidTime then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.InvalidTimeMessageSpec(cmd.timeArg)
    else if cmd.mode == Schema.ModeAmbiguousTime then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.AmbiguousTimeMessageSpec(cmd.timeArg)
    else if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      exit == 0 &&
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr())
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      exit == 0 &&
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr())
    else if cmd.timeArg != "" && Schema.ClassifyTimeWord(cmd.timeArg) == Schema.TimeWordAmbiguous then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.AmbiguousTimeMessageSpec(cmd.timeArg)
    else if cmd.timeArg != "" && Schema.ClassifyTimeWord(cmd.timeArg) == Schema.TimeWordInvalid then
      io.fs() == old(io.fs()) &&
      exit == 1 &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.InvalidTimeMessageSpec(cmd.timeArg)
    else if cmd.hasTimestamp then
      (exists sec: int, nsec: int ::
         IOContract.ParseTimestampContractFields(
           old(io.trustedTimeParses()), cmd.timestampArg, old(io.now()), 0,
           false, sec, nsec
         ) &&
         io.fs() == old(io.fs()) &&
         io.stdout() == old(io.stdout()) &&
         io.stderr() == old(io.stderr()) + Spec.InvalidDateMessageSpec(cmd.timestampArg) &&
         exit == 1) ||
      (Spec.SourceConflict(cmd) &&
       IOContract.TrustedTimeParseResultFields(
         old(io.trustedTimeParses()),
         BenchWorld.TimestampParseRequest(cmd.timestampArg, old(io.now()), 0)).ok &&
       io.fs() == old(io.fs()) &&
       io.stdout() == old(io.stdout()) &&
       io.stderr() == old(io.stderr()) + Spec.SourceConflictMessageSpec() &&
       exit == 1) ||
      ResolvedRunSummaryFields(cmd, io, exit)
    else if cmd.hasDate then
      (cmd.hasReference &&
       var observed := old(io.trustedFilesystem())(
         BenchWorld.FilesystemQuery(
           old(io.fs()), cmd.referenceArg, cmd.followSymlink
         )
       );
       observed.postFs == old(io.fs()) && !observed.ok &&
         io.fs() == old(io.fs()) &&
         io.stdout() == old(io.stdout()) &&
         io.stderr() == old(io.stderr()) +
           Spec.ReferenceErrorMessageSpec(cmd.referenceArg, observed.err) &&
         exit == 1) ||
      (Spec.DateParseFailureFields(
         old(io.trustedFilesystem()), cmd, old(io.fs()), old(io.now()),
         old(io.trustedTimeParses())) &&
       io.fs() == old(io.fs()) &&
       io.stdout() == old(io.stdout()) &&
       io.stderr() == old(io.stderr()) + Spec.InvalidDateMessageSpec(cmd.dateArg) &&
       exit == 1) ||
      ResolvedRunSummaryFields(cmd, io, exit)
    else if cmd.hasReference then
      (var observed := old(io.trustedFilesystem())(
         BenchWorld.FilesystemQuery(
           old(io.fs()), cmd.referenceArg, cmd.followSymlink
         )
       );
       observed.postFs == old(io.fs()) && !observed.ok &&
         io.fs() == old(io.fs()) &&
         io.stdout() == old(io.stdout()) &&
         io.stderr() == old(io.stderr()) +
           Spec.ReferenceErrorMessageSpec(cmd.referenceArg, observed.err) &&
         exit == 1) ||
      ResolvedRunSummaryFields(cmd, io, exit)
    else
      ResolvedRunSummaryFields(cmd, io, exit)
  }

  method ResolveDateSource(
    cmd: Schema.TouchCmd, selection: Schema.TimeSelection, io: BenchIO.IO
  ) returns (ok: bool, source: Schema.TimeSource, errOut: BenchWorld.Bytes)
    requires cmd.hasDate && !Spec.SourceConflict(cmd)
    requires Spec.RequestedSelection(cmd, selection)
    ensures if ok then
      Spec.RequestedSourceFields(
        io.trustedFilesystem(), cmd, io.fs(), io.now(), io.trustedTimeParses(), source
      ) && errOut == []
    else
      (Spec.DateParseFailureFields(
        io.trustedFilesystem(), cmd, io.fs(), io.now(), io.trustedTimeParses()
      ) && errOut == Spec.InvalidDateMessageSpec(cmd.dateArg)) ||
      (cmd.hasReference &&
       var observed := io.trustedFilesystem()(
         BenchWorld.FilesystemQuery(io.fs(), cmd.referenceArg, cmd.followSymlink));
       observed.postFs == io.fs() && !observed.ok &&
       errOut == Spec.ReferenceErrorMessageSpec(cmd.referenceArg, observed.err))
  {
    ok := false;
    source := Schema.TimeSourceCurrent;
    errOut := [];
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    ghost var preParses := io.trustedTimeParses();
    ghost var preFilesystemObservations := io.trustedFilesystem();
    var nowSec := io.Now();
    var referenceSec := nowSec;
    var referenceNsec := 0;
    var accessReferenceSec := nowSec;
    var accessReferenceNsec := 0;
    if cmd.hasReference {
      var refOk, refAtimeSec, refAtimeNsec, refMtimeSec, refMtimeNsec,
        refIsDir, refIsSymlink, refDevice, refInode, refLinkCount, refErr :=
        io.GetFileTimes(cmd.referenceArg, cmd.followSymlink);
      if !refOk {
        errOut := GetReferenceErrorMessage(cmd.referenceArg, refErr, io);
        return;
      }
      accessReferenceSec := refAtimeSec;
      accessReferenceNsec := refAtimeNsec;
      referenceSec := refMtimeSec;
      referenceNsec := refMtimeNsec;
    }
    assert Spec.DateReferenceFields(
      preFilesystemObservations, cmd, preFs, preNow,
      referenceSec, referenceNsec
    ) by {
      reveal Spec.DateReferenceFields();
    }
    assert Spec.DateAccessReferenceFields(
      preFilesystemObservations, cmd, preFs, preNow,
      accessReferenceSec, accessReferenceNsec
    );
    var atimeSec := accessReferenceSec;
    var atimeNsec := accessReferenceNsec;
    var mtimeSec := referenceSec;
    var mtimeNsec := referenceNsec;
    if selection != Schema.TimeModify {
      var dateOk;
      dateOk, atimeSec, atimeNsec :=
        io.ParseDate(cmd.dateArg, accessReferenceSec, accessReferenceNsec);
      if !dateOk {
        assert Spec.DateParseFailureFields(
          preFilesystemObservations, cmd, preFs, preNow, preParses
        ) by {
          var aSec := accessReferenceSec;
          var aNsec := accessReferenceNsec;
          var mSec := referenceSec;
          var mNsec := referenceNsec;
        }
        errOut := Spec.InvalidDateMessageSpec(cmd.dateArg);
        return;
      }
    }
    if !cmd.hasReference && selection == Schema.TimeBoth {
      mtimeSec := atimeSec;
      mtimeNsec := atimeNsec;
    } else if selection != Schema.TimeAccess {
      var dateOk;
      dateOk, mtimeSec, mtimeNsec :=
        io.ParseDate(cmd.dateArg, referenceSec, referenceNsec);
      if !dateOk {
        assert Spec.DateParseFailureFields(
          preFilesystemObservations, cmd, preFs, preNow, preParses
        ) by {
          var aSec := accessReferenceSec;
          var aNsec := accessReferenceNsec;
          var mSec := referenceSec;
          var mNsec := referenceNsec;
        }
        errOut := Spec.InvalidDateMessageSpec(cmd.dateArg);
        return;
      }
    }
    source := Schema.TimeSourceFixed(atimeSec, atimeNsec, mtimeSec, mtimeNsec);
    assert Spec.RequestedSourceFields(
      preFilesystemObservations, cmd, preFs, preNow, preParses, source
    ) by {
      var aSec := accessReferenceSec;
      var aNsec := accessReferenceNsec;
      var mSec := referenceSec;
      var mNsec := referenceNsec;
    }
    ok := true;
  }

  method RunCore(raw: Schema.TouchCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion, io.stdoutTimestampRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    ghost var preNow := io.now();
    ghost var preParses := io.trustedTimeParses();
    ghost var preFilesystemObservations := io.trustedFilesystem();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeInvalidTime {
      var err := GetInvalidTimeMessage(cmd.timeArg);
      io.AppendStderr(err);
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeAmbiguousTime {
      var err := GetAmbiguousTimeMessage(cmd.timeArg);
      io.AppendStderr(err);
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeHelp {
      var out := GetHelpText();
      io.AppendStdout(out);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := GetVersionText();
      io.AppendStdout(out);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    var selection := Spec.RequestedSelectionValue(cmd);
    if cmd.timeArg != "" {
      var timeWord := Schema.ClassifyTimeWord(cmd.timeArg);
      if timeWord == Schema.TimeWordAmbiguous {
        var err := GetAmbiguousTimeMessage(cmd.timeArg);
        io.AppendStderr(err);
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      } else if timeWord == Schema.TimeWordInvalid {
        var err := GetInvalidTimeMessage(cmd.timeArg);
        io.AppendStderr(err);
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      }
    } else if cmd.touchAtime && !cmd.touchMtime {
      selection := Schema.TimeAccess;
    } else if cmd.touchMtime && !cmd.touchAtime {
      selection := Schema.TimeModify;
    }
    assert Spec.RequestedSelection(cmd, selection);

    var source := Schema.TimeSourceCurrent;
    if cmd.hasTimestamp {
      var nowSec := io.Now();
      var timestampOk, timestampSec, timestampNsec := io.ParseTimestamp(cmd.timestampArg, nowSec, 0);
      if !timestampOk {
        var err := GetInvalidDateMessage(cmd.timestampArg);
        io.AppendStderr(err);
        exit := 1;
        assert CoreSummary(raw, io, exit);
        return;
      }
      if Spec.SourceConflict(cmd) {
        io.AppendStderr(Spec.SourceConflictMessageSpec());
        exit := 1;
        return;
      }
      source := Schema.TimeSourceFixed(timestampSec, timestampNsec, timestampSec, timestampNsec);
      assert Spec.RequestedSourceFields(
        preFilesystemObservations, cmd, preFs, preNow, preParses, source
      );
    } else if cmd.hasDate {
      var dateOk, dateSource, dateError := ResolveDateSource(cmd, selection, io);
      if !dateOk {
        io.AppendStderr(dateError);
        exit := 1;
        return;
      }
      source := dateSource;
    } else if cmd.hasReference {
      var refOk, refAtimeSec, refAtimeNsec, refMtimeSec, refMtimeNsec,
          refIsDir, refIsSymlink, refDevice, refInode, refLinkCount, refErr :=
        io.GetFileTimes(cmd.referenceArg, cmd.followSymlink);
      if !refOk {
        var err := GetReferenceErrorMessage(cmd.referenceArg, refErr, io);
        io.AppendStderr(err);
        exit := 1;
        assert IOContract.TrustedFilesystemQueryContractFields(
            preFilesystemObservations, preFs,
            cmd.referenceArg, cmd.followSymlink, false,
            refAtimeSec, refAtimeNsec, refMtimeSec, refMtimeNsec,
            refIsDir, refIsSymlink, refDevice, refInode, refLinkCount, refErr
          );
        assert CoreSummary(raw, io, exit);
        return;
      }
      assert IOContract.TrustedFilesystemQueryContractFields(
          preFilesystemObservations, preFs,
          cmd.referenceArg, cmd.followSymlink, true,
          refAtimeSec, refAtimeNsec, refMtimeSec, refMtimeNsec,
          refIsDir, refIsSymlink, refDevice, refInode, refLinkCount, refErr
        );
      source := Schema.TimeSourceFixed(refAtimeSec, refAtimeNsec, refMtimeSec, refMtimeNsec);
      assert Spec.SuccessfulReferenceSourceFields(
        preFilesystemObservations, preFs, cmd.referenceArg,
        cmd.followSymlink, source
      ) by {
        reveal Spec.SuccessfulReferenceSourceFields();
      }
      assert Spec.RequestedSourceFields(
        preFilesystemObservations, cmd, preFs, preNow, preParses, source
      );
    }
    assert Spec.RequestedSourceFields(
      preFilesystemObservations, cmd, preFs, preNow, preParses, source
    );

    if |cmd.files| == 0 {
      var err := GetMissingOperandMessage();
      io.AppendStderr(err);
      exit := 1;
      assert ResolvedRunSummaryFields(cmd, io, exit) by {
        assert Spec.RequestedSelection(cmd, selection);
        assert Spec.RequestedSourceFields(
          preFilesystemObservations, cmd, preFs, preNow, preParses, source
        );
      }
      assert CoreSummary(raw, io, exit);
      return;
    }

    var hadError, errOut := RunFiles(cmd.files, cmd.noCreate, cmd.followSymlink, selection, source, io);
    io.AppendStderr(errOut);
    exit := if hadError then 1 else 0;
    assert io.stderr() == preStderr + errOut;
    assert RunFilesSummaryFields(
      preFilesystemObservations, cmd.files, cmd.noCreate,
      cmd.followSymlink, selection, source,
      preFs, preNow, preStdout, old(io.stdoutTimestamp()),
      io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
    );
    assert ResolvedRunSummaryFields(cmd, io, exit) by {
      assert Spec.RequestedSelection(cmd, selection);
      assert Spec.RequestedSourceFields(
        preFilesystemObservations, cmd, preFs, preNow, preParses, source
      );
    }
    assert CoreSummary(raw, io, exit);
  }

  method SetPathTimes(
    path: BenchWorld.Path,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    io: BenchIO.IO
  ) returns (ok: bool, err: int)
    modifies io.fsRegion
    ensures SetPathTimesSummaryFields(
              old(io.trustedFilesystem()), path, followSymlink, selection, source,
              old(io.fs()), old(io.now()), io.fs(), ok, err
            )
    decreases *
  {
    ok := false;
    err := 0;
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeBoth {
      ok, err := io.SetFileTimesNow(path, followSymlink);
      return;
    }
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeAccess {
      ok, err := io.SetFileAccessTimeNow(path, followSymlink);
      return;
    }
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeModify {
      ok, err := io.SetFileModificationTimeNow(path, followSymlink);
      return;
    }

    var atimeSec := 0;
    var atimeNsec := 0;
    var mtimeSec := 0;
    var mtimeNsec := 0;

    match source
    case TimeSourceCurrent =>
      var nowSec := io.Now();
      atimeSec := nowSec;
      mtimeSec := nowSec;
    case TimeSourceFixed(sourceAtimeSec, sourceAtimeNsec, sourceMtimeSec, sourceMtimeNsec) =>
      atimeSec := sourceAtimeSec;
      atimeNsec := sourceAtimeNsec;
      mtimeSec := sourceMtimeSec;
      mtimeNsec := sourceMtimeNsec;

      if selection != Schema.TimeBoth {
        var getOk, oldAtimeSec, oldAtimeNsec, oldMtimeSec, oldMtimeNsec,
            isDir, isSymlink, device, inode, linkCount, getErr :=
          io.GetFileTimes(path, followSymlink);
        if !getOk {
          ok := false;
          err := getErr;
          return;
        }
        if selection == Schema.TimeAccess {
          mtimeSec := oldMtimeSec;
          mtimeNsec := oldMtimeNsec;
        } else {
          atimeSec := oldAtimeSec;
          atimeNsec := oldAtimeNsec;
        }
      }

      ok, err := io.SetFileTimes(
        path, followSymlink, atimeSec, atimeNsec, mtimeSec, mtimeNsec
      );
  }

  method SetStdoutTimesSelected(
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    io: BenchIO.IO
  ) returns (ok: bool, err: int)
    modifies io.stdoutTimestampRegion
    ensures SetStdoutTimesSummaryFields(
              selection, source, old(io.now()),
              old(io.stdoutTimestamp()), io.stdoutTimestamp(), ok, err
            )
    decreases *
  {
    ok := false;
    err := 0;
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeBoth {
      ok, err := io.SetStdoutTimesNow();
      return;
    }
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeAccess {
      ok, err := io.SetStdoutAccessTimeNow();
      return;
    }
    if source == Schema.TimeSourceCurrent && selection == Schema.TimeModify {
      ok, err := io.SetStdoutModificationTimeNow();
      return;
    }

    var atimeSec := 0;
    var atimeNsec := 0;
    var mtimeSec := 0;
    var mtimeNsec := 0;
    match source
    case TimeSourceCurrent =>
      var nowSec := io.Now();
      atimeSec := nowSec;
      mtimeSec := nowSec;
    case TimeSourceFixed(sourceAtimeSec, sourceAtimeNsec, sourceMtimeSec, sourceMtimeNsec) =>
      atimeSec := sourceAtimeSec;
      atimeNsec := sourceAtimeNsec;
      mtimeSec := sourceMtimeSec;
      mtimeNsec := sourceMtimeNsec;
      ok, err := io.SetStdoutTimes(
        if selection == Schema.TimeModify then BenchWorld.Keep else BenchWorld.Exact(atimeSec, atimeNsec),
        if selection == Schema.TimeAccess then BenchWorld.Keep else BenchWorld.Exact(mtimeSec, mtimeNsec)
      );
  }

  method {:isolate_assertions} RunFiles(
    files: seq<BenchWorld.Path>,
    noCreate: bool,
    followSymlink: bool,
    selection: Schema.TimeSelection,
    source: Schema.TimeSource,
    io: BenchIO.IO
  )
    returns (hadError: bool, errOut: BenchWorld.Bytes)
    modifies io.fsRegion, io.stdoutRegion, io.stdoutTimestampRegion
    ensures RunFilesSummaryFields(
              old(io.trustedFilesystem()), files, noCreate,
              followSymlink, selection, source,
              old(io.fs()), old(io.now()), old(io.stdout()), old(io.stdoutTimestamp()),
              io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
            )
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    ghost var preStdout := io.stdout();
    ghost var preStdoutTarget := io.stdoutTimestamp();
    ghost var preFilesystemObservations := io.trustedFilesystem();
    hadError := false;
    errOut := [];
    var i := 0;
    RunFilesSummaryFieldsEmpty(
      preFilesystemObservations, noCreate, followSymlink, selection, source,
      preFs, preNow, preStdout, preStdoutTarget
    );
    while i < |files|
      invariant 0 <= i <= |files|
      invariant RunFilesSummaryFields(
                  preFilesystemObservations, files[..i], noCreate,
                  followSymlink, selection, source,
                  preFs, preNow, preStdout, preStdoutTarget,
                  io.fs(), io.stdout(), io.stdoutTimestamp(), hadError, errOut
                )
      decreases |files| - i
    {
      var prefixError := hadError;
      var prefixOut := errOut;
      ghost var stepFs := io.fs();
      ghost var stepStdout := io.stdout();
      ghost var stepStdoutTarget := io.stdoutTimestamp();
      var path := files[i];
      var stepError := false;
      var stepOut: BenchWorld.Bytes := [];

      if path == "-" {
        var okStdout, stdoutErr := SetStdoutTimesSelected(selection, source, io);
        stepError := !okStdout;
        if stepError {
          stepOut := GetStdoutErrorMessage(stdoutErr, io);
        }
      } else {
        var found, existsErr := io.PathExists(path, followSymlink);
        if found {
          var okSet, setErr := SetPathTimes(path, followSymlink, selection, source, io);
          stepError := !okSet;
          if stepError {
            stepOut := GetTouchErrorMessage(path, setErr, io);
          }
        } else if noCreate {
          if existsErr == ENOENT {
            stepError := false;
          } else {
            stepError := true;
            stepOut := GetTouchErrorMessage(path, existsErr, io);
          }
        } else if !followSymlink {
          stepError := true;
          stepOut := GetSetTimesErrorMessage(path, existsErr, io);
        } else {
          var okCreate, createErr := io.CreateFile(path);
          if okCreate {
            if source == Schema.TimeSourceCurrent && selection == Schema.TimeBoth {
              stepError := false;
            } else {
              var okSet, setErr := SetPathTimes(path, followSymlink, selection, source, io);
              stepError := !okSet;
              if stepError {
                stepOut := GetTouchErrorMessage(path, setErr, io);
              }
            }
          } else {
            stepError := true;
            stepOut := GetTouchErrorMessage(path, createErr, io);
          }
        }
      }

      hadError := prefixError || stepError;
      errOut := prefixOut + stepOut;
      assert RunStepSummaryFields(
        preFilesystemObservations, path, noCreate, followSymlink, selection, source,
        stepFs, preNow, stepStdout, stepStdoutTarget,
        io.fs(), io.stdout(), io.stdoutTimestamp(), stepError, stepOut
      );
      RunFilesSummaryFieldsAppend(
        preFilesystemObservations, files[..i], path,
        noCreate, followSymlink, selection, source,
        preFs, preNow, preStdout, preStdoutTarget,
        stepFs, stepStdout, stepStdoutTarget,
        io.fs(), io.stdout(), io.stdoutTimestamp(),
        prefixError, stepError, prefixOut, stepOut
      );
      assert files[..i] + [path] == files[..i + 1];
      i := i + 1;
    }
    assert i == |files|;
    assert files[..i] == files;
  }
}
