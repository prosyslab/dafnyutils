include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "LnSchema.dfy"
include "LnSpec.dfy"

module LnCore {
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = LnSchema
  import Spec = LnSpec

  twostate predicate CoreSummary(raw: Schema.LnCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if |cmd.operands| == 0 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MissingOperandMessageSpec() &&
      exit == 1
    else if !cmd.symbolic then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.UnsupportedHardLinkMessageSpec() &&
      exit == 1
    else if |cmd.operands| != 2 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.UnsupportedTargetDirectoryMessageSpec() &&
      exit == 1
    else
      exists dirOk: bool, isDir: bool, dirErr: int ::
        IOContract.IsDirectoryStrictContractFields(
          old(io.fs()), cmd.operands[1], true, dirOk, isDir, dirErr
        ) &&
        if dirOk && isDir then
          io.fs() == old(io.fs()) &&
          io.stdout() == old(io.stdout()) &&
          io.stderr() == old(io.stderr()) +
          Spec.UnsupportedTargetDirectoryMessageSpec() &&
          exit == 1
        else
          exists ok: bool, err: int ::
            IOContract.CreateSymlinkContractFields(
              old(io.fs()),
              old(io.now()),
              cmd.operands[1],
              cmd.operands[0],
              ok,
              err,
              io.fs()
            ) &&
            io.stdout() == old(io.stdout()) &&
            io.stderr() ==
            (if ok then
               old(io.stderr())
             else
               old(io.stderr()) +
               Spec.CreateSymlinkErrorMessageSpec(cmd.operands[1], err)) &&
            exit == (if ok then 0 else 1)
  }

  method RunCore(raw: Schema.LnCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preFs := io.fs();
    ghost var preNow := io.now();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
      io.AppendStdout(Spec.HelpTextSpec());
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      io.AppendStdout(Spec.VersionTextSpec());
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if |cmd.operands| == 0 {
      io.AppendStderr(Spec.MissingOperandMessageSpec());
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if !cmd.symbolic {
      io.AppendStderr(Spec.UnsupportedHardLinkMessageSpec());
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if |cmd.operands| != 2 {
      io.AppendStderr(Spec.UnsupportedTargetDirectoryMessageSpec());
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }

    var rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1 := io.GetFileStatus(cmd.operands[1], true);
    IOContract.FileStatusImpliesMetadata(io.fs(), cmd.operands[1], true, rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1);
    var dirOk := rawMetadataOk1;
    var isDir := rawMetadataStatus1.kind == BenchWorld.DirectoryKind;
    var dirErr := rawMetadataErr1;
    assert IOContract.IsDirectoryStrictContractFields(preFs, cmd.operands[1], true, dirOk, isDir, dirErr);
    if dirOk && isDir {
      io.AppendStderr(Spec.UnsupportedTargetDirectoryMessageSpec());
      exit := 1;
      assert CoreSummary(raw, io, exit) by {
        assert exists dirOk0: bool, isDir0: bool, dirErr0: int ::
            IOContract.IsDirectoryStrictContractFields(
              old(io.fs()), cmd.operands[1], true, dirOk0, isDir0, dirErr0
            ) &&
            dirOk0 && isDir0 &&
            io.fs() == old(io.fs()) &&
            io.stdout() == old(io.stdout()) &&
            io.stderr() == old(io.stderr()) +
            Spec.UnsupportedTargetDirectoryMessageSpec() &&
            exit == 1 by {
          assert preFs == old(io.fs());
        }
      }
      return;
    }

    var ok, createErr := io.CreateSymlink(cmd.operands[1], cmd.operands[0]);
    assert IOContract.CreateSymlinkContractFields(
        preFs,
        preNow,
        cmd.operands[1],
        cmd.operands[0],
        ok,
        createErr,
        io.fs()
      );
    if ok {
      exit := 0;
      assert io.stderr() == preStderr;
    } else {
      io.AppendStderr(Spec.CreateSymlinkErrorMessageSpec(cmd.operands[1], createErr));
      exit := 1;
      assert io.stderr() == preStderr + Spec.CreateSymlinkErrorMessageSpec(cmd.operands[1], createErr);
    }
    assert io.stdout() == preStdout;
    assert io.stderr() ==
           (if ok then preStderr else preStderr + Spec.CreateSymlinkErrorMessageSpec(cmd.operands[1], createErr));
    assert exit == (if ok then 0 else 1);
    assert preFs == old(io.fs());
    assert preNow == old(io.now());
    assert preStdout == old(io.stdout());
    assert preStderr == old(io.stderr());
    assert CoreSummary(raw, io, exit) by {
      assert exists dirOk0: bool, isDir0: bool, dirErr0: int ::
          IOContract.IsDirectoryStrictContractFields(
            old(io.fs()), cmd.operands[1], true, dirOk0, isDir0, dirErr0
          ) &&
          !(dirOk0 && isDir0) &&
          exists ok0: bool, err0: int ::
            IOContract.CreateSymlinkContractFields(
              old(io.fs()),
              old(io.now()),
              cmd.operands[1],
              cmd.operands[0],
              ok0,
              err0,
              io.fs()
            ) &&
            io.stdout() == old(io.stdout()) &&
            io.stderr() ==
            (if ok0 then
               old(io.stderr())
             else
               old(io.stderr()) +
               Spec.CreateSymlinkErrorMessageSpec(cmd.operands[1], err0)) &&
            exit == (if ok0 then 0 else 1) by {
        assert preFs == old(io.fs());
        assert IOContract.IsDirectoryStrictContractFields(
            old(io.fs()), cmd.operands[1], true, dirOk, isDir, dirErr
          );
        assert !(dirOk && isDir);
        assert IOContract.CreateSymlinkContractFields(
            old(io.fs()),
            old(io.now()),
            cmd.operands[1],
            cmd.operands[0],
            ok,
            createErr,
            io.fs()
          );
        assert exists ok0: bool, err0: int ::
            IOContract.CreateSymlinkContractFields(
              old(io.fs()),
              old(io.now()),
              cmd.operands[1],
              cmd.operands[0],
              ok0,
              err0,
              io.fs()
            ) &&
            io.stdout() == old(io.stdout()) &&
            io.stderr() ==
            (if ok0 then
               old(io.stderr())
             else
               old(io.stderr()) +
               Spec.CreateSymlinkErrorMessageSpec(cmd.operands[1], err0)) &&
            exit == (if ok0 then 0 else 1);
      }
    }
  }
}
