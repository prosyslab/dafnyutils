include "../../core/World.dfy"
include "../../core/IOContract.dfy"
include "LnSchema.dfy"
include "LnCore.dfy"
include "LnSpec.dfy"

module LnProof {
  import BenchIO
  import IOContract
  import BenchWorld
  import Schema = LnSchema
  import Core = LnCore
  import Spec = LnSpec

  lemma IsDirectoryProbeMatchesLinkNameFs(
    fs: BenchWorld.FileSystem,
    linkName: BenchWorld.Path,
    ok: bool,
    isDir: bool,
    err: int
  )
    requires IOContract.IsDirectoryStrictContractFields(
               fs, linkName, true, ok, isDir, err
             )
    ensures ok ==> isDir == Spec.LinkNameIsDirectoryFs(fs, linkName)
    ensures !ok ==> !Spec.LinkNameIsDirectoryFs(fs, linkName)
  {
    match IOContract.ResolvePathForMetadataFields(fs, linkName, true)
    case Ok(resolved) =>
      assert ok;
      assert BenchWorld.FsContainsPath(fs, resolved);
    case Err(_) =>
      assert !ok;
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.LnCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else if |cmd.operands| == 0 {
    } else if !cmd.symbolic {
    } else if |cmd.operands| != 2 {
    } else {
      var dirOk, isDir, dirErr :|
        IOContract.IsDirectoryStrictContractFields(
          old(io.fs()), cmd.operands[1], true, dirOk, isDir, dirErr
        ) &&
        (if dirOk && isDir then
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
             exit == (if ok then 0 else 1));
      IsDirectoryProbeMatchesLinkNameFs(
        old(io.fs()), cmd.operands[1], dirOk, isDir, dirErr
      );
    }
  }
}
