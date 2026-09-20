include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "ChmodSchema.dfy"
include "ChmodSpec.dfy"

module ChmodCore {
  import BenchIO
  import IOContract
  import BenchWorld
  import Utf8 = Utf8Semantics
  import Schema = ChmodSchema
  import Spec = ChmodSpec

  function HelpTextCore(): BenchWorld.Bytes
  {
    Spec.HelpTextSpec()
  }

  function VersionTextCore(): BenchWorld.Bytes
  {
    Spec.VersionTextSpec()
  }

  function ErrnoTextCore(err: int): string
  {
    Spec.ErrnoTextSpec(err)
  }

  function MissingOperandMessageCore(cmd: Schema.ChmodCmd): BenchWorld.Bytes
  {
    Spec.MissingOperandMessageSpec(cmd)
  }

  function InvalidModeMessageCore(modeExpr: string): BenchWorld.Bytes
  {
    Spec.InvalidModeMessageSpec(modeExpr)
  }

  function ReferenceErrorMessageCore(path: string, err: string): BenchWorld.Bytes
  {
    Spec.ReferenceErrorMessageSpec(path, err)
  }

  function GettingNewAttributesMessageCore(path: string, err: string): BenchWorld.Bytes
  {
    Spec.GettingNewAttributesMessageSpec(path, err)
  }

  function CombineModeReferenceMessageCore(): BenchWorld.Bytes
  {
    Spec.CombineModeReferenceMessageSpec()
  }

  function UnsupportedRecursiveMessageCore(): BenchWorld.Bytes
  {
    Spec.UnsupportedRecursiveMessageSpec()
  }

  function UnsupportedMultiFileMessageCore(): BenchWorld.Bytes
  {
    Spec.UnsupportedMultiFileMessageSpec()
  }

  function ChangeErrorMessageCore(path: string, err: string): BenchWorld.Bytes
  {
    Spec.ChangeErrorMessageSpec(path, err)
  }

  function AccessErrorMessageCore(path: string, err: string): BenchWorld.Bytes
  {
    Spec.AccessErrorMessageSpec(path, err)
  }

  function DanglingSymlinkMessageCore(path: string): BenchWorld.Bytes
  {
    Spec.DanglingSymlinkMessageSpec(path)
  }

  function CannotDereferenceMessageCore(path: string, err: int): BenchWorld.Bytes
  {
    Spec.CannotDereferenceMessageSpec(path, err)
  }

  function NeitherChangedMessageCore(path: string): BenchWorld.Bytes
  {
    Spec.NeitherChangedMessageSpec(path)
  }

  function ChangedMessageCore(path: string, before: bv32, after: bv32): BenchWorld.Bytes
  {
    Spec.ChangedMessageSpec(path, before, after)
  }

  function FailedChangeMessageCore(
    path: string,
    before: bv32,
    desired: bv32
  ): BenchWorld.Bytes
  {
    Spec.FailedChangeMessageSpec(path, before, desired)
  }

  function RetainedMessageCore(path: string, mode: bv32): BenchWorld.Bytes
  {
    Spec.RetainedMessageSpec(path, mode)
  }

  function AccessFailureMessageCore(path: string): BenchWorld.Bytes
  {
    Spec.AccessFailureMessageSpec(path)
  }

  function SurpriseModeMessageCore(path: string, actual: bv32, naive: bv32): BenchWorld.Bytes
  {
    Spec.SurpriseModeMessageSpec(path, actual, naive)
  }

  function MakeAbsoluteCore(cwd: BenchWorld.Path, path: BenchWorld.Path): BenchWorld.Path
  {
    if path == "" then ""
    else if BenchWorld.IsAbsolutePath(path) then path
    else
      var absoluteCwd := BenchWorld.BuildPath(
                           true,
                           BenchWorld.PathSegments(cwd)
                         );
      BenchWorld.AppendPath(absoluteCwd, path)
  }

  function ShouldDereferenceCore(cmd: Schema.ChmodCmd): bool
  {
    cmd.dereferenceMode != 0
  }

  function CoreUsesPhysicalTopLevelMetadata(cmd: Schema.ChmodCmd): bool
  {
    !cmd.recursive && cmd.dereferenceMode == -1 && cmd.traversalMode == 0
  }

  function CoreUsesExplicitPhysicalDereference(cmd: Schema.ChmodCmd): bool
  {
    !cmd.recursive && cmd.dereferenceMode == 1 && cmd.traversalMode == 0
  }

  function CoreUsesFollowedTopLevelNoDereference(cmd: Schema.ChmodCmd): bool
  {
    !cmd.recursive && cmd.dereferenceMode == 0 && cmd.traversalMode != 0
  }

  function CoreIsDanglingSymlinkFailure(isSymlink: bool, err: int): bool
  {
    isSymlink && err == 2
  }

  function CorePathIsDanglingSymlinkFailure(
    fs: BenchWorld.FileSystem,
    actual: BenchWorld.Path,
    follow: bool,
    err: int
  ): bool
  {
    follow &&
    match IOContract.ResolvePathForMetadataFields(fs, actual, false)
    case Err(_) => false
    case Ok(resolved) =>
      BenchWorld.FsContainsPath(fs, resolved) &&
      CoreIsDanglingSymlinkFailure(
        match BenchWorld.FsNodeAt(fs, resolved)
        case Symlink(_, _, _, _) => true
        case _ => false,
        err
      )
  }

  function SupportedOctalModeCore(expr: string): bool
  {
    |expr| > 0 && BenchWorld.IsOctalDigit(expr[0]) &&
    BenchWorld.AllOctalDigits(expr, 0) && BenchWorld.OctalValue(expr, 0, 0) <= 4095
  }

  function OctalModeCore(expr: string): bv32
    requires SupportedOctalModeCore(expr)
  {
    BenchWorld.NormalizeMode(BenchWorld.ToBv32(BenchWorld.OctalValue(expr, 0, 0)))
  }

  const CORE_READ_MASK: bv32 := Schema.READ_MASK
  const CORE_WRITE_MASK: bv32 := Schema.WRITE_MASK
  const CORE_EXEC_MASK: bv32 := Schema.EXEC_MASK

  function CoreCopyExistingValue(value: bv32, current: bv32): bv32
  {
    var isolated := value & current;
    isolated |
    (if (isolated & CORE_READ_MASK) != 0 as bv32 then CORE_READ_MASK else 0 as bv32) |
    (if (isolated & CORE_WRITE_MASK) != 0 as bv32 then CORE_WRITE_MASK else 0 as bv32) |
    (if (isolated & CORE_EXEC_MASK) != 0 as bv32 then CORE_EXEC_MASK else 0 as bv32)
  }

  function CoreInvertModeBits(value: bv32): bv32
  {
    Schema.CHMOD_MODE_BITS ^ value
  }

  function CoreOmittedChangeBits(isDir: bool, mentioned: bv32): bv32
  {
    (if isDir then Schema.S_ISUID | Schema.S_ISGID else 0 as bv32) &
    CoreInvertModeBits(mentioned)
  }

  function CoreChangeAffectedMask(affected: bv32, umask: bv32): bv32
  {
    if affected != 0 as bv32 then affected else CoreInvertModeBits(umask)
  }

  function CoreChangeValue(current: bv32, isDir: bool, change: Schema.ModeChange): bv32
  {
    match change.flag
    case ModeCopyExisting => CoreCopyExistingValue(change.value, current)
    case ModeXIfAnyX =>
      if (current & CORE_EXEC_MASK) != 0 as bv32 || isDir then
        change.value | CORE_EXEC_MASK
      else
        change.value
    case ModeOrdinary => change.value
  }

  function CoreMaskedChangeValue(
    current: bv32,
    isDir: bool,
    umask: bv32,
    change: Schema.ModeChange
  ): bv32
  {
    CoreChangeValue(current, isDir, change) &
    CoreChangeAffectedMask(change.affected, umask) &
    CoreInvertModeBits(CoreOmittedChangeBits(isDir, change.mentioned))
  }

  function CorePreservedAffectedBits(affected: bv32): bv32
  {
    if affected != 0 as bv32 then CoreInvertModeBits(affected) else 0 as bv32
  }

  function CorePreservedChangeBits(isDir: bool, change: Schema.ModeChange): bv32
  {
    CorePreservedAffectedBits(change.affected) |
    CoreOmittedChangeBits(isDir, change.mentioned)
  }

  function CoreApplyChange(
    current: bv32,
    isDir: bool,
    umask: bv32,
    change: Schema.ModeChange
  ): bv32
  {
    var masked := CoreMaskedChangeValue(current, isDir, umask, change);
    if change.op == '=' then
      BenchWorld.NormalizeMode((current & CorePreservedChangeBits(isDir, change)) | masked)
    else if change.op == '+' then
      BenchWorld.NormalizeMode(current | masked)
    else
      BenchWorld.NormalizeMode(current & CoreInvertModeBits(masked))
  }

  function CoreModeAdjustFrom(
    changes: seq<Schema.ModeChange>,
    i: nat,
    current: bv32,
    isDir: bool,
    umask: bv32
  ): bv32
    requires i <= |changes|
    decreases |changes| - i
  {
    if i == |changes| then
      current
    else
      CoreModeAdjustFrom(
        changes,
        i + 1,
        CoreApplyChange(current, isDir, umask, changes[i]),
        isDir,
        umask
      )
  }

  function CoreModeAdjust(
    oldMode: bv32,
    isDir: bool,
    umask: bv32,
    changes: seq<Schema.ModeChange>
  ): bv32
  {
    CoreModeAdjustFrom(changes, 0, BenchWorld.NormalizeMode(oldMode), isDir, umask)
  }

  function CoreApplyModeExpr(expr: string, oldMode: bv32, isDir: bool, umask: bv32): bv32
  {
    var base := BenchWorld.NormalizeMode(oldMode);
    if |expr| == 0 then
      base
    else if BenchWorld.IsOctalDigit(expr[0]) then
      if BenchWorld.AllOctalDigits(expr, 0) then
        var raw := BenchWorld.OctalValue(expr, 0, 0);
        if raw > 4095 then
          base
        else
          var mode := BenchWorld.NormalizeMode(BenchWorld.ToBv32(raw));
          var mentioned :=
            if |expr| < 5 then
              (mode & (Schema.S_ISUID | Schema.S_ISGID)) | Schema.S_ISVTX | Schema.S_IRWXUGO
            else
              Schema.CHMOD_MODE_BITS;
          CoreModeAdjust(
            base,
            isDir,
            umask,
            [Schema.ModeChange('=', Schema.ModeOrdinary, Schema.CHMOD_MODE_BITS, mode, mentioned)]
          )
      else
        base
    else
      match Schema.ParseSymbolic(expr, 0)
      case Invalid => base
      case Parsed(changes, endIdx) =>
        if endIdx == |expr| then CoreModeAdjust(base, isDir, umask, changes) else base
  }

  datatype CoreModePlan =
    | CoreGeneralModePlan(expr: string, umask: bv32)
    | CoreReferenceModePlan(mode: bv32)

  datatype CorePathStatus =
    | CorePathChanged(before: bv32, after: bv32)
    | CorePathRetained(mode: bv32)
    | CorePathAccessFailed(err: int)
    | CorePathChangeFailed(before: bv32, desired: bv32, err: int)
    | CorePathSurprise(before: bv32, after: bv32, naive: bv32)

  datatype CorePathResult = CorePathResult(
    fs: BenchWorld.FileSystem,
    stdoutChunk: BenchWorld.Bytes,
    stderrChunk: BenchWorld.Bytes,
    ok: bool,
    status: CorePathStatus
  )

  datatype CoreBatchResult = CoreBatchResult(
    fs: BenchWorld.FileSystem,
    stdoutChunk: BenchWorld.Bytes,
    stderrChunk: BenchWorld.Bytes,
    allOk: bool
  )

  function CoreNodeIsDirectory(node: BenchWorld.FsNode): bool
  {
    match node
    case Directory(_, _, _) => true
    case _ => false
  }

  function CorePlannedMode(plan: CoreModePlan, before: bv32, isDir: bool): bv32
  {
    match plan
    case CoreGeneralModePlan(expr, umask) =>
      CoreApplyModeExpr(expr, before, isDir, umask)
    case CoreReferenceModePlan(mode) => BenchWorld.NormalizeMode(mode)
  }

  function CoreSuccessStdout(
    cmd: Schema.ChmodCmd,
    path: string,
    before: bv32,
    after: bv32
  ): BenchWorld.Bytes
  {
    if cmd.verbose then
      if before == after then RetainedMessageCore(path, after)
      else ChangedMessageCore(path, before, after)
    else if cmd.changes && before != after then
      ChangedMessageCore(path, before, after)
    else
      []
  }

  function CoreNaiveMode(plan: CoreModePlan, before: bv32, isDir: bool): bv32
  {
    match plan
    case CoreGeneralModePlan(expr, _) => CoreApplyModeExpr(expr, before, isDir, 0 as bv32)
    case CoreReferenceModePlan(mode) => BenchWorld.NormalizeMode(mode)
  }

  function CoreDiagnoseSurprise(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    before: bv32,
    after: bv32,
    isDir: bool
  ): bool
  {
    var naive := CoreNaiveMode(plan, before, isDir);
    cmd.diagnoseSurprises && (after & CoreInvertModeBits(naive)) != 0 as bv32
  }

  function CorePostChangeLookupNeeded(
    cmd: Schema.ChmodCmd,
    after: bv32
  ): bool
  {
    (cmd.verbose || cmd.changes) &&
    (after & Schema.SPECIAL_BITS) != 0 as bv32
  }

  function CoreSuccessfulChangeResult(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    path: string,
    actual: BenchWorld.Path,
    follow: bool,
    before: bv32,
    after: bv32,
    isDir: bool,
    fs: BenchWorld.FileSystem
  ): CorePathResult
  {
    if CorePostChangeLookupNeeded(cmd, after) then
      match IOContract.ResolvePathForMetadataFields(fs, actual, follow)
      case Err(_) =>
        var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
        var surprise := CoreDiagnoseSurprise(cmd, plan, before, after, isDir);
        var naive := CoreNaiveMode(plan, before, isDir);
        CorePathResult(
          fs,
          if cmd.verbose then RetainedMessageCore(path, after) else [],
          (if cmd.silent then []
           else GettingNewAttributesMessageCore(path, ErrnoTextCore(err))) +
          (if surprise then SurpriseModeMessageCore(path, after, naive) else []),
          !surprise,
          CorePathRetained(after)
        )
      case Ok(target) =>
        if !BenchWorld.FsContainsPath(fs, target) then
          var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
          var surprise := CoreDiagnoseSurprise(cmd, plan, before, after, isDir);
          var naive := CoreNaiveMode(plan, before, isDir);
          CorePathResult(
            fs,
            if cmd.verbose then RetainedMessageCore(path, after) else [],
            (if cmd.silent then []
             else GettingNewAttributesMessageCore(path, ErrnoTextCore(err))) +
            (if surprise then SurpriseModeMessageCore(path, after, naive) else []),
            !surprise,
            CorePathRetained(after)
          )
        else
          var observed := BenchWorld.NodeMode(BenchWorld.FsNodeAt(fs, target));
          var surprise := CoreDiagnoseSurprise(cmd, plan, before, observed, isDir);
          var naive := CoreNaiveMode(plan, before, isDir);
          CorePathResult(
            fs,
            CoreSuccessStdout(cmd, path, before, observed),
            if surprise then SurpriseModeMessageCore(path, observed, naive) else [],
            !surprise,
            if surprise then CorePathSurprise(before, observed, naive)
            else if before == observed then CorePathRetained(observed)
            else CorePathChanged(before, observed)
          )
    else
      var surprise := CoreDiagnoseSurprise(cmd, plan, before, after, isDir);
      var naive := CoreNaiveMode(plan, before, isDir);
      CorePathResult(
        fs,
        CoreSuccessStdout(cmd, path, before, after),
        if surprise then SurpriseModeMessageCore(path, after, naive) else [],
        !surprise,
        if surprise then CorePathSurprise(before, after, naive)
        else if before == after then CorePathRetained(after)
        else CorePathChanged(before, after)
      )
  }

  method {:isolate_assertions} FinishSuccessfulChangeCore(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    path: string,
    actual: BenchWorld.Path,
    follow: bool,
    before: bv32,
    requestedAfter: bv32,
    isDir: bool,
    io: BenchIO.IO
  ) returns (ok: bool)
    modifies io.stdoutRegion, io.stderrRegion
    ensures var result := CoreSuccessfulChangeResult(
                            cmd,
                            plan,
                            path,
                            actual,
                            follow,
                            before,
                            requestedAfter,
                            isDir,
                            old(io.fs())
                          );
            io.stdout() == old(io.stdout()) + result.stdoutChunk &&
            io.stderr() == old(io.stderr()) + result.stderrChunk &&
            ok == result.ok
  {
    var after := requestedAfter;
    if CorePostChangeLookupNeeded(cmd, requestedAfter) {
      var postOk, rawModeStatus1, postErr := io.GetFileStatus(actual, follow);
      IOContract.FileStatusImpliesMode(io.fs(), actual, follow, postOk, rawModeStatus1, postErr);
      var observed := rawModeStatus1.mode;
      if !postOk {
        if !cmd.silent {
          io.AppendStderr(
            GettingNewAttributesMessageCore(path, ErrnoTextCore(postErr))
          );
        }
        if cmd.verbose {
          io.AppendStdout(RetainedMessageCore(path, requestedAfter));
        }
        var failedNaive := CoreNaiveMode(plan, before, isDir);
        var failedSurprise := CoreDiagnoseSurprise(
          cmd, plan, before, requestedAfter, isDir
        );
        if failedSurprise {
          io.AppendStderr(
            SurpriseModeMessageCore(path, requestedAfter, failedNaive)
          );
        }
        ok := !failedSurprise;
        reveal IOContract.GetFileModeContractFields;
        return;
      }
      after := observed;
    }
    var out := CoreSuccessStdout(cmd, path, before, after);
    if |out| > 0 {
      io.AppendStdout(out);
    }
    var naive := CoreNaiveMode(plan, before, isDir);
    var surprise := CoreDiagnoseSurprise(cmd, plan, before, after, isDir);
    if surprise {
      io.AppendStderr(SurpriseModeMessageCore(path, after, naive));
    }
    ok := !surprise;
    reveal IOContract.GetFileModeContractFields;
  }

  function CoreModeSetFs(
    fs: BenchWorld.FileSystem,
    follow: bool,
    target: BenchWorld.Path,
    desired: bv32,
    now: int
  ): BenchWorld.FileSystem
    requires BenchWorld.FsContainsPath(fs, target)
  {
    if CoreModeSetSuppressed(fs, target, follow) then
      fs
    else
      BenchWorld.FsSetPath(
        fs,
        target,
        BenchWorld.WithNodeChangeTime(
          BenchWorld.WithNodeMode(BenchWorld.FsNodeAt(fs, target), desired),
          now,
          0
        )
      )
  }

  function CoreModeSetSuppressed(
    fs: BenchWorld.FileSystem,
    target: BenchWorld.Path,
    follow: bool
  ): bool
    requires BenchWorld.FsContainsPath(fs, target)
  {
    !follow &&
    match BenchWorld.FsNodeAt(fs, target)
    case Symlink(_, _, _, _) => true
    case _ => false
  }

  function CoreNoDereferenceSymlink(
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    follow: bool
  ): bool
  {
    !follow &&
    match IOContract.ResolvePathForMetadataFields(fs, path, false)
    case Err(_) => false
    case Ok(target) =>
      BenchWorld.FsContainsPath(fs, target) &&
      match BenchWorld.FsNodeAt(fs, target)
      case Symlink(_, _, _, _) => true
      case _ => false
  }

  function CorePathAccessFailureResult(
    cmd: Schema.ChmodCmd,
    fs: BenchWorld.FileSystem,
    path: string,
    actual: BenchWorld.Path,
    follow: bool,
    err: int
  ): CorePathResult
  {
    CorePathResult(
      fs,
      if cmd.verbose then AccessFailureMessageCore(path) else [],
      if cmd.silent then []
      else if CoreUsesExplicitPhysicalDereference(cmd) &&
              CoreNoDereferenceSymlink(fs, actual, false) then
        CannotDereferenceMessageCore(path, err)
      else if CorePathIsDanglingSymlinkFailure(fs, actual, follow, err) then
        DanglingSymlinkMessageCore(path)
      else AccessErrorMessageCore(path, ErrnoTextCore(err)),
      false,
      CorePathAccessFailed(err)
    )
  }

  function CorePathStep(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    cwd: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    path: string,
    now: int
  ): CorePathResult
  {
    var actual := MakeAbsoluteCore(cwd, path);
    var follow := ShouldDereferenceCore(cmd);
    if CoreUsesPhysicalTopLevelMetadata(cmd) then
      match IOContract.ResolvePathForMetadataFields(fs, actual, false)
      case Err(_) =>
        var err := IOContract.MetadataFailureErrFields(fs, actual, false);
        CorePathAccessFailureResult(cmd, fs, path, actual, false, err)
      case Ok(metadataTarget) =>
        if !BenchWorld.FsContainsPath(fs, metadataTarget) then
          var err := IOContract.MetadataFailureErrFields(fs, actual, false);
          CorePathAccessFailureResult(cmd, fs, path, actual, false, err)
        else
          var node := BenchWorld.FsNodeAt(fs, metadataTarget);
          var before := BenchWorld.NodeMode(node);
          var isDir := CoreNodeIsDirectory(node);
          var desired := CorePlannedMode(plan, before, isDir);
          match IOContract.ResolvePathForMetadataFields(fs, actual, true)
          case Err(_) =>
            var err := IOContract.MetadataFailureErrFields(fs, actual, true);
            CorePathResult(
              fs,
              if cmd.verbose then FailedChangeMessageCore(path, before, desired) else [],
              if cmd.silent then []
              else ChangeErrorMessageCore(path, ErrnoTextCore(err)),
              false,
              CorePathChangeFailed(before, desired, err)
            )
          case Ok(changeTarget) =>
            if !BenchWorld.FsContainsPath(fs, changeTarget) then
              var err := IOContract.MetadataFailureErrFields(fs, actual, true);
              CorePathResult(
                fs,
                if cmd.verbose then FailedChangeMessageCore(path, before, desired) else [],
                if cmd.silent then []
                else ChangeErrorMessageCore(path, ErrnoTextCore(err)),
                false,
                CorePathChangeFailed(before, desired, err)
              )
            else
              var fs2 := CoreModeSetFs(
                fs, true, changeTarget, desired, now
              );
              var after := BenchWorld.NormalizeMode(desired);
              CoreSuccessfulChangeResult(
                cmd, plan, path, actual, true, before, after, isDir, fs2
              )
    else
      match IOContract.ResolvePathForMetadataFields(fs, actual, follow)
      case Err(_) =>
        var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
        CorePathAccessFailureResult(cmd, fs, path, actual, follow, err)
      case Ok(target) =>
        if !BenchWorld.FsContainsPath(fs, target) then
          var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
          CorePathAccessFailureResult(cmd, fs, path, actual, follow, err)
        else
          var before := BenchWorld.NodeMode(BenchWorld.FsNodeAt(fs, target));
          if CoreNoDereferenceSymlink(fs, actual, follow) then
            if CoreUsesFollowedTopLevelNoDereference(cmd) then
              var followed := IOContract.ResolvePathForMetadataFields(fs, actual, true);
              var followedOk :=
                match followed
                case Err(_) => false
                case Ok(followedTarget) =>
                  BenchWorld.FsContainsPath(fs, followedTarget);
              var err := IOContract.MetadataFailureErrFields(fs, actual, true);
              if !followedOk && err != 2 then
                CorePathAccessFailureResult(cmd, fs, path, actual, true, err)
              else
                CorePathResult(
                  fs,
                  if cmd.verbose then NeitherChangedMessageCore(path) else [],
                  [],
                  true,
                  CorePathRetained(before)
                )
            else
              CorePathResult(
                fs,
                if cmd.verbose then NeitherChangedMessageCore(path) else [],
                [],
                true,
                CorePathRetained(before)
              )
          else
            var isDir := CoreNodeIsDirectory(BenchWorld.FsNodeAt(fs, target));
            var desired := CorePlannedMode(plan, before, isDir);
            var fs2 := CoreModeSetFs(fs, follow, target, desired, now);
            var after :=
              if CoreModeSetSuppressed(fs, target, follow) then before
              else BenchWorld.NormalizeMode(desired);
            CoreSuccessfulChangeResult(
              cmd, plan, path, actual, follow, before, after, isDir, fs2
            )
  }

  function CoreRunFilesFrom(
    files: seq<string>,
    i: nat,
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    cwd: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    now: int
  ): CoreBatchResult
    requires i <= |files|
    decreases |files| - i
  {
    if i == |files| then
      CoreBatchResult(fs, [], [], true)
    else
      var step := CorePathStep(cmd, plan, cwd, fs, files[i], now);
      var rest := CoreRunFilesFrom(
        files, i + 1, cmd, plan, cwd, step.fs, now
      );
      CoreBatchResult(
        rest.fs,
        step.stdoutChunk + rest.stdoutChunk,
        step.stderrChunk + rest.stderrChunk,
        step.ok && rest.allOk
      )
  }

  function CoreRunFiles(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    cwd: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    now: int
  ): CoreBatchResult
  {
    CoreRunFilesFrom(cmd.files, 0, cmd, plan, cwd, fs, now)
  }

  lemma AppendAssociative<T>(a: seq<T>, b: seq<T>, c: seq<T>)
    ensures (a + b) + c == a + (b + c)
  {
  }

  ghost predicate CoreBatchOutcome(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    fs0: BenchWorld.FileSystem,
    cwd0: BenchWorld.Path,
    fs2: BenchWorld.FileSystem,
    stdout0: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr0: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int,
    now: int
  )
  {
    var result := CoreRunFiles(cmd, plan, cwd0, fs0, now);
    fs2 == result.fs &&
    stdout2 == stdout0 + result.stdoutChunk &&
    stderr2 == stderr0 + result.stderrChunk &&
    exit == (if result.allOk then 0 else 1)
  }

  ghost predicate CoreReferenceFailure(
    cmd: Schema.ChmodCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path
  )
  {
    exists mode: bv32, err: int ::
      IOContract.GetFileModeContractFields(
        fs,
        MakeAbsoluteCore(cwd, cmd.referenceFile),
        true,
        false,
        mode,
        err
      )
  }

  ghost predicate CoreReferenceFailureOutcome(
    cmd: Schema.ChmodCmd,
    fs0: BenchWorld.FileSystem,
    cwd0: BenchWorld.Path,
    fs2: BenchWorld.FileSystem,
    stdout0: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr0: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int
  )
  {
    exists mode: bv32, err: int ::
      IOContract.GetFileModeContractFields(
        fs0,
        MakeAbsoluteCore(cwd0, cmd.referenceFile),
        true,
        false,
        mode,
        err
      ) &&
      fs2 == fs0 && stdout2 == stdout0 &&
      stderr2 == stderr0 + ReferenceErrorMessageCore(
        cmd.referenceFile,
        ErrnoTextCore(err)
      ) && exit == 1
  }

  ghost predicate CoreReferenceBatchOutcome(
    cmd: Schema.ChmodCmd,
    fs0: BenchWorld.FileSystem,
    cwd0: BenchWorld.Path,
    fs2: BenchWorld.FileSystem,
    stdout0: BenchWorld.Bytes,
    stdout2: BenchWorld.Bytes,
    stderr0: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    exit: int,
    now: int
  )
  {
    exists refMode: bv32 ::
      IOContract.GetFileModeContractFields(
        fs0,
        MakeAbsoluteCore(cwd0, cmd.referenceFile),
        true,
        true,
        refMode,
        0
      ) &&
      CoreBatchOutcome(
        cmd,
        CoreReferenceModePlan(refMode),
        fs0,
        cwd0,
        fs2,
        stdout0,
        stdout2,
        stderr0,
        stderr2,
        exit,
        now
      )
  }

  method {:isolate_assertions} RunOnePathCore(
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    cwd: BenchWorld.Path,
    path: string,
    io: BenchIO.IO
  ) returns (ok: bool)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures var result := CorePathStep(
                            cmd, plan, cwd, old(io.fs()), path, old(io.now())
                          );
            io.fs() == result.fs &&
            io.stdout() == old(io.stdout()) + result.stdoutChunk &&
            io.stderr() == old(io.stderr()) + result.stderrChunk &&
            ok == result.ok
  {
    ghost var fs0 := io.fs();
    ghost var now0 := io.now();
    ghost var stdout0 := io.stdout();
    ghost var stderr0 := io.stderr();
    var actual := MakeAbsoluteCore(cwd, path);
    var follow := ShouldDereferenceCore(cmd);
    var metadataFollow := if CoreUsesPhysicalTopLevelMetadata(cmd) then false else follow;
    var rawMetadataOk2, rawMetadataStatus2, rawMetadataErr2 := io.GetFileStatus(actual, false);
    IOContract.FileStatusImpliesMetadata(io.fs(), actual, false, rawMetadataOk2, rawMetadataStatus2, rawMetadataErr2);
    var linkOk := rawMetadataOk2;
    var isLink := rawMetadataStatus2.kind == BenchWorld.SymlinkKind;
    assert (linkOk && isLink) ==
           CoreNoDereferenceSymlink(fs0, actual, false) by {
      reveal IOContract.IsSymlinkContractFields;
      reveal CoreNoDereferenceSymlink;
    }
    assert (!follow && linkOk && isLink) ==
           CoreNoDereferenceSymlink(fs0, actual, follow) by {
      reveal IOContract.IsSymlinkContractFields;
      reveal CoreNoDereferenceSymlink;
    }
    if !follow && linkOk && isLink {
      if CoreUsesFollowedTopLevelNoDereference(cmd) {
        var followedOk, rawModeStatus2, followedErr := io.GetFileStatus(actual, true);
        IOContract.FileStatusImpliesMode(io.fs(), actual, true, followedOk, rawModeStatus2, followedErr);
        if !followedOk && followedErr != 2 {
          if !cmd.silent {
            io.AppendStderr(AccessErrorMessageCore(path, ErrnoTextCore(followedErr)));
          }
          if cmd.verbose {
            io.AppendStdout(AccessFailureMessageCore(path));
          }
          ok := false;
          return;
        }
      }
      if cmd.verbose {
        io.AppendStdout(NeitherChangedMessageCore(path));
      }
      ok := true;
      return;
    }
    var gotMode, rawModeStatus3, getErr := io.GetFileStatus(actual, metadataFollow);
    IOContract.FileStatusImpliesMode(io.fs(), actual, metadataFollow, gotMode, rawModeStatus3, getErr);
    var before := rawModeStatus3.mode;
    if !gotMode {
      assert CoreIsDanglingSymlinkFailure(linkOk && isLink, getErr) ==
             CorePathIsDanglingSymlinkFailure(fs0, actual, metadataFollow, getErr) by {
        reveal CoreIsDanglingSymlinkFailure;
        reveal CorePathIsDanglingSymlinkFailure;
        reveal IOContract.GetFileModeContractFields;
        reveal IOContract.IsSymlinkContractFields;
      }
      if !cmd.silent {
        if CoreUsesExplicitPhysicalDereference(cmd) && linkOk && isLink {
          io.AppendStderr(CannotDereferenceMessageCore(path, getErr));
        } else if CoreIsDanglingSymlinkFailure(linkOk && isLink, getErr) {
          io.AppendStderr(DanglingSymlinkMessageCore(path));
        } else {
          io.AppendStderr(AccessErrorMessageCore(path, ErrnoTextCore(getErr)));
        }
      }
      if cmd.verbose {
        io.AppendStdout(AccessFailureMessageCore(path));
      }
      ok := false;
      return;
    }

    var rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1 := io.GetFileStatus(actual, metadataFollow);
    IOContract.FileStatusImpliesMetadata(io.fs(), actual, metadataFollow, rawMetadataOk1, rawMetadataStatus1, rawMetadataErr1);
    var dirOk := rawMetadataOk1;
    var isDir := rawMetadataStatus1.kind == BenchWorld.DirectoryKind;
    var dirErr := rawMetadataErr1;
    if !dirOk {
      if !cmd.silent {
        io.AppendStderr(AccessErrorMessageCore(path, ErrnoTextCore(dirErr)));
      }
      if cmd.verbose {
        io.AppendStdout(AccessFailureMessageCore(path));
      }
      ok := false;
      return;
    }

    var desired := CorePlannedMode(plan, before, isDir);
    var setOk, setErr := io.SetFileMode(actual, follow, desired);
    if !setOk {
      if cmd.verbose {
        io.AppendStdout(FailedChangeMessageCore(path, before, desired));
      }
      if !cmd.silent {
        io.AppendStderr(ChangeErrorMessageCore(path, ErrnoTextCore(setErr)));
      }
      ok := false;
      return;
    }
    assert {:split_here} true;
    var requestedAfter := BenchWorld.NormalizeMode(desired);
    assert CorePathStep(cmd, plan, cwd, fs0, path, now0) ==
           CoreSuccessfulChangeResult(
             cmd,
             plan,
             path,
             actual,
             follow,
             before,
             requestedAfter,
             isDir,
             io.fs()
           ) by {
      match IOContract.ResolvePathForMetadataFields(fs0, actual, metadataFollow)
      case Err(_) =>
      case Ok(metadataTarget) =>
    assert BenchWorld.FsContainsPath(fs0, metadataTarget);
    assert before == BenchWorld.NodeMode(BenchWorld.FsNodeAt(fs0, metadataTarget));
    assert isDir == CoreNodeIsDirectory(BenchWorld.FsNodeAt(fs0, metadataTarget));
    match IOContract.ResolvePathForMetadataFields(fs0, actual, follow)
    case Err(_) =>
    case Ok(changeTarget) =>
    assert BenchWorld.FsContainsPath(fs0, changeTarget);
    assert !CoreModeSetSuppressed(fs0, changeTarget, follow) by {
      assert !CoreNoDereferenceSymlink(fs0, actual, follow);
      reveal CoreNoDereferenceSymlink;
      reveal CoreModeSetSuppressed;
    }
    assert io.fs() == CoreModeSetFs(
                        fs0, follow, changeTarget, desired, now0
                      );
    }
    ok := FinishSuccessfulChangeCore(
      cmd,
      plan,
      path,
      actual,
      follow,
      before,
      requestedAfter,
      isDir,
      io
    );
  }

  method {:isolate_assertions} RunFilesFromCore(
    files: seq<string>,
    i: nat,
    cmd: Schema.ChmodCmd,
    plan: CoreModePlan,
    cwd: BenchWorld.Path,
    io: BenchIO.IO
  ) returns (allOk: bool)
    requires i <= |files|
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures var result := CoreRunFilesFrom(
                            files, i, cmd, plan, cwd, old(io.fs()), old(io.now())
                          );
            io.fs() == result.fs &&
            io.stdout() == old(io.stdout()) + result.stdoutChunk &&
            io.stderr() == old(io.stderr()) + result.stderrChunk &&
            allOk == result.allOk
    decreases |files| - i
  {
    if i == |files| {
      allOk := true;
      return;
    }
    ghost var fs0 := io.fs();
    ghost var now0 := io.now();
    ghost var stdout0 := io.stdout();
    ghost var stderr0 := io.stderr();
    var stepOk := RunOnePathCore(cmd, plan, cwd, files[i], io);
    ghost var step := CorePathStep(cmd, plan, cwd, fs0, files[i], now0);
    assert io.fs() == step.fs;
    assert io.stdout() == stdout0 + step.stdoutChunk;
    assert io.stderr() == stderr0 + step.stderrChunk;
    assert {:split_here} true;
    var restOk := RunFilesFromCore(files, i + 1, cmd, plan, cwd, io);
    ghost var rest := CoreRunFilesFrom(
      files, i + 1, cmd, plan, cwd, step.fs, now0
    );
    AppendAssociative(
      stdout0, step.stdoutChunk, rest.stdoutChunk
    );
    AppendAssociative(
      stderr0, step.stderrChunk, rest.stderrChunk
    );
    assert {:split_here} true;
    allOk := stepOk && restOk;
  }

  // Kept independent from the specification's normalized external-text domain.
  predicate CoreExternalDomain(raw: Schema.ChmodCmdRaw)
  {
    var cmd := Schema.Command(raw);
    Utf8.ValidExternalText(cmd.modeExpr) &&
    Utf8.ValidExternalText(cmd.referenceFile) &&
    forall i :: 0 <= i < |cmd.files| ==>
                  Utf8.ValidExternalText(cmd.files[i])
  }

  twostate predicate CoreSummary(raw: Schema.ChmodCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) + HelpTextCore() &&
      io.stderr() == old(io.stderr()) && exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) + VersionTextCore() &&
      io.stderr() == old(io.stderr()) && exit == 0
    else if cmd.seenReference && cmd.diagnoseSurprises then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + CombineModeReferenceMessageCore() && exit == 1
    else if |cmd.files| == 0 then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MissingOperandMessageCore(cmd) && exit == 1
    else if cmd.seenReference &&
            CoreReferenceFailure(cmd, old(io.fs()), old(io.cwd())) then
      CoreReferenceFailureOutcome(
        cmd, old(io.fs()), old(io.cwd()), io.fs(),
        old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(), exit
      )
    else if !cmd.seenReference && !Schema.IsValidModeExpr(cmd.modeExpr) then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + InvalidModeMessageCore(cmd.modeExpr) && exit == 1
    else if cmd.recursive then
      io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + UnsupportedRecursiveMessageCore() && exit == 1
    else if cmd.seenReference then
      CoreReferenceBatchOutcome(
        cmd, old(io.fs()), old(io.cwd()), io.fs(),
        old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(), exit,
        old(io.now())
      )
    else
      CoreBatchOutcome(
        cmd,
        CoreGeneralModePlan(
          cmd.modeExpr,
          IOContract.GetUmaskResultFields(old(io.props()))
        ),
        old(io.fs()),
        old(io.cwd()),
        io.fs(),
        old(io.stdout()),
        io.stdout(),
        old(io.stderr()),
        io.stderr(),
        exit,
        old(io.now())
      )
  }

  method RunCore(raw: Schema.ChmodCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    ghost var preFs := io.fs();
    ghost var preCwd := io.cwd();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    ghost var preNow := io.now();
    var cmd := Schema.Command(raw);

    if cmd.mode == Schema.ModeHelp {
      io.AppendStdout(HelpTextCore());
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }
    if cmd.mode == Schema.ModeVersion {
      io.AppendStdout(VersionTextCore());
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }
    if cmd.seenReference && cmd.diagnoseSurprises {
      io.AppendStderr(CombineModeReferenceMessageCore());
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }
    if |cmd.files| == 0 {
      io.AppendStderr(MissingOperandMessageCore(cmd));
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }
    var cwd := io.GetCwd();
    assert cwd == preCwd;
    var plan := CoreGeneralModePlan(cmd.modeExpr, 0 as bv32);
    if cmd.seenReference {
      var refActual := MakeAbsoluteCore(cwd, cmd.referenceFile);
      var refOk, rawModeStatus4, refErr := io.GetFileStatus(refActual, true);
      IOContract.FileStatusImpliesMode(io.fs(), refActual, true, refOk, rawModeStatus4, refErr);
      var refMode := rawModeStatus4.mode;
      if !refOk {
        io.AppendStderr(ReferenceErrorMessageCore(cmd.referenceFile, ErrnoTextCore(refErr)));
        exit := 1;
        assert CoreReferenceFailure(cmd, preFs, preCwd);
        assert CoreReferenceFailureOutcome(
            cmd, preFs, preCwd, io.fs(),
            preStdout, io.stdout(), preStderr, io.stderr(), exit
          );
        assert CoreSummary(raw, io, exit);
        return;
      }
      plan := CoreReferenceModePlan(refMode);
    }

    if !cmd.seenReference && !Schema.IsValidModeExpr(cmd.modeExpr) {
      io.AppendStderr(InvalidModeMessageCore(cmd.modeExpr));
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }
    if cmd.recursive {
      io.AppendStderr(UnsupportedRecursiveMessageCore());
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }
    if !cmd.seenReference {
      var umask := io.GetUmask();
      plan := CoreGeneralModePlan(cmd.modeExpr, umask);
    }

    var allOk := RunFilesFromCore(cmd.files, 0, cmd, plan, cwd, io);
    exit := if allOk then 0 else 1;
    if cmd.seenReference {
      assert CoreReferenceBatchOutcome(
          cmd, preFs, preCwd, io.fs(),
          preStdout, io.stdout(), preStderr, io.stderr(), exit, preNow
        );
    } else {
      assert CoreBatchOutcome(
          cmd,
          CoreGeneralModePlan(cmd.modeExpr, IOContract.GetUmaskResultFields(io.props())),
          preFs,
          preCwd,
          io.fs(),
          preStdout,
          io.stdout(),
          preStderr,
          io.stderr(),
          exit,
          preNow
        );
    }
    assert CoreSummary(raw, io, exit);
  }
}
