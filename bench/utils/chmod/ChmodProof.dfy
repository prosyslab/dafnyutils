include "../../core/World.dfy"
include "ChmodSchema.dfy"
include "ChmodCore.dfy"
include "ChmodSpec.dfy"

module ChmodProof {
  import BW = BenchWorld
  import BenchIO
  import IOC = IOContract
  import Schema = ChmodSchema
  import Core = ChmodCore
  import Spec = ChmodSpec

  lemma BridgeHelpText()
    ensures Core.HelpTextCore() == Spec.HelpTextSpec()
  {
  }

  lemma BridgeVersionText()
    ensures Core.VersionTextCore() == Spec.VersionTextSpec()
  {
  }

  lemma BridgeErrnoText(err: int)
    ensures Core.ErrnoTextCore(err) == Spec.ErrnoTextSpec(err)
  {
  }

  lemma BridgeMissingOperandMessage(cmd: Schema.ChmodCmd)
    ensures Core.MissingOperandMessageCore(cmd) == Spec.MissingOperandMessageSpec(cmd)
  {
  }

  lemma BridgeInvalidModeMessage(expr: string)
    ensures Core.InvalidModeMessageCore(expr) == Spec.InvalidModeMessageSpec(expr)
  {
  }

  lemma BridgeReferenceErrorMessage(path: string, err: int)
    ensures Core.ReferenceErrorMessageCore(path, Core.ErrnoTextCore(err)) ==
            Spec.ReferenceErrorMessageSpec(path, Spec.ErrnoTextSpec(err))
  {
    BridgeErrnoText(err);
  }

  lemma BridgeGettingNewAttributesMessage(path: string, err: int)
    ensures Core.GettingNewAttributesMessageCore(
              path, Core.ErrnoTextCore(err)
            ) == Spec.GettingNewAttributesMessageSpec(
                   path, Spec.ErrnoTextSpec(err)
                 )
  {
    BridgeErrnoText(err);
  }

  lemma BridgeCombineModeReferenceMessage()
    ensures Core.CombineModeReferenceMessageCore() == Spec.CombineModeReferenceMessageSpec()
  {
  }

  lemma BridgeUnsupportedRecursiveMessage()
    ensures Core.UnsupportedRecursiveMessageCore() == Spec.UnsupportedRecursiveMessageSpec()
  {
  }

  lemma BridgeUnsupportedMultiFileMessage()
    ensures Core.UnsupportedMultiFileMessageCore() == Spec.UnsupportedMultiFileMessageSpec()
  {
  }

  lemma BridgeChangeErrorMessage(path: string, err: int)
    ensures Core.ChangeErrorMessageCore(path, Core.ErrnoTextCore(err)) ==
            Spec.ChangeErrorMessageSpec(path, Spec.ErrnoTextSpec(err))
  {
    BridgeErrnoText(err);
  }

  lemma BridgeAccessErrorMessage(path: string, err: int)
    ensures Core.AccessErrorMessageCore(path, Core.ErrnoTextCore(err)) ==
            Spec.AccessErrorMessageSpec(path, Spec.ErrnoTextSpec(err))
  {
    BridgeErrnoText(err);
  }

  lemma BridgeDanglingSymlinkMessage(path: string)
    ensures Core.DanglingSymlinkMessageCore(path) ==
            Spec.DanglingSymlinkMessageSpec(path)
  {
  }

  lemma BridgeCannotDereferenceMessage(path: string, err: int)
    ensures Core.CannotDereferenceMessageCore(path, err) ==
            Spec.CannotDereferenceMessageSpec(path, err)
  {
    BridgeErrnoText(err);
  }

  lemma BridgeNeitherChangedMessage(path: string)
    ensures Core.NeitherChangedMessageCore(path) ==
            Spec.NeitherChangedMessageSpec(path)
  {
  }

  lemma BridgeChangedMessage(path: string, before: bv32, after: bv32)
    ensures Core.ChangedMessageCore(path, before, after) ==
            Spec.ChangedMessageSpec(path, before, after)
  {
  }

  lemma BridgeFailedChangeMessage(path: string, before: bv32, desired: bv32)
    ensures Core.FailedChangeMessageCore(path, before, desired) ==
            Spec.FailedChangeMessageSpec(path, before, desired)
  {
  }

  lemma BridgeRetainedMessage(path: string, mode: bv32)
    ensures Core.RetainedMessageCore(path, mode) ==
            Spec.RetainedMessageSpec(path, mode)
  {
  }

  lemma BridgeAccessFailureMessage(path: string)
    ensures Core.AccessFailureMessageCore(path) == Spec.AccessFailureMessageSpec(path)
  {
  }

  lemma BridgeSurpriseModeMessage(path: string, actual: bv32, naive: bv32)
    ensures Core.SurpriseModeMessageCore(path, actual, naive) ==
            Spec.SurpriseModeMessageSpec(path, actual, naive)
  {
  }

  lemma BridgeMakeAbsolute(cwd: BW.Path, path: BW.Path)
    ensures Core.MakeAbsoluteCore(cwd, path) == Spec.MakeAbsolute(cwd, path)
  {
  }

  lemma BridgeShouldDereference(cmd: Schema.ChmodCmd)
    ensures Core.ShouldDereferenceCore(cmd) == Spec.ShouldDereference(cmd)
  {
  }

  lemma BridgeUsesPhysicalTopLevelMetadata(cmd: Schema.ChmodCmd)
    ensures Core.CoreUsesPhysicalTopLevelMetadata(cmd) ==
            Spec.SpecUsesPhysicalTopLevelMetadata(cmd)
  {
  }

  lemma BridgeUsesExplicitPhysicalDereference(cmd: Schema.ChmodCmd)
    ensures Core.CoreUsesExplicitPhysicalDereference(cmd) ==
            Spec.SpecUsesExplicitPhysicalDereference(cmd)
  {
  }

  lemma BridgeUsesFollowedTopLevelNoDereference(cmd: Schema.ChmodCmd)
    ensures Core.CoreUsesFollowedTopLevelNoDereference(cmd) ==
            Spec.SpecUsesFollowedTopLevelNoDereference(cmd)
  {
  }

  lemma BridgeIsDanglingSymlinkFailure(isSymlink: bool, err: int)
    ensures Core.CoreIsDanglingSymlinkFailure(isSymlink, err) ==
            Spec.SpecIsDanglingSymlinkFailure(isSymlink, err)
  {
  }

  lemma BridgePathIsDanglingSymlinkFailure(
    fs: BW.FileSystem,
    actual: BW.Path,
    follow: bool,
    err: int
  )
    ensures Core.CorePathIsDanglingSymlinkFailure(fs, actual, follow, err) ==
            Spec.SpecPathIsDanglingSymlinkFailure(fs, actual, follow, err)
  {
    if follow {
      match IOC.ResolvePathForMetadataFields(fs, actual, false)
      case Err(_) =>
      case Ok(resolved) =>
        if BW.FsContainsPath(fs, resolved) {
          match BW.FsNodeAt(fs, resolved)
          case Symlink(_, _, _, _) => BridgeIsDanglingSymlinkFailure(true, err);
          case _ => BridgeIsDanglingSymlinkFailure(false, err);
        }
    }
  }

  lemma BridgeSupportedOctalMode(expr: string)
    ensures Core.SupportedOctalModeCore(expr) == Spec.SupportedOctalMode(expr)
  {
  }

  lemma BridgeOctalMode(expr: string)
    requires Core.SupportedOctalModeCore(expr)
    ensures Core.OctalModeCore(expr) == Spec.OctalMode(expr)
  {
    BridgeSupportedOctalMode(expr);
  }

  lemma BridgeCopyExistingValue(value: bv32, current: bv32)
    ensures Core.CoreCopyExistingValue(value, current) ==
            Spec.SpecCopyExistingValue(value, current)
  {
  }

  lemma BridgeInvertModeBits(value: bv32)
    ensures Core.CoreInvertModeBits(value) == Spec.SpecInvertModeBits(value)
  {
  }

  lemma BridgeOmittedChangeBits(isDir: bool, mentioned: bv32)
    ensures Core.CoreOmittedChangeBits(isDir, mentioned) ==
            Spec.SpecOmittedChangeBits(isDir, mentioned)
  {
    BridgeInvertModeBits(mentioned);
  }

  lemma BridgeChangeAffectedMask(affected: bv32, umask: bv32)
    ensures Core.CoreChangeAffectedMask(affected, umask) ==
            Spec.SpecChangeAffectedMask(affected, umask)
  {
    BridgeInvertModeBits(umask);
  }

  lemma BridgeChangeValue(current: bv32, isDir: bool, change: Schema.ModeChange)
    ensures Core.CoreChangeValue(current, isDir, change) ==
            Spec.SpecChangeValue(current, isDir, change)
  {
    BridgeCopyExistingValue(change.value, current);
  }

  lemma BridgeMaskedChangeValue(
    current: bv32,
    isDir: bool,
    umask: bv32,
    change: Schema.ModeChange
  )
    ensures Core.CoreMaskedChangeValue(current, isDir, umask, change) ==
            Spec.SpecMaskedChangeValue(current, isDir, umask, change)
  {
    BridgeChangeValue(current, isDir, change);
    BridgeChangeAffectedMask(change.affected, umask);
    BridgeOmittedChangeBits(isDir, change.mentioned);
    BridgeInvertModeBits(Core.CoreOmittedChangeBits(isDir, change.mentioned));
  }

  lemma BridgePreservedAffectedBits(affected: bv32)
    ensures Core.CorePreservedAffectedBits(affected) ==
            Spec.SpecPreservedAffectedBits(affected)
  {
    BridgeInvertModeBits(affected);
  }

  lemma BridgePreservedChangeBits(isDir: bool, change: Schema.ModeChange)
    ensures Core.CorePreservedChangeBits(isDir, change) ==
            Spec.SpecPreservedChangeBits(isDir, change)
  {
    BridgePreservedAffectedBits(change.affected);
    BridgeOmittedChangeBits(isDir, change.mentioned);
  }

  lemma {:isolate_assertions} {:vcs_split_on_every_assert} BridgeApplyChange(
    current: bv32,
    isDir: bool,
    umask: bv32,
    change: Schema.ModeChange
  )
    ensures Core.CoreApplyChange(current, isDir, umask, change) ==
            Spec.SpecApplyChange(current, isDir, umask, change)
  {
    BridgeMaskedChangeValue(current, isDir, umask, change);
    var coreMasked := Core.CoreMaskedChangeValue(current, isDir, umask, change);
    var specMasked := Spec.SpecMaskedChangeValue(current, isDir, umask, change);
    assert coreMasked == specMasked;
    if change.op == '=' {
      BridgePreservedChangeBits(isDir, change);
      var corePreserved := Core.CorePreservedChangeBits(isDir, change);
      var specPreserved := Spec.SpecPreservedChangeBits(isDir, change);
      assert corePreserved == specPreserved;
      assert Core.CoreApplyChange(current, isDir, umask, change) ==
             BW.NormalizeMode((current & corePreserved) | coreMasked);
      assert Spec.SpecApplyChange(current, isDir, umask, change) ==
             BW.NormalizeMode((current & specPreserved) | specMasked);
    } else if change.op == '+' {
      assert Core.CoreApplyChange(current, isDir, umask, change) ==
             BW.NormalizeMode(current | coreMasked);
      assert Spec.SpecApplyChange(current, isDir, umask, change) ==
             BW.NormalizeMode(current | specMasked);
    } else {
      BridgeInvertModeBits(coreMasked);
      assert Core.CoreInvertModeBits(coreMasked) == Spec.SpecInvertModeBits(specMasked);
      assert Core.CoreApplyChange(current, isDir, umask, change) ==
             BW.NormalizeMode(current & Core.CoreInvertModeBits(coreMasked));
      assert Spec.SpecApplyChange(current, isDir, umask, change) ==
             BW.NormalizeMode(current & Spec.SpecInvertModeBits(specMasked));
    }
  }

  lemma BridgeModeChangesFrom(
    changes: seq<Schema.ModeChange>,
    i: nat,
    current: bv32,
    isDir: bool,
    umask: bv32
  )
    requires i <= |changes|
    ensures Spec.SpecModeChangesRelation(
              changes[i..],
              current,
              isDir,
              umask,
              Core.CoreModeAdjustFrom(changes, i, current, isDir, umask)
            )
    decreases |changes| - i
  {
    reveal Spec.SpecModeChangesRelation();
    if i < |changes| {
      BridgeApplyChange(current, isDir, umask, changes[i]);
      BridgeModeChangesFrom(
        changes,
        i + 1,
        Core.CoreApplyChange(current, isDir, umask, changes[i]),
        isDir,
        umask
      );
    }
  }

  lemma BridgeModeChanges(
    oldMode: bv32,
    isDir: bool,
    umask: bv32,
    changes: seq<Schema.ModeChange>
  )
    ensures Spec.SpecModeChangesRelation(
              changes,
              BW.NormalizeMode(oldMode),
              isDir,
              umask,
              Core.CoreModeAdjust(oldMode, isDir, umask, changes)
            )
  {
    BridgeModeChangesFrom(changes, 0, BW.NormalizeMode(oldMode), isDir, umask);
  }

  function SpecChangesOfExpr(expr: string): seq<Schema.ModeChange>
  {
    if |expr| > 0 && BW.IsOctalDigit(expr[0]) &&
       BW.AllOctalDigits(expr, 0) &&
       BW.OctalValue(expr, 0, 0) <= 4095 then
      var mode := BW.NormalizeMode(BW.ToBv32(BW.OctalValue(expr, 0, 0)));
      var mentioned :=
        if |expr| < 5 then
          (mode & (Schema.S_ISUID | Schema.S_ISGID)) |
          Schema.S_ISVTX | Schema.S_IRWXUGO
        else
          Schema.CHMOD_MODE_BITS;
      [Schema.ModeChange(
         '=',
         Schema.ModeOrdinary,
         Schema.CHMOD_MODE_BITS,
         mode,
         mentioned
       )]
    else if |expr| > 0 && !BW.IsOctalDigit(expr[0]) then
      match Schema.ParseSymbolic(expr, 0)
      case Invalid => []
      case Parsed(changes, endIdx) =>
        if endIdx == |expr| then changes else []
    else
      []
  }

  lemma ParseWhoSatisfiesRelation(
    expr: string,
    i: nat,
    accumulated: bv32
  )
    requires i <= |expr|
    ensures
      match Schema.ParseWhoFrom(expr, i, accumulated)
      case Invalid => true
      case Parsed(affected, next) =>
        Spec.SpecWhoRelation(
          expr, i, accumulated, affected, next
        )
    decreases |expr| - i
  {
    if i < |expr| &&
       !Schema.ModeIsOp(expr[i]) &&
       Schema.ModeIsWhoChar(expr[i]) {
      ParseWhoSatisfiesRelation(
        expr,
        i + 1,
        accumulated | Schema.WhoMask(expr[i])
      );
    }
  }

  lemma ParseOctalRunSatisfiesRelation(
    expr: string,
    i: nat,
    accumulated: int
  )
    requires i <= |expr|
    ensures var parsed := Schema.ParseOctalRun(expr, i, accumulated);
            Spec.SpecOctalRunRelation(
              expr, i, accumulated, parsed.value, parsed.next
            )
    decreases |expr| - i
  {
    if i < |expr| && BW.IsOctalDigit(expr[i]) {
      ParseOctalRunSatisfiesRelation(
        expr,
        i + 1,
        accumulated * 8 + BW.CharToDigit(expr[i])
      );
    }
  }

  lemma ParsePermsSatisfiesRelation(
    expr: string,
    i: nat,
    accumulated: bv32,
    accumulatedFlag: Schema.ModeFlag
  )
    requires i <= |expr|
    ensures var parsed :=
              Schema.ParsePerms(expr, i, accumulated, accumulatedFlag);
            Spec.SpecPermsRelation(
              expr,
              i,
              accumulated,
              accumulatedFlag,
              parsed.value,
              parsed.flag,
              parsed.next
            )
    decreases |expr| - i
  {
    if i < |expr| &&
       (expr[i] == 'r' || expr[i] == 'w' || expr[i] == 'x' ||
        expr[i] == 'X' || expr[i] == 's' || expr[i] == 't') {
      var nextValue :=
        if expr[i] == 'r' then accumulated | Schema.READ_MASK
        else if expr[i] == 'w' then accumulated | Schema.WRITE_MASK
        else if expr[i] == 'x' then accumulated | Schema.EXEC_MASK
        else if expr[i] == 's' then
          accumulated | (Schema.S_ISUID | Schema.S_ISGID)
        else if expr[i] == 't' then accumulated | Schema.S_ISVTX
        else accumulated;
      var nextFlag :=
        if expr[i] == 'X' then Schema.FlagWithX(accumulatedFlag)
        else accumulatedFlag;
      ParsePermsSatisfiesRelation(
        expr, i + 1, nextValue, nextFlag
      );
    }
  }

  lemma ParseOneChangeSatisfiesRelation(
    expr: string,
    i: nat,
    affected: bv32
  )
    requires i <= |expr|
    ensures
      match Schema.ParseOneChange(expr, i, affected)
      case Invalid => true
      case Parsed(change, next) =>
        Spec.SpecOneChangeRelation(expr, i, affected, change, next)
  {
    if i < |expr| && Schema.ModeIsOp(expr[i]) {
      var j := i + 1;
      if j < |expr| {
        if BW.IsOctalDigit(expr[j]) {
          ParseOctalRunSatisfiesRelation(expr, j, 0);
        } else if !(expr[j] == 'u' || expr[j] == 'g' || expr[j] == 'o') {
          ParsePermsSatisfiesRelation(
            expr, j, 0 as bv32, Schema.ModeOrdinary
          );
        }
      }
    }
  }

  lemma ParseOpSequenceSatisfiesRelation(
    expr: string,
    i: nat,
    affected: bv32
  )
    requires i <= |expr|
    ensures
      match Schema.ParseOpSeq(expr, i, affected)
      case Invalid => true
      case Parsed(changes, next) =>
        Spec.SpecOpSequenceRelation(
          expr, i, affected, changes, next
        )
    decreases |expr| - i
  {
    ParseOneChangeSatisfiesRelation(expr, i, affected);
    match Schema.ParseOneChange(expr, i, affected)
    case Invalid =>
    case Parsed(change, next) =>
      if next > i && next < |expr| && Schema.ModeIsOp(expr[next]) {
        ParseOpSequenceSatisfiesRelation(expr, next, affected);
      }
  }

  lemma ParseSymbolicSatisfiesRelation(expr: string, i: nat)
    requires i <= |expr|
    ensures
      match Schema.ParseSymbolic(expr, i)
      case Invalid => true
      case Parsed(changes, next) =>
        Spec.SpecSymbolicChangesFromRelation(
          expr, i, changes, next
        )
    decreases |expr| - i
  {
    if i < |expr| {
      ParseWhoSatisfiesRelation(expr, i, 0 as bv32);
      match Schema.ParseWho(expr, i)
      case Invalid =>
      case Parsed(affected, whoNext) =>
        ParseOpSequenceSatisfiesRelation(expr, whoNext, affected);
        match Schema.ParseOpSeq(expr, whoNext, affected)
        case Invalid =>
        case Parsed(clause, clauseNext) =>
          if clauseNext >= i && clauseNext < |expr| &&
             expr[clauseNext] == ',' {
            ParseSymbolicSatisfiesRelation(expr, clauseNext + 1);
          }
    }
  }

  lemma ValidModeProgramSatisfiesRelation(expr: string)
    requires Schema.IsValidModeExpr(expr)
    ensures Spec.SpecModeProgramRelation(
              expr, SpecChangesOfExpr(expr)
            )
  {
    if BW.IsOctalDigit(expr[0]) {
    } else {
      ParseSymbolicSatisfiesRelation(expr, 0);
    }
  }

  lemma {:isolate_assertions} {:vcs_split_on_every_assert} BridgeApplyModeExpr(
    expr: string,
    oldMode: bv32,
    isDir: bool,
    umask: bv32
  )
    ensures Spec.SpecModeChangesRelation(
              SpecChangesOfExpr(expr),
              BW.NormalizeMode(oldMode),
              isDir,
              umask,
              Core.CoreApplyModeExpr(expr, oldMode, isDir, umask)
            )
  {
    var base := BW.NormalizeMode(oldMode);
    var coreResult := Core.CoreApplyModeExpr(expr, oldMode, isDir, umask);
    if |expr| > 0 && BW.IsOctalDigit(expr[0]) && BW.AllOctalDigits(expr, 0) &&
       BW.OctalValue(expr, 0, 0) <= 4095 {
      var raw := BW.OctalValue(expr, 0, 0);
      var mode := BW.NormalizeMode(BW.ToBv32(raw));
      var mentioned :=
        if |expr| < 5 then
          (mode & (Schema.S_ISUID | Schema.S_ISGID)) | Schema.S_ISVTX | Schema.S_IRWXUGO
        else
          Schema.CHMOD_MODE_BITS;
      var changes := [Schema.ModeChange(
                        '=',
                        Schema.ModeOrdinary,
                        Schema.CHMOD_MODE_BITS,
                        mode,
                        mentioned
                      )];
      assert SpecChangesOfExpr(expr) == changes;
      assert coreResult == Core.CoreModeAdjust(
                             base, isDir, umask, changes
                           );
      BridgeModeChanges(
        oldMode,
        isDir,
        umask,
        changes
      );
      assert Spec.SpecModeChangesRelation(
          SpecChangesOfExpr(expr), base, isDir, umask, coreResult
        );
    } else if |expr| > 0 && !BW.IsOctalDigit(expr[0]) {
      match Schema.ParseSymbolic(expr, 0)
      case Invalid => {
        assert SpecChangesOfExpr(expr) == [];
        assert coreResult == base;
        reveal Spec.SpecModeChangesRelation();
        assert Spec.SpecModeChangesRelation(
            SpecChangesOfExpr(expr), base, isDir, umask, coreResult
          );
      }
      case Parsed(changes, endIdx) =>
        if endIdx == |expr| {
          assert SpecChangesOfExpr(expr) == changes;
          assert coreResult == Core.CoreModeAdjust(
                                 base, isDir, umask, changes
                               );
          BridgeModeChanges(oldMode, isDir, umask, changes);
          assert Spec.SpecModeChangesRelation(
              SpecChangesOfExpr(expr), base, isDir, umask, coreResult
            );
        } else {
          assert SpecChangesOfExpr(expr) == [];
          assert coreResult == base;
          reveal Spec.SpecModeChangesRelation();
          assert Spec.SpecModeChangesRelation(
              SpecChangesOfExpr(expr), base, isDir, umask, coreResult
            );
        }
    } else {
      assert SpecChangesOfExpr(expr) == [];
      assert coreResult == base;
      reveal Spec.SpecModeChangesRelation();
      assert Spec.SpecModeChangesRelation(
          SpecChangesOfExpr(expr), base, isDir, umask, coreResult
        );
    }
  }

  function SpecModePlanOfCore(plan: Core.CoreModePlan): Spec.SpecModePlan
  {
    match plan
    case CoreGeneralModePlan(expr, umask) =>
      Spec.SpecGeneralModePlan(SpecChangesOfExpr(expr), umask)
    case CoreReferenceModePlan(mode) => Spec.SpecReferenceModePlan(mode)
  }

  function SpecPathStatusOfCore(status: Core.CorePathStatus): Spec.SpecPathStatus
  {
    match status
    case CorePathChanged(before, after) => Spec.SpecPathChanged(before, after)
    case CorePathRetained(mode) => Spec.SpecPathRetained(mode)
    case CorePathAccessFailed(err) => Spec.SpecPathAccessFailed(err)
    case CorePathChangeFailed(before, desired, err) =>
      Spec.SpecPathChangeFailed(before, desired, err)
    case CorePathSurprise(before, after, naive) =>
      Spec.SpecPathSurprise(before, after, naive)
  }

  function SpecPathResultOfCore(result: Core.CorePathResult): Spec.SpecPathResult
  {
    Spec.SpecPathResult(
      result.fs,
      result.stdoutChunk,
      result.stderrChunk,
      result.ok,
      SpecPathStatusOfCore(result.status)
    )
  }

  lemma AndAssociative(a: bool, b: bool, c: bool)
    ensures (a && (b && c)) == ((a && b) && c)
  {
    if a {
      if b {
      }
    }
  }

  lemma BridgePathAccessFailureResult(
    cmd: Schema.ChmodCmd,
    fs: BW.FileSystem,
    path: string,
    actual: BW.Path,
    follow: bool,
    err: int
  )
    ensures SpecPathResultOfCore(
              Core.CorePathAccessFailureResult(cmd, fs, path, actual, follow, err)
            ) == Spec.SpecPathAccessFailureResult(
                   cmd, fs, path, actual, follow, err
                 )
  {
    BridgeUsesExplicitPhysicalDereference(cmd);
    BridgeNoDereferenceSymlink(fs, actual, false);
    BridgeCannotDereferenceMessage(path, err);
    BridgePathIsDanglingSymlinkFailure(fs, actual, follow, err);
    BridgeDanglingSymlinkMessage(path);
    BridgeErrnoText(err);
    BridgeAccessErrorMessage(path, err);
    BridgeAccessFailureMessage(path);
  }

  lemma BridgeNodeIsDirectory(node: BW.FsNode)
    ensures Core.CoreNodeIsDirectory(node) == Spec.SpecNodeIsDirectory(node)
  {
  }

  lemma BridgePlannedMode(plan: Core.CoreModePlan, before: bv32, isDir: bool)
    ensures Spec.SpecPlannedModeRelation(
              SpecModePlanOfCore(plan),
              before,
              isDir,
              Core.CorePlannedMode(plan, before, isDir)
            )
  {
    match plan
    case CoreGeneralModePlan(expr, umask) =>
      BridgeApplyModeExpr(expr, before, isDir, umask);
    case CoreReferenceModePlan(mode) =>
  }

  lemma BridgeNaiveMode(plan: Core.CoreModePlan, before: bv32, isDir: bool)
    ensures Spec.SpecNaiveModeRelation(
              SpecModePlanOfCore(plan),
              before,
              isDir,
              Core.CoreNaiveMode(plan, before, isDir)
            )
  {
    match plan
    case CoreGeneralModePlan(expr, _) =>
      BridgeApplyModeExpr(expr, before, isDir, 0 as bv32);
    case CoreReferenceModePlan(mode) =>
  }

  lemma {:isolate_assertions} {:vcs_split_on_every_assert} BridgeDiagnoseSurprise(
    cmd: Schema.ChmodCmd,
    plan: Core.CoreModePlan,
    before: bv32,
    after: bv32,
    isDir: bool
  )
    ensures Core.CoreDiagnoseSurprise(cmd, plan, before, after, isDir) ==
            Spec.SpecDiagnoseSurpriseForNaive(
              cmd,
              after,
              Core.CoreNaiveMode(plan, before, isDir)
            )
  {
    var coreNaive := Core.CoreNaiveMode(plan, before, isDir);
    BridgeInvertModeBits(coreNaive);
    assert Core.CoreInvertModeBits(coreNaive) ==
           Spec.SpecInvertModeBits(coreNaive);
    assert Core.CoreDiagnoseSurprise(cmd, plan, before, after, isDir) ==
           (cmd.diagnoseSurprises &&
            (after & Core.CoreInvertModeBits(coreNaive)) != 0 as bv32);
    assert Spec.SpecDiagnoseSurpriseForNaive(cmd, after, coreNaive) ==
           (cmd.diagnoseSurprises &&
            (after & Spec.SpecInvertModeBits(coreNaive)) != 0 as bv32);
  }

  lemma BridgeSuccessStdout(
    cmd: Schema.ChmodCmd,
    path: string,
    before: bv32,
    after: bv32
  )
    ensures Core.CoreSuccessStdout(cmd, path, before, after) ==
            Spec.SpecSuccessStdout(cmd, path, before, after)
  {
    if cmd.verbose {
      if before == after {
        BridgeRetainedMessage(path, after);
      } else {
        BridgeChangedMessage(path, before, after);
      }
    } else if cmd.changes && before != after {
      BridgeChangedMessage(path, before, after);
    }
  }

  lemma BridgePostChangeLookupNeeded(
    cmd: Schema.ChmodCmd,
    after: bv32
  )
    ensures Core.CorePostChangeLookupNeeded(cmd, after) ==
            Spec.SpecPostChangeLookupNeeded(cmd, after)
  {
  }

  lemma {:isolate_assertions} {:vcs_split_on_every_assert} BridgeSuccessfulChangeResult(
    cmd: Schema.ChmodCmd,
    plan: Core.CoreModePlan,
    path: string,
    actual: BW.Path,
    follow: bool,
    before: bv32,
    after: bv32,
    isDir: bool,
    fs: BW.FileSystem
  )
    ensures Spec.SpecSuccessfulChangeResultRelation(
              cmd,
              SpecModePlanOfCore(plan),
              path,
              actual,
              follow,
              before,
              after,
              isDir,
              fs,
              SpecPathResultOfCore(Core.CoreSuccessfulChangeResult(
                                     cmd, plan, path, actual, follow, before, after, isDir, fs
                                   ))
            )
  {
    ghost var coreResult := Core.CoreSuccessfulChangeResult(
      cmd, plan, path, actual, follow, before, after, isDir, fs
    );
    var naive := Core.CoreNaiveMode(plan, before, isDir);
    ghost var specResult := Spec.SpecSuccessfulChangeResultForNaive(
      cmd,
      path,
      actual,
      follow,
      before,
      after,
      naive,
      fs
    );
    BridgePostChangeLookupNeeded(cmd, after);
    BridgeNaiveMode(plan, before, isDir);
    BridgeDiagnoseSurprise(cmd, plan, before, after, isDir);
    BridgeSuccessStdout(cmd, path, before, after);
    BridgeRetainedMessage(path, after);
    BridgeSurpriseModeMessage(path, after, naive);
    if Core.CorePostChangeLookupNeeded(cmd, after) {
      match IOC.ResolvePathForMetadataFields(fs, actual, follow)
      case Err(_) =>
        var err := IOC.MetadataFailureErrFields(fs, actual, follow);
        BridgeGettingNewAttributesMessage(path, err);
        assert SpecPathResultOfCore(coreResult) == specResult by {
          reveal SpecPathResultOfCore;
          reveal SpecPathStatusOfCore;
          reveal Core.CoreSuccessfulChangeResult;
          reveal Spec.SpecSuccessfulChangeResultForNaive;
        }
      case Ok(target) =>
        if !BW.FsContainsPath(fs, target) {
          var err := IOC.MetadataFailureErrFields(fs, actual, follow);
          BridgeGettingNewAttributesMessage(path, err);
          assert SpecPathResultOfCore(coreResult) == specResult by {
            reveal SpecPathResultOfCore;
            reveal SpecPathStatusOfCore;
            reveal Core.CoreSuccessfulChangeResult;
            reveal Spec.SpecSuccessfulChangeResultForNaive;
          }
        } else {
          var observed := BW.NodeMode(BW.FsNodeAt(fs, target));
          BridgeDiagnoseSurprise(cmd, plan, before, observed, isDir);
          BridgeSuccessStdout(cmd, path, before, observed);
          var observedNaive := Core.CoreNaiveMode(plan, before, isDir);
          BridgeSurpriseModeMessage(path, observed, observedNaive);
          assert SpecPathResultOfCore(coreResult) == specResult by {
            reveal SpecPathResultOfCore;
            reveal SpecPathStatusOfCore;
            reveal Core.CoreSuccessfulChangeResult;
            reveal Spec.SpecSuccessfulChangeResultForNaive;
          }
        }
    } else {
      assert SpecPathResultOfCore(coreResult) == specResult by {
        reveal SpecPathResultOfCore;
        reveal SpecPathStatusOfCore;
        reveal Core.CoreSuccessfulChangeResult;
        reveal Spec.SpecSuccessfulChangeResultForNaive;
      }
    }
    assert Spec.SpecNaiveModeRelation(
        SpecModePlanOfCore(plan), before, isDir, naive
      );
    assert exists candidate: bv32 ::
        Spec.SpecNaiveModeRelation(
          SpecModePlanOfCore(plan), before, isDir, candidate
        ) &&
        SpecPathResultOfCore(coreResult) ==
        Spec.SpecSuccessfulChangeResultForNaive(
          cmd, path, actual, follow, before, after, candidate, fs
        ) by {
      ghost var candidate := naive;
    }
  }

  lemma BridgeModeSetSuppressed(
    fs: BW.FileSystem,
    target: BW.Path,
    follow: bool
  )
    requires BW.FsContainsPath(fs, target)
    ensures Core.CoreModeSetSuppressed(fs, target, follow) ==
            Spec.SpecModeSetSuppressed(fs, target, follow)
  {
  }

  lemma BridgeNoDereferenceSymlink(
    fs: BW.FileSystem,
    path: BW.Path,
    follow: bool
  )
    ensures Core.CoreNoDereferenceSymlink(fs, path, follow) ==
            Spec.SpecNoDereferenceSymlink(fs, path, follow)
  {
  }

  lemma BridgeModeSetFs(
    fs: BW.FileSystem,
    follow: bool,
    target: BW.Path,
    desired: bv32,
    now: int
  )
    requires BW.FsContainsPath(fs, target)
    ensures Core.CoreModeSetFs(fs, follow, target, desired, now) ==
            Spec.SpecModeSetFs(fs, follow, target, desired, now)
  {
    BridgeModeSetSuppressed(fs, target, follow);
  }

  lemma BridgePhysicalPathStep(
    cmd: Schema.ChmodCmd,
    plan: Core.CoreModePlan,
    cwd: BW.Path,
    fs: BW.FileSystem,
    path: string,
    now: int
  )
    requires Core.CoreUsesPhysicalTopLevelMetadata(cmd)
    ensures Spec.SpecPathStepRelation(
              cmd,
              SpecModePlanOfCore(plan),
              cwd,
              fs,
              path,
              SpecPathResultOfCore(
                Core.CorePathStep(cmd, plan, cwd, fs, path, now)
              ),
              now
            )
  {
    BridgeMakeAbsolute(cwd, path);
    BridgeShouldDereference(cmd);
    BridgeUsesPhysicalTopLevelMetadata(cmd);
    var actual := Core.MakeAbsoluteCore(cwd, path);
    assert Spec.SpecUsesPhysicalTopLevelMetadata(cmd);
    match IOC.ResolvePathForMetadataFields(fs, actual, false)
    case Err(_) =>
      var err := IOC.MetadataFailureErrFields(fs, actual, false);
      assert SpecPathResultOfCore(
          Core.CorePathAccessFailureResult(cmd, fs, path, actual, false, err)
        ) == Spec.SpecPathAccessFailureResult(
                    cmd, fs, path, actual, false, err
                  ) by {
        BridgePathAccessFailureResult(cmd, fs, path, actual, false, err);
      }
    case Ok(metadataTarget) =>
      if !BW.FsContainsPath(fs, metadataTarget) {
        var err := IOC.MetadataFailureErrFields(fs, actual, false);
        assert SpecPathResultOfCore(
            Core.CorePathAccessFailureResult(cmd, fs, path, actual, false, err)
          ) == Spec.SpecPathAccessFailureResult(
                      cmd, fs, path, actual, false, err
                    ) by {
          BridgePathAccessFailureResult(cmd, fs, path, actual, false, err);
        }
      } else {
        var node := BW.FsNodeAt(fs, metadataTarget);
        var before := BW.NodeMode(node);
        BridgeNodeIsDirectory(node);
        var isDir := Core.CoreNodeIsDirectory(node);
        BridgePlannedMode(plan, before, isDir);
        var desired := Core.CorePlannedMode(plan, before, isDir);
        match IOC.ResolvePathForMetadataFields(fs, actual, true)
        case Err(_) =>
          var err := IOC.MetadataFailureErrFields(fs, actual, true);
          BridgeFailedChangeMessage(path, before, desired);
          BridgeChangeErrorMessage(path, err);
        case Ok(changeTarget) =>
          if !BW.FsContainsPath(fs, changeTarget) {
            var err := IOC.MetadataFailureErrFields(fs, actual, true);
            BridgeFailedChangeMessage(path, before, desired);
            BridgeChangeErrorMessage(path, err);
          } else {
            BridgeModeSetFs(fs, true, changeTarget, desired, now);
            var after := BW.NormalizeMode(desired);
            BridgeSuccessfulChangeResult(
              cmd, plan, path, actual, true, before, after, isDir,
              Core.CoreModeSetFs(fs, true, changeTarget, desired, now)
            );
            BridgeNaiveMode(plan, before, isDir);
            BridgeDiagnoseSurprise(cmd, plan, before, after, isDir);
            var naive := Core.CoreNaiveMode(plan, before, isDir);
            BridgeSurpriseModeMessage(path, after, naive);
            BridgeSuccessStdout(cmd, path, before, after);
          }
      }
  }

  lemma BridgeOrdinaryPathStep(
    cmd: Schema.ChmodCmd,
    plan: Core.CoreModePlan,
    cwd: BW.Path,
    fs: BW.FileSystem,
    path: string,
    now: int
  )
    requires !Core.CoreUsesPhysicalTopLevelMetadata(cmd)
    ensures Spec.SpecPathStepRelation(
              cmd,
              SpecModePlanOfCore(plan),
              cwd,
              fs,
              path,
              SpecPathResultOfCore(
                Core.CorePathStep(cmd, plan, cwd, fs, path, now)
              ),
              now
            )
  {
    BridgeMakeAbsolute(cwd, path);
    BridgeShouldDereference(cmd);
    BridgeUsesPhysicalTopLevelMetadata(cmd);
    var actual := Core.MakeAbsoluteCore(cwd, path);
    var follow := Core.ShouldDereferenceCore(cmd);
    assert !Spec.SpecUsesPhysicalTopLevelMetadata(cmd);
    match IOC.ResolvePathForMetadataFields(fs, actual, follow)
    case Err(_) =>
      var err := IOC.MetadataFailureErrFields(fs, actual, follow);
      BridgePathAccessFailureResult(cmd, fs, path, actual, follow, err);
    case Ok(target) =>
      if !BW.FsContainsPath(fs, target) {
        var err := IOC.MetadataFailureErrFields(fs, actual, follow);
        BridgePathAccessFailureResult(cmd, fs, path, actual, follow, err);
      } else {
        var node := BW.FsNodeAt(fs, target);
        var before := BW.NodeMode(node);
        BridgeNoDereferenceSymlink(fs, actual, follow);
        if Core.CoreNoDereferenceSymlink(fs, actual, follow) {
          BridgeUsesFollowedTopLevelNoDereference(cmd);
          if Core.CoreUsesFollowedTopLevelNoDereference(cmd) {
            var followed := IOC.ResolvePathForMetadataFields(fs, actual, true);
            var followedOk :=
              match followed
              case Err(_) => false
              case Ok(followedTarget) => BW.FsContainsPath(fs, followedTarget);
            var err := IOC.MetadataFailureErrFields(fs, actual, true);
            if !followedOk && err != 2 {
              BridgePathAccessFailureResult(cmd, fs, path, actual, true, err);
            } else {
              BridgeNeitherChangedMessage(path);
            }
          } else {
            BridgeNeitherChangedMessage(path);
          }
        } else {
          BridgeNodeIsDirectory(node);
          var isDir := Core.CoreNodeIsDirectory(node);
          BridgePlannedMode(plan, before, isDir);
          var desired := Core.CorePlannedMode(plan, before, isDir);
          BridgeModeSetSuppressed(fs, target, follow);
          BridgeModeSetFs(fs, follow, target, desired, now);
          var after :=
            if Core.CoreModeSetSuppressed(fs, target, follow) then before
            else BW.NormalizeMode(desired);
          BridgeSuccessfulChangeResult(
            cmd, plan, path, actual, follow, before, after, isDir,
            Core.CoreModeSetFs(fs, follow, target, desired, now)
          );
          BridgeNaiveMode(plan, before, isDir);
          BridgeDiagnoseSurprise(cmd, plan, before, after, isDir);
          var naive := Core.CoreNaiveMode(plan, before, isDir);
          BridgeSurpriseModeMessage(path, after, naive);
          BridgeSuccessStdout(cmd, path, before, after);
        }
      }
  }

  lemma BridgePathStep(
    cmd: Schema.ChmodCmd,
    plan: Core.CoreModePlan,
    cwd: BW.Path,
    fs: BW.FileSystem,
    path: string,
    now: int
  )
    ensures Spec.SpecPathStepRelation(
              cmd,
              SpecModePlanOfCore(plan),
              cwd,
              fs,
              path,
              SpecPathResultOfCore(
                Core.CorePathStep(cmd, plan, cwd, fs, path, now)
              ),
              now
            )
  {
    if Core.CoreUsesPhysicalTopLevelMetadata(cmd) {
      BridgePhysicalPathStep(cmd, plan, cwd, fs, path, now);
    } else {
      BridgeOrdinaryPathStep(cmd, plan, cwd, fs, path, now);
    }
  }

  lemma {:isolate_assertions} BridgeRunFilesRelation(
    files: seq<string>,
    i: nat,
    cmd: Schema.ChmodCmd,
    plan: Core.CoreModePlan,
    cwd: BW.Path,
    fs: BW.FileSystem,
    stdout: BW.Bytes,
    stderr: BW.Bytes,
    allOk: bool,
    now: int
  )
    requires i <= |files|
    ensures
      var result := Core.CoreRunFilesFrom(
                      files, i, cmd, plan, cwd, fs, now
                    );
      exists trace: Spec.SpecBatchTrace {:nowarn} ::
        Spec.SpecBatchTraceRelation(
          files[i..],
          cmd,
          SpecModePlanOfCore(plan),
          cwd,
          fs,
          stdout,
          stderr,
          allOk,
          result.fs,
          stdout + result.stdoutChunk,
          stderr + result.stderrChunk,
          allOk && result.allOk,
          trace,
          now
        )
    decreases |files| - i
  {
    reveal Spec.SpecBatchTraceRelation;
    if i < |files| {
      BridgePathStep(cmd, plan, cwd, fs, files[i], now);
      var step := Core.CorePathStep(cmd, plan, cwd, fs, files[i], now);
      reveal SpecPathResultOfCore;
      BridgeRunFilesRelation(
        files,
        i + 1,
        cmd,
        plan,
        cwd,
        step.fs,
        stdout + step.stdoutChunk,
        stderr + step.stderrChunk,
        allOk && step.ok,
        now
      );
      var rest := Core.CoreRunFilesFrom(
        files, i + 1, cmd, plan, cwd, step.fs, now
      );
      var restTrace :| Spec.SpecBatchTraceRelation(
          files[i + 1..],
          cmd,
          SpecModePlanOfCore(plan),
          cwd,
          step.fs,
          stdout + step.stdoutChunk,
          stderr + step.stderrChunk,
          allOk && step.ok,
          rest.fs,
          (stdout + step.stdoutChunk) + rest.stdoutChunk,
          (stderr + step.stderrChunk) + rest.stderrChunk,
          (allOk && step.ok) && rest.allOk,
          restTrace,
          now
        );
      assert files[i..][0] == files[i];
      assert files[i..][1..] == files[i + 1..];
      Core.AppendAssociative(stdout, step.stdoutChunk, rest.stdoutChunk);
      Core.AppendAssociative(stderr, step.stderrChunk, rest.stderrChunk);
      AndAssociative(allOk, step.ok, rest.allOk);
      assert Core.CoreRunFilesFrom(
          files, i, cmd, plan, cwd, fs, now
        ) == Core.CoreBatchResult(
                    rest.fs,
                    step.stdoutChunk + rest.stdoutChunk,
                    step.stderrChunk + rest.stderrChunk,
                    step.ok && rest.allOk
                  );
      assert Spec.SpecBatchTraceRelation(
          files[i..],
          cmd,
          SpecModePlanOfCore(plan),
          cwd,
          fs,
          stdout,
          stderr,
          allOk,
          rest.fs,
          stdout + (step.stdoutChunk + rest.stdoutChunk),
          stderr + (step.stderrChunk + rest.stderrChunk),
          allOk && (step.ok && rest.allOk),
          Spec.SpecBatchNext(fs, stdout, stderr, allOk, restTrace),
          now
        );
    } else {
      assert i == |files|;
      assert files[i..] == [];
      assert Core.CoreRunFilesFrom(
          files, i, cmd, plan, cwd, fs, now
        ) == Core.CoreBatchResult(fs, [], [], true);
      assert stdout + [] == stdout;
      assert stderr + [] == stderr;
      assert (allOk && true) == allOk by {
        if allOk {
        }
      }
      assert Spec.SpecBatchTraceRelation(
          [],
          cmd,
          SpecModePlanOfCore(plan),
          cwd,
          fs,
          stdout,
          stderr,
          allOk,
          fs,
          stdout,
          stderr,
          allOk,
          Spec.SpecBatchEnd(fs, stdout, stderr, allOk),
          now
        );
      assert Spec.SpecBatchTraceRelation(
          files[i..],
          cmd,
          SpecModePlanOfCore(plan),
          cwd,
          fs,
          stdout,
          stderr,
          allOk,
          Core.CoreRunFilesFrom(
            files, i, cmd, plan, cwd, fs, now
          ).fs,
          stdout + Core.CoreRunFilesFrom(
            files, i, cmd, plan, cwd, fs, now
          ).stdoutChunk,
          stderr + Core.CoreRunFilesFrom(
            files, i, cmd, plan, cwd, fs, now
          ).stderrChunk,
          allOk && Core.CoreRunFilesFrom(
            files, i, cmd, plan, cwd, fs, now
          ).allOk,
          Spec.SpecBatchEnd(fs, stdout, stderr, allOk),
          now
        );
      assert exists trace: Spec.SpecBatchTrace {:nowarn} ::
          Spec.SpecBatchTraceRelation(
            files[i..],
            cmd,
            SpecModePlanOfCore(plan),
            cwd,
            fs,
            stdout,
            stderr,
            allOk,
            Core.CoreRunFilesFrom(
              files, i, cmd, plan, cwd, fs, now
            ).fs,
            stdout + Core.CoreRunFilesFrom(
              files, i, cmd, plan, cwd, fs, now
            ).stdoutChunk,
            stderr + Core.CoreRunFilesFrom(
              files, i, cmd, plan, cwd, fs, now
            ).stderrChunk,
            allOk && Core.CoreRunFilesFrom(
              files, i, cmd, plan, cwd, fs, now
            ).allOk,
            trace,
            now
          );
    }
  }

  lemma {:isolate_assertions} BridgeBatchOutcome(
    cmd: Schema.ChmodCmd,
    plan: Core.CoreModePlan,
    fs0: BW.FileSystem,
    cwd0: BW.Path,
    fs2: BW.FileSystem,
    stdout0: BW.Bytes,
    stdout2: BW.Bytes,
    stderr0: BW.Bytes,
    stderr2: BW.Bytes,
    exit: int,
    now: int
  )
    requires Core.CoreBatchOutcome(
               cmd, plan, fs0, cwd0, fs2, stdout0, stdout2,
               stderr0, stderr2, exit, now
             )
    ensures Spec.SpecBatchOutcome(
              cmd,
              SpecModePlanOfCore(plan),
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
  {
    var specPlan := SpecModePlanOfCore(plan);
    BridgeRunFilesRelation(
      cmd.files,
      0,
      cmd,
      plan,
      cwd0,
      fs0,
      stdout0,
      stderr0,
      true,
      now
    );
    var result := Core.CoreRunFiles(cmd, plan, cwd0, fs0, now);
    var trace :| Spec.SpecBatchTraceRelation(
        cmd.files,
        cmd,
        specPlan,
        cwd0,
        fs0,
        stdout0,
        stderr0,
        true,
        result.fs,
        stdout0 + result.stdoutChunk,
        stderr0 + result.stderrChunk,
        result.allOk,
        trace,
        now
      );
    reveal Core.CoreBatchOutcome;
    assert exists specTrace: Spec.SpecBatchTrace, allOk: bool ::
        Spec.SpecBatchTraceRelation(
          cmd.files,
          cmd,
          specPlan,
          cwd0,
          fs0,
          stdout0,
          stderr0,
          true,
          fs2,
          stdout2,
          stderr2,
          allOk,
          specTrace,
          now
        ) &&
        exit == (if allOk then 0 else 1) by {
      assert Spec.SpecBatchTraceRelation(
          cmd.files,
          cmd,
          specPlan,
          cwd0,
          fs0,
          stdout0,
          stderr0,
          true,
          fs2,
          stdout2,
          stderr2,
          result.allOk,
          trace,
          now
        );
    }
  }

  lemma BridgeReferenceFailure(
    cmd: Schema.ChmodCmd,
    fs: BW.FileSystem,
    cwd: BW.Path
  )
    requires Core.CoreReferenceFailure(cmd, fs, cwd)
    ensures Spec.SpecReferenceFailure(cmd, fs, cwd)
  {
    BridgeMakeAbsolute(cwd, cmd.referenceFile);
  }

  lemma BridgeReferenceFailureEquivalent(
    cmd: Schema.ChmodCmd,
    fs: BW.FileSystem,
    cwd: BW.Path
  )
    ensures Core.CoreReferenceFailure(cmd, fs, cwd) <==>
            Spec.SpecReferenceFailure(cmd, fs, cwd)
  {
    BridgeMakeAbsolute(cwd, cmd.referenceFile);
  }

  lemma BridgeReferenceFailureOutcome(
    cmd: Schema.ChmodCmd,
    fs0: BW.FileSystem,
    cwd0: BW.Path,
    fs2: BW.FileSystem,
    stdout0: BW.Bytes,
    stdout2: BW.Bytes,
    stderr0: BW.Bytes,
    stderr2: BW.Bytes,
    exit: int
  )
    requires Core.CoreReferenceFailureOutcome(
               cmd, fs0, cwd0, fs2, stdout0, stdout2, stderr0, stderr2, exit
             )
    ensures Spec.SpecReferenceFailureOutcome(
              cmd, fs0, cwd0, fs2, stdout0, stdout2, stderr0, stderr2, exit
            )
  {
    var mode: bv32, err: int :|
      IOC.GetFileModeContractFields(
        fs0,
        Core.MakeAbsoluteCore(cwd0, cmd.referenceFile),
        true,
        false,
        mode,
        err
      ) &&
      fs2 == fs0 && stdout2 == stdout0 &&
      stderr2 == stderr0 + Core.ReferenceErrorMessageCore(
        cmd.referenceFile,
        Core.ErrnoTextCore(err)
      ) && exit == 1;
    BridgeMakeAbsolute(cwd0, cmd.referenceFile);
    BridgeReferenceErrorMessage(cmd.referenceFile, err);
    assert exists specMode: bv32, specErr: int ::
        IOC.GetFileModeContractFields(
          fs0,
          Spec.MakeAbsolute(cwd0, cmd.referenceFile),
          true,
          false,
          specMode,
          specErr
        ) &&
        fs2 == fs0 && stdout2 == stdout0 &&
        stderr2 == stderr0 + Spec.ReferenceErrorMessageSpec(
          cmd.referenceFile,
          Spec.ErrnoTextSpec(specErr)
        ) && exit == 1;
  }

  lemma BridgeReferenceBatchOutcome(
    cmd: Schema.ChmodCmd,
    fs0: BW.FileSystem,
    cwd0: BW.Path,
    fs2: BW.FileSystem,
    stdout0: BW.Bytes,
    stdout2: BW.Bytes,
    stderr0: BW.Bytes,
    stderr2: BW.Bytes,
    exit: int,
    now: int
  )
    requires Core.CoreReferenceBatchOutcome(
               cmd, fs0, cwd0, fs2, stdout0, stdout2,
               stderr0, stderr2, exit, now
             )
    ensures Spec.SpecReferenceBatchOutcome(
              cmd, fs0, cwd0, fs2, stdout0, stdout2,
              stderr0, stderr2, exit, now
            )
  {
    var refMode: bv32 :|
      IOC.GetFileModeContractFields(
        fs0,
        Core.MakeAbsoluteCore(cwd0, cmd.referenceFile),
        true,
        true,
        refMode,
        0
      ) &&
      Core.CoreBatchOutcome(
        cmd,
        Core.CoreReferenceModePlan(refMode),
        fs0,
        cwd0,
        fs2,
        stdout0,
        stdout2,
        stderr0,
        stderr2,
        exit,
        now
      );
    BridgeMakeAbsolute(cwd0, cmd.referenceFile);
    BridgeBatchOutcome(
      cmd,
      Core.CoreReferenceModePlan(refMode),
      fs0,
      cwd0,
      fs2,
      stdout0,
      stdout2,
      stderr0,
      stderr2,
      exit,
      now
    );
    assert exists specMode: bv32 ::
        IOC.GetFileModeContractFields(
          fs0,
          Spec.MakeAbsolute(cwd0, cmd.referenceFile),
          true,
          true,
          specMode,
          0
        ) &&
        Spec.SpecBatchOutcome(
          cmd,
          Spec.SpecReferenceModePlan(specMode),
          fs0,
          cwd0,
          fs2,
          stdout0,
          stdout2,
          stderr0,
          stderr2,
          exit,
          now
        );
  }

  lemma BridgeExternalDomain(raw: Schema.ChmodCmdRaw)
    ensures Core.CoreExternalDomain(raw) == Spec.SpecExternalDomain(raw)
  {
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.ChmodCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    BridgeExternalDomain(raw);
    if !Spec.SpecExternalDomain(raw) {
      return;
    }
    var cmd := Schema.Command(raw);
    if cmd.seenReference {
      BridgeReferenceFailureEquivalent(cmd, old(io.fs()), old(io.cwd()));
    }
    if cmd.mode == Schema.ModeHelp {
      BridgeHelpText();
    } else if cmd.mode == Schema.ModeVersion {
      BridgeVersionText();
    } else if cmd.seenReference && cmd.diagnoseSurprises {
      BridgeCombineModeReferenceMessage();
    } else if |cmd.files| == 0 {
      BridgeMissingOperandMessage(cmd);
    } else if cmd.seenReference &&
              Core.CoreReferenceFailure(cmd, old(io.fs()), old(io.cwd())) {
      BridgeReferenceFailure(cmd, old(io.fs()), old(io.cwd()));
      BridgeReferenceFailureOutcome(
        cmd,
        old(io.fs()),
        old(io.cwd()),
        io.fs(),
        old(io.stdout()),
        io.stdout(),
        old(io.stderr()),
        io.stderr(),
        exit
      );
    } else if !cmd.seenReference && !Schema.IsValidModeExpr(cmd.modeExpr) {
      BridgeInvalidModeMessage(cmd.modeExpr);
    } else if cmd.recursive {
      BridgeUnsupportedRecursiveMessage();
    } else if cmd.seenReference {
      BridgeReferenceBatchOutcome(
        cmd,
        old(io.fs()),
        old(io.cwd()),
        io.fs(),
        old(io.stdout()),
        io.stdout(),
        old(io.stderr()),
        io.stderr(),
        exit,
        old(io.now())
      );
    } else {
      var umask := IOC.GetUmaskResultFields(old(io.props()));
      var corePlan := Core.CoreGeneralModePlan(cmd.modeExpr, umask);
      var specPlan := SpecModePlanOfCore(corePlan);
      ValidModeProgramSatisfiesRelation(cmd.modeExpr);
      assert Spec.SpecGeneralModePlanRelation(
          cmd.modeExpr, umask, specPlan
        ) by {
        assert exists changes: seq<Schema.ModeChange> ::
            Spec.SpecModeProgramRelation(cmd.modeExpr, changes) &&
            specPlan == Spec.SpecGeneralModePlan(changes, umask) by {
          ghost var changes := SpecChangesOfExpr(cmd.modeExpr);
        }
      }
      BridgeBatchOutcome(
        cmd,
        corePlan,
        old(io.fs()),
        old(io.cwd()),
        io.fs(),
        old(io.stdout()),
        io.stdout(),
        old(io.stderr()),
        io.stderr(),
        exit,
        old(io.now())
      );
      assert exists plan: Spec.SpecModePlan ::
          Spec.SpecGeneralModePlanRelation(cmd.modeExpr, umask, plan) &&
          Spec.SpecBatchOutcome(
            cmd,
            plan,
            old(io.fs()),
            old(io.cwd()),
            io.fs(),
            old(io.stdout()),
            io.stdout(),
            old(io.stderr()),
            io.stderr(),
            exit,
            old(io.now())
          ) by {
        ghost var plan := specPlan;
      }
    }
  }

}
