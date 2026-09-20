include "../../core/World.dfy"
include "../../core/Utf8.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "ChmodSchema.dfy"
include "ChmodQuoteSpec.dfy"

module ChmodSpec {
  import BenchWorld
  import BenchIO
  import IOContract
  import Utf8 = Utf8Semantics
  import Schema = ChmodSchema
  import Quote = ChmodQuoteSpec

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: chmod [OPTION]... MODE[,MODE]... FILE...\n"
    + "  or:  chmod [OPTION]... OCTAL-MODE FILE...\n"
    + "  or:  chmod [OPTION]... --reference=RFILE FILE...\n"
    + "Change the mode of each FILE to MODE.\n"
    + "With --reference, change the mode of each FILE to that of RFILE.\n"
    + "\n"
    + "  -c, --changes\n"
    + "         like verbose but report only when a change is made\n"
    + "  -f, --silent, --quiet\n"
    + "         suppress most error messages\n"
    + "  -v, --verbose\n"
    + "         output a diagnostic for every file processed\n"
    + "      --dereference\n"
    + "         affect the referent of each symbolic link,\n"
    + "         rather than the symbolic link itself\n"
    + "  -h, --no-dereference\n"
    + "         affect each symbolic link, rather than the referent\n"
    + "      --no-preserve-root\n"
    + "         do not treat '/' specially (the default)\n"
    + "      --preserve-root\n"
    + "         fail to operate recursively on '/'\n"
    + "      --reference=RFILE\n"
    + "         use RFILE's mode instead of specifying MODE values.\n"
    + "         RFILE is always dereferenced if a symbolic link.\n"
    + "  -R, --recursive\n"
    + "         change files and directories recursively\n"
    + "\n"
    + "The following options modify how a hierarchy is traversed when the -R\n"
    + "option is also specified.  If more than one is specified, only the final\n"
    + "one takes effect. -H is the default.\n"
    + "\n"
    + "  -H\n"
    + "         if a command line argument is a symlink to a directory, traverse it\n"
    + "  -L\n"
    + "         traverse every symbolic link to a directory encountered\n"
    + "  -P\n"
    + "         do not traverse any symbolic links\n"
    + "\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Each MODE is of the form '[ugoa]*([-+=]([rwxXst]*|[ugo]))+|[-+=][0-7]+'.\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/chmod>\n"
    + "or available locally via: info '(coreutils) chmod invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "chmod (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by David MacKenzie and Jim Meyering.\n"
  }

  function ErrnoTextSpec(err: int): string
  {
    if err == 2 then "No such file or directory"
    else if err == 13 then "Permission denied"
    else if err == 20 then "Not a directory"
    else if err == 21 then "Is a directory"
    else if err == 40 then "Too many levels of symbolic links"
    else "unknown error"
  }

  function MissingOperandMessageSpec(cmd: Schema.ChmodCmd): BenchWorld.Bytes
  {
    if cmd.modeExpr != "" && !cmd.diagnoseSurprises then
      "chmod: missing operand after " +
      Quote.SpecLocaleQuoteBytes(Utf8.Encode(cmd.modeExpr)) +
      "\nTry 'chmod --help' for more information.\n"
    else
      "chmod: missing operand\nTry 'chmod --help' for more information.\n"
  }

  function InvalidModeMessageSpec(modeExpr: string): BenchWorld.Bytes
  {
    "chmod: invalid mode: " + Quote.SpecLocaleQuoteBytes(Utf8.Encode(modeExpr)) +
    "\nTry 'chmod --help' for more information.\n"
  }

  function ReferenceErrorMessageSpec(path: string, err: string): BenchWorld.Bytes
  {
    "chmod: failed to get attributes of " + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    ": " + err + "\n"
  }

  function GettingNewAttributesMessageSpec(path: string, err: string): BenchWorld.Bytes
  {
    "chmod: getting new attributes of " +
    Quote.SpecQuoteAfBytes(Utf8.Encode(path)) + ": " + err + "\n"
  }

  function CombineModeReferenceMessageSpec(): BenchWorld.Bytes
  {
    "chmod: cannot combine mode and --reference options\nTry 'chmod --help' for more information.\n"
  }

  function UnsupportedRecursiveMessageSpec(): BenchWorld.Bytes
  {
    "chmod: recursive traversal is outside this benchmark slice\n"
  }

  function UnsupportedMultiFileMessageSpec(): BenchWorld.Bytes
  {
    "chmod: multi-file batches are outside this benchmark slice\n"
  }

  function ChangeErrorMessageSpec(path: string, err: string): BenchWorld.Bytes
  {
    "chmod: changing permissions of " + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    ": " + err + "\n"
  }

  function AccessErrorMessageSpec(path: string, err: string): BenchWorld.Bytes
  {
    "chmod: cannot access " + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    ": " + err + "\n"
  }

  function DanglingSymlinkMessageSpec(path: string): BenchWorld.Bytes
  {
    "chmod: cannot operate on dangling symlink " +
    Quote.SpecQuoteAfBytes(Utf8.Encode(path)) + "\n"
  }

  function CannotDereferenceMessageSpec(path: string, err: int): BenchWorld.Bytes
  {
    "chmod: cannot dereference " + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    ": " + ErrnoTextSpec(err) + "\n"
  }

  function NeitherChangedMessageSpec(path: string): BenchWorld.Bytes
  {
    "neither symbolic link " + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    " nor referent has been changed\n"
  }

  lemma AccessErrorMessagePlainSpec(path: string, err: string)
    requires Utf8.Encode(path) == path
    requires Quote.SpecQuoteAfBytes(path) == "'" + path + "'"
    ensures AccessErrorMessageSpec(path, err) ==
            "chmod: cannot access '" + path + "': " + err + "\n"
  {
  }

  lemma DanglingSymlinkMessagePlainSpec(path: string)
    requires Utf8.Encode(path) == path
    requires Quote.SpecQuoteAfBytes(path) == "'" + path + "'"
    ensures DanglingSymlinkMessageSpec(path) ==
            "chmod: cannot operate on dangling symlink '" + path + "'\n"
  {
  }

  function SpecOctDigitChar(n: int): char
  {
    if n == 0 then '0'
    else if n == 1 then '1'
    else if n == 2 then '2'
    else if n == 3 then '3'
    else if n == 4 then '4'
    else if n == 5 then '5'
    else if n == 6 then '6'
    else '7'
  }

  function SpecOctalText(mode: bv32): BenchWorld.Bytes
  {
    [SpecOctDigitChar(((mode >> 9) & (7 as bv32)) as int)] +
    [SpecOctDigitChar(((mode >> 6) & (7 as bv32)) as int)] +
    [SpecOctDigitChar(((mode >> 3) & (7 as bv32)) as int)] +
    [SpecOctDigitChar((mode & (7 as bv32)) as int)]
  }

  function SpecPermissionText(mode: bv32): BenchWorld.Bytes
  {
    [if (mode & Schema.S_IRUSR) != 0 as bv32 then 'r' else '-'] +
    [if (mode & Schema.S_IWUSR) != 0 as bv32 then 'w' else '-'] +
    [if (mode & Schema.S_ISUID) != 0 as bv32 then
       if (mode & Schema.S_IXUSR) != 0 as bv32 then 's' else 'S'
     else if (mode & Schema.S_IXUSR) != 0 as bv32 then 'x' else '-'] +
    [if (mode & Schema.S_IRGRP) != 0 as bv32 then 'r' else '-'] +
    [if (mode & Schema.S_IWGRP) != 0 as bv32 then 'w' else '-'] +
    [if (mode & Schema.S_ISGID) != 0 as bv32 then
       if (mode & Schema.S_IXGRP) != 0 as bv32 then 's' else 'S'
     else if (mode & Schema.S_IXGRP) != 0 as bv32 then 'x' else '-'] +
    [if (mode & Schema.S_IROTH) != 0 as bv32 then 'r' else '-'] +
    [if (mode & Schema.S_IWOTH) != 0 as bv32 then 'w' else '-'] +
    [if (mode & Schema.S_ISVTX) != 0 as bv32 then
       if (mode & Schema.S_IXOTH) != 0 as bv32 then 't' else 'T'
     else if (mode & Schema.S_IXOTH) != 0 as bv32 then 'x' else '-']
  }

  function SpecModeDisplay(mode: bv32): BenchWorld.Bytes
  {
    SpecOctalText(mode) + " (" + SpecPermissionText(mode) + ")"
  }

  function ChangedMessageSpec(path: string, before: bv32, after: bv32): BenchWorld.Bytes
  {
    "mode of " + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    " changed from " + SpecModeDisplay(before) +
    " to " + SpecModeDisplay(after) + "\n"
  }

  function FailedChangeMessageSpec(
    path: string,
    before: bv32,
    desired: bv32
  ): BenchWorld.Bytes
  {
    "failed to change mode of " + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    " from " + SpecModeDisplay(before) +
    " to " + SpecModeDisplay(desired) + "\n"
  }

  function RetainedMessageSpec(path: string, mode: bv32): BenchWorld.Bytes
  {
    "mode of " + Quote.SpecQuoteAfBytes(Utf8.Encode(path)) +
    " retained as " + SpecModeDisplay(mode) + "\n"
  }

  function AccessFailureMessageSpec(path: string): BenchWorld.Bytes
  {
    Quote.SpecQuoteAfBytes(Utf8.Encode(path)) + " could not be accessed\n"
  }

  function SurpriseModeMessageSpec(path: string, actual: bv32, naive: bv32): BenchWorld.Bytes
  {
    "chmod: " + Quote.SpecQuoteFBytes(Utf8.Encode(path)) +
    ": new permissions are " + SpecPermissionText(actual) +
    ", not " + SpecPermissionText(naive) + "\n"
  }

  function MakeAbsolute(cwd: BenchWorld.Path, path: BenchWorld.Path): BenchWorld.Path
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

  function ShouldDereference(cmd: Schema.ChmodCmd): bool
  {
    cmd.dereferenceMode != 0
  }

  function SpecUsesPhysicalTopLevelMetadata(cmd: Schema.ChmodCmd): bool
  {
    !cmd.recursive && cmd.dereferenceMode == -1 && cmd.traversalMode == 0
  }

  function SpecUsesExplicitPhysicalDereference(cmd: Schema.ChmodCmd): bool
  {
    !cmd.recursive && cmd.dereferenceMode == 1 && cmd.traversalMode == 0
  }

  function SpecUsesFollowedTopLevelNoDereference(cmd: Schema.ChmodCmd): bool
  {
    !cmd.recursive && cmd.dereferenceMode == 0 && cmd.traversalMode != 0
  }

  function SpecIsDanglingSymlinkFailure(isSymlink: bool, err: int): bool
  {
    isSymlink && err == 2
  }

  function SpecPathIsDanglingSymlinkFailure(
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
      SpecIsDanglingSymlinkFailure(
        match BenchWorld.FsNodeAt(fs, resolved)
        case Symlink(_, _, _, _) => true
        case _ => false,
        err
      )
  }

  function SupportedOctalMode(expr: string): bool
  {
    |expr| > 0 && BenchWorld.IsOctalDigit(expr[0]) &&
    BenchWorld.AllOctalDigits(expr, 0) && BenchWorld.OctalValue(expr, 0, 0) <= 4095
  }

  function OctalMode(expr: string): bv32
    requires SupportedOctalMode(expr)
  {
    BenchWorld.NormalizeMode(BenchWorld.ToBv32(BenchWorld.OctalValue(expr, 0, 0)))
  }

  const SPEC_READ_MASK: bv32 := Schema.READ_MASK
  const SPEC_WRITE_MASK: bv32 := Schema.WRITE_MASK
  const SPEC_EXEC_MASK: bv32 := Schema.EXEC_MASK

  function SpecCopyExistingValue(value: bv32, current: bv32): bv32
  {
    var isolated := value & current;
    isolated |
    (if (isolated & SPEC_READ_MASK) != 0 as bv32 then SPEC_READ_MASK else 0 as bv32) |
    (if (isolated & SPEC_WRITE_MASK) != 0 as bv32 then SPEC_WRITE_MASK else 0 as bv32) |
    (if (isolated & SPEC_EXEC_MASK) != 0 as bv32 then SPEC_EXEC_MASK else 0 as bv32)
  }

  function SpecInvertModeBits(value: bv32): bv32
  {
    Schema.CHMOD_MODE_BITS ^ value
  }

  function SpecOmittedChangeBits(isDir: bool, mentioned: bv32): bv32
  {
    (if isDir then Schema.S_ISUID | Schema.S_ISGID else 0 as bv32) &
    SpecInvertModeBits(mentioned)
  }

  function SpecChangeAffectedMask(affected: bv32, umask: bv32): bv32
  {
    if affected != 0 as bv32 then affected else SpecInvertModeBits(umask)
  }

  function SpecChangeValue(current: bv32, isDir: bool, change: Schema.ModeChange): bv32
  {
    match change.flag
    case ModeCopyExisting => SpecCopyExistingValue(change.value, current)
    case ModeXIfAnyX =>
      if (current & SPEC_EXEC_MASK) != 0 as bv32 || isDir then
        change.value | SPEC_EXEC_MASK
      else
        change.value
    case ModeOrdinary => change.value
  }

  function SpecMaskedChangeValue(
    current: bv32,
    isDir: bool,
    umask: bv32,
    change: Schema.ModeChange
  ): bv32
  {
    SpecChangeValue(current, isDir, change) &
    SpecChangeAffectedMask(change.affected, umask) &
    SpecInvertModeBits(SpecOmittedChangeBits(isDir, change.mentioned))
  }

  function SpecPreservedAffectedBits(affected: bv32): bv32
  {
    if affected != 0 as bv32 then SpecInvertModeBits(affected) else 0 as bv32
  }

  function SpecPreservedChangeBits(isDir: bool, change: Schema.ModeChange): bv32
  {
    SpecPreservedAffectedBits(change.affected) |
    SpecOmittedChangeBits(isDir, change.mentioned)
  }

  function SpecApplyChange(
    current: bv32,
    isDir: bool,
    umask: bv32,
    change: Schema.ModeChange
  ): bv32
  {
    var masked := SpecMaskedChangeValue(current, isDir, umask, change);
    if change.op == '=' then
      BenchWorld.NormalizeMode((current & SpecPreservedChangeBits(isDir, change)) | masked)
    else if change.op == '+' then
      BenchWorld.NormalizeMode(current | masked)
    else
      BenchWorld.NormalizeMode(current & SpecInvertModeBits(masked))
  }

  opaque ghost predicate SpecModeChangesRelation(
    changes: seq<Schema.ModeChange>,
    before: bv32,
    isDir: bool,
    umask: bv32,
    after: bv32
  )
    decreases |changes|
  {
    if |changes| == 0 then
      after == before
    else
      SpecModeChangesRelation(
        changes[1..],
        SpecApplyChange(before, isDir, umask, changes[0]),
        isDir,
        umask,
        after
      )
  }

  ghost predicate SpecWhoRelation(
    expr: string,
    i: nat,
    accumulated: bv32,
    affected: bv32,
    next: nat
  )
    requires i <= |expr|
    decreases |expr| - i
  {
    next <= |expr| &&
    if i == |expr| || Schema.ModeIsOp(expr[i]) then
      affected == accumulated && next == i
    else
      Schema.ModeIsWhoChar(expr[i]) &&
      SpecWhoRelation(
        expr,
        i + 1,
        accumulated | Schema.WhoMask(expr[i]),
        affected,
        next
      )
  }

  ghost predicate SpecOctalRunRelation(
    expr: string,
    i: nat,
    accumulated: int,
    value: int,
    next: nat
  )
    requires i <= |expr|
    decreases |expr| - i
  {
    next <= |expr| &&
    if i == |expr| || !BenchWorld.IsOctalDigit(expr[i]) then
      value == accumulated && next == i
    else
      SpecOctalRunRelation(
        expr,
        i + 1,
        accumulated * 8 + BenchWorld.CharToDigit(expr[i]),
        value,
        next
      )
  }

  ghost predicate SpecPermsRelation(
    expr: string,
    i: nat,
    accumulated: bv32,
    accumulatedFlag: Schema.ModeFlag,
    value: bv32,
    flag: Schema.ModeFlag,
    next: nat
  )
    requires i <= |expr|
    decreases |expr| - i
  {
    next <= |expr| &&
    if i == |expr| ||
       !(expr[i] == 'r' || expr[i] == 'w' || expr[i] == 'x' ||
         expr[i] == 'X' || expr[i] == 's' || expr[i] == 't') then
      value == accumulated && flag == accumulatedFlag && next == i
    else
      var nextValue :=
        if expr[i] == 'r' then accumulated | Schema.READ_MASK
        else if expr[i] == 'w' then accumulated | Schema.WRITE_MASK
        else if expr[i] == 'x' then accumulated | Schema.EXEC_MASK
        else if expr[i] == 's' then accumulated | (Schema.S_ISUID | Schema.S_ISGID)
        else if expr[i] == 't' then accumulated | Schema.S_ISVTX
        else accumulated;
      var nextFlag :=
        if expr[i] == 'X' then Schema.FlagWithX(accumulatedFlag)
        else accumulatedFlag;
      SpecPermsRelation(
        expr,
        i + 1,
        nextValue,
        nextFlag,
        value,
        flag,
        next
      )
  }

  ghost predicate SpecOneChangeRelation(
    expr: string,
    i: nat,
    affected: bv32,
    change: Schema.ModeChange,
    next: nat
  )
    requires i <= |expr|
  {
    next <= |expr| &&
    i < |expr| &&
    Schema.ModeIsOp(expr[i]) &&
    var op := expr[i];
    var j := i + 1;
    if j == |expr| then
      change == Schema.ModeChange(
        op,
        Schema.ModeOrdinary,
        affected,
        0 as bv32,
        Schema.DefaultMentioned(affected, 0 as bv32)
      ) &&
      next == j
    else if BenchWorld.IsOctalDigit(expr[j]) then
      affected == 0 as bv32 &&
      exists value: int, octalNext: nat ::
        SpecOctalRunRelation(expr, j, 0, value, octalNext) &&
        value <= 4095 &&
        (octalNext == |expr| || expr[octalNext] == ',') &&
        change == Schema.ModeChange(
          op,
          Schema.ModeOrdinary,
          Schema.CHMOD_MODE_BITS,
          BenchWorld.NormalizeMode(BenchWorld.ToBv32(value)),
          Schema.CHMOD_MODE_BITS
        ) &&
        next == octalNext
    else if expr[j] == 'u' || expr[j] == 'g' || expr[j] == 'o' then
      var value := Schema.CopySourceMask(expr[j]);
      change == Schema.ModeChange(
        op,
        Schema.ModeCopyExisting,
        affected,
        value,
        Schema.DefaultMentioned(affected, value)
      ) &&
      next == j + 1
    else
      exists value: bv32, flag: Schema.ModeFlag, permsNext: nat
        {:trigger SpecPermsRelation(
          expr, j, 0 as bv32, Schema.ModeOrdinary,
          value, flag, permsNext
        )} ::
        SpecPermsRelation(
          expr,
          j,
          0 as bv32,
          Schema.ModeOrdinary,
          value,
          flag,
          permsNext
        ) &&
        change == Schema.ModeChange(
          op,
          flag,
          affected,
          value,
          Schema.DefaultMentioned(affected, value)
        ) &&
        next == permsNext
  }

  ghost predicate SpecOpSequenceRelation(
    expr: string,
    i: nat,
    affected: bv32,
    changes: seq<Schema.ModeChange>,
    next: nat
  )
    requires i <= |expr|
    decreases |expr| - i
  {
    next <= |expr| &&
    exists change: Schema.ModeChange, changeNext: nat ::
      SpecOneChangeRelation(expr, i, affected, change, changeNext) &&
      changeNext > i &&
      if changeNext < |expr| && Schema.ModeIsOp(expr[changeNext]) then
        exists rest: seq<Schema.ModeChange> ::
          SpecOpSequenceRelation(expr, changeNext, affected, rest, next) &&
          changes == [change] + rest
      else
        changes == [change] && next == changeNext
  }

  ghost predicate SpecSymbolicChangesFromRelation(
    expr: string,
    i: nat,
    changes: seq<Schema.ModeChange>,
    next: nat
  )
    requires i <= |expr|
    decreases |expr| - i
  {
    next <= |expr| &&
    i < |expr| &&
    exists affected: bv32, whoNext: nat,
      clause: seq<Schema.ModeChange>, clauseNext: nat ::
      SpecWhoRelation(expr, i, 0 as bv32, affected, whoNext) &&
      SpecOpSequenceRelation(expr, whoNext, affected, clause, clauseNext) &&
      clauseNext >= i &&
      if clauseNext < |expr| && expr[clauseNext] == ',' then
        exists rest: seq<Schema.ModeChange> ::
          SpecSymbolicChangesFromRelation(
            expr,
            clauseNext + 1,
            rest,
            next
          ) &&
          changes == clause + rest
      else
        clauseNext == |expr| &&
        changes == clause &&
        next == clauseNext
  }

  ghost predicate SpecModeProgramRelation(
    expr: string,
    changes: seq<Schema.ModeChange>
  )
  {
    |expr| > 0 &&
    if BenchWorld.IsOctalDigit(expr[0]) then
      BenchWorld.AllOctalDigits(expr, 0) &&
      BenchWorld.OctalValue(expr, 0, 0) <= 4095 &&
      var mode := BenchWorld.NormalizeMode(
                    BenchWorld.ToBv32(BenchWorld.OctalValue(expr, 0, 0))
                  );
      var mentioned :=
        if |expr| < 5 then
          (mode & (Schema.S_ISUID | Schema.S_ISGID)) |
          Schema.S_ISVTX | Schema.S_IRWXUGO
        else
          Schema.CHMOD_MODE_BITS;
      changes == [
        Schema.ModeChange(
          '=',
          Schema.ModeOrdinary,
          Schema.CHMOD_MODE_BITS,
          mode,
          mentioned
        )
      ]
    else
      SpecSymbolicChangesFromRelation(expr, 0, changes, |expr|)
  }

  datatype SpecModePlan =
    | SpecGeneralModePlan(changes: seq<Schema.ModeChange>, umask: bv32)
    | SpecReferenceModePlan(mode: bv32)

  ghost predicate SpecGeneralModePlanRelation(
    expr: string,
    umask: bv32,
    plan: SpecModePlan
  )
  {
    exists changes: seq<Schema.ModeChange> ::
      SpecModeProgramRelation(expr, changes) &&
      plan == SpecGeneralModePlan(changes, umask)
  }

  datatype SpecPathStatus =
    | SpecPathChanged(before: bv32, after: bv32)
    | SpecPathRetained(mode: bv32)
    | SpecPathAccessFailed(err: int)
    | SpecPathChangeFailed(before: bv32, desired: bv32, err: int)
    | SpecPathSurprise(before: bv32, after: bv32, naive: bv32)

  datatype SpecPathResult = SpecPathResult(
    fs: BenchWorld.FileSystem,
    stdoutChunk: BenchWorld.Bytes,
    stderrChunk: BenchWorld.Bytes,
    ok: bool,
    status: SpecPathStatus
  )

  function SpecNodeIsDirectory(node: BenchWorld.FsNode): bool
  {
    match node
    case Directory(_, _, _) => true
    case _ => false
  }

  ghost predicate SpecPlannedModeRelation(
    plan: SpecModePlan,
    before: bv32,
    isDir: bool,
    after: bv32
  )
  {
    match plan
    case SpecGeneralModePlan(changes, umask) =>
      SpecModeChangesRelation(
        changes,
        BenchWorld.NormalizeMode(before),
        isDir,
        umask,
        after
      )
    case SpecReferenceModePlan(mode) =>
      after == BenchWorld.NormalizeMode(mode)
  }

  function SpecSuccessStdout(
    cmd: Schema.ChmodCmd,
    path: string,
    before: bv32,
    after: bv32
  ): BenchWorld.Bytes
  {
    if cmd.verbose then
      if before == after then RetainedMessageSpec(path, after)
      else ChangedMessageSpec(path, before, after)
    else if cmd.changes && before != after then
      ChangedMessageSpec(path, before, after)
    else
      []
  }

  ghost predicate SpecNaiveModeRelation(
    plan: SpecModePlan,
    before: bv32,
    isDir: bool,
    naive: bv32
  )
  {
    match plan
    case SpecGeneralModePlan(changes, _) =>
      SpecModeChangesRelation(
        changes,
        BenchWorld.NormalizeMode(before),
        isDir,
        0 as bv32,
        naive
      )
    case SpecReferenceModePlan(mode) =>
      naive == BenchWorld.NormalizeMode(mode)
  }

  function SpecDiagnoseSurpriseForNaive(
    cmd: Schema.ChmodCmd,
    after: bv32,
    naive: bv32
  ): bool
  {
    cmd.diagnoseSurprises && (after & SpecInvertModeBits(naive)) != 0 as bv32
  }

  function SpecPostChangeLookupNeeded(
    cmd: Schema.ChmodCmd,
    after: bv32
  ): bool
  {
    (cmd.verbose || cmd.changes) &&
    (after & Schema.SPECIAL_BITS) != 0 as bv32
  }

  function SpecSuccessfulChangeResultForNaive(
    cmd: Schema.ChmodCmd,
    path: string,
    actual: BenchWorld.Path,
    follow: bool,
    before: bv32,
    after: bv32,
    naive: bv32,
    fs: BenchWorld.FileSystem
  ): SpecPathResult
  {
    if SpecPostChangeLookupNeeded(cmd, after) then
      match IOContract.ResolvePathForMetadataFields(fs, actual, follow)
      case Err(_) =>
        var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
        var surprise := SpecDiagnoseSurpriseForNaive(cmd, after, naive);
        SpecPathResult(
          fs,
          if cmd.verbose then RetainedMessageSpec(path, after) else [],
          (if cmd.silent then []
           else GettingNewAttributesMessageSpec(path, ErrnoTextSpec(err))) +
          (if surprise then SurpriseModeMessageSpec(path, after, naive) else []),
          !surprise,
          SpecPathRetained(after)
        )
      case Ok(target) =>
        if !BenchWorld.FsContainsPath(fs, target) then
          var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
          var surprise := SpecDiagnoseSurpriseForNaive(cmd, after, naive);
          SpecPathResult(
            fs,
            if cmd.verbose then RetainedMessageSpec(path, after) else [],
            (if cmd.silent then []
             else GettingNewAttributesMessageSpec(path, ErrnoTextSpec(err))) +
            (if surprise then SurpriseModeMessageSpec(path, after, naive) else []),
            !surprise,
            SpecPathRetained(after)
          )
        else
          var observed := BenchWorld.NodeMode(BenchWorld.FsNodeAt(fs, target));
          var surprise := SpecDiagnoseSurpriseForNaive(cmd, observed, naive);
          SpecPathResult(
            fs,
            SpecSuccessStdout(cmd, path, before, observed),
            if surprise then SurpriseModeMessageSpec(path, observed, naive) else [],
            !surprise,
            if surprise then SpecPathSurprise(before, observed, naive)
            else if before == observed then SpecPathRetained(observed)
            else SpecPathChanged(before, observed)
          )
    else
      var surprise := SpecDiagnoseSurpriseForNaive(cmd, after, naive);
      SpecPathResult(
        fs,
        SpecSuccessStdout(cmd, path, before, after),
        if surprise then SurpriseModeMessageSpec(path, after, naive) else [],
        !surprise,
        if surprise then SpecPathSurprise(before, after, naive)
        else if before == after then SpecPathRetained(after)
        else SpecPathChanged(before, after)
      )
  }

  ghost predicate SpecSuccessfulChangeResultRelation(
    cmd: Schema.ChmodCmd,
    plan: SpecModePlan,
    path: string,
    actual: BenchWorld.Path,
    follow: bool,
    before: bv32,
    after: bv32,
    isDir: bool,
    fs: BenchWorld.FileSystem,
    result: SpecPathResult
  )
  {
    exists naive: bv32 ::
      SpecNaiveModeRelation(plan, before, isDir, naive) &&
      result == SpecSuccessfulChangeResultForNaive(
        cmd,
        path,
        actual,
        follow,
        before,
        after,
        naive,
        fs
      )
  }

  function SpecModeSetFs(
    fs: BenchWorld.FileSystem,
    follow: bool,
    target: BenchWorld.Path,
    desired: bv32,
    now: int
  ): BenchWorld.FileSystem
    requires BenchWorld.FsContainsPath(fs, target)
  {
    if SpecModeSetSuppressed(fs, target, follow) then
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

  function SpecModeSetSuppressed(
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

  function SpecNoDereferenceSymlink(
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

  function SpecPathAccessFailureResult(
    cmd: Schema.ChmodCmd,
    fs: BenchWorld.FileSystem,
    path: string,
    actual: BenchWorld.Path,
    follow: bool,
    err: int
  ): SpecPathResult
  {
    SpecPathResult(
      fs,
      if cmd.verbose then AccessFailureMessageSpec(path) else [],
      if cmd.silent then []
      else if SpecUsesExplicitPhysicalDereference(cmd) &&
              SpecNoDereferenceSymlink(fs, actual, false) then
        CannotDereferenceMessageSpec(path, err)
      else if SpecPathIsDanglingSymlinkFailure(fs, actual, follow, err) then
        DanglingSymlinkMessageSpec(path)
      else AccessErrorMessageSpec(path, ErrnoTextSpec(err)),
      false,
      SpecPathAccessFailed(err)
    )
  }

  ghost predicate SpecPathStepForResolutionRelation(
    cmd: Schema.ChmodCmd,
    plan: SpecModePlan,
    cwd: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    path: string,
    resolution: BenchWorld.Result<BenchWorld.Path>,
    result: SpecPathResult,
    now: int
  )
  {
    var actual := MakeAbsolute(cwd, path);
    var follow := ShouldDereference(cmd);
    match resolution
    case Err(_) =>
      var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
      result == SpecPathAccessFailureResult(cmd, fs, path, actual, follow, err)
    case Ok(target) =>
      if !BenchWorld.FsContainsPath(fs, target) then
        var err := IOContract.MetadataFailureErrFields(fs, actual, follow);
        result == SpecPathAccessFailureResult(cmd, fs, path, actual, follow, err)
      else
        var before := BenchWorld.NodeMode(BenchWorld.FsNodeAt(fs, target));
        if SpecNoDereferenceSymlink(fs, actual, follow) then
          if SpecUsesFollowedTopLevelNoDereference(cmd) then
            var followed := IOContract.ResolvePathForMetadataFields(fs, actual, true);
            var followedOk :=
              match followed
              case Err(_) => false
              case Ok(followedTarget) =>
                BenchWorld.FsContainsPath(fs, followedTarget);
            var err := IOContract.MetadataFailureErrFields(fs, actual, true);
            if !followedOk && err != 2 then
              result == SpecPathAccessFailureResult(
                cmd, fs, path, actual, true, err
              )
            else
              result == SpecPathResult(
                fs,
                if cmd.verbose then NeitherChangedMessageSpec(path) else [],
                [],
                true,
                SpecPathRetained(before)
              )
          else
            result == SpecPathResult(
              fs,
              if cmd.verbose then NeitherChangedMessageSpec(path) else [],
              [],
              true,
              SpecPathRetained(before)
            )
        else
          var isDir := SpecNodeIsDirectory(BenchWorld.FsNodeAt(fs, target));
          exists desired: bv32 ::
            SpecPlannedModeRelation(plan, before, isDir, desired) &&
            var fs2 := SpecModeSetFs(fs, follow, target, desired, now);
            var after :=
              if SpecModeSetSuppressed(fs, target, follow) then before
              else BenchWorld.NormalizeMode(desired);
            SpecSuccessfulChangeResultRelation(
              cmd,
              plan,
              path,
              actual,
              follow,
              before,
              after,
              isDir,
              fs2,
              result
            )
  }

  ghost predicate SpecPathStepRelation(
    cmd: Schema.ChmodCmd,
    plan: SpecModePlan,
    cwd: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    path: string,
    result: SpecPathResult,
    now: int
  )
  {
    var actual := MakeAbsolute(cwd, path);
    if SpecUsesPhysicalTopLevelMetadata(cmd) then
      match IOContract.ResolvePathForMetadataFields(fs, actual, false)
      case Err(_) =>
        var err := IOContract.MetadataFailureErrFields(fs, actual, false);
        result == SpecPathAccessFailureResult(
          cmd, fs, path, actual, false, err
        )
      case Ok(metadataTarget) =>
        if !BenchWorld.FsContainsPath(fs, metadataTarget) then
          var err := IOContract.MetadataFailureErrFields(fs, actual, false);
          result == SpecPathAccessFailureResult(
            cmd, fs, path, actual, false, err
          )
        else
          var node := BenchWorld.FsNodeAt(fs, metadataTarget);
          var before := BenchWorld.NodeMode(node);
          var isDir := SpecNodeIsDirectory(node);
          match IOContract.ResolvePathForMetadataFields(fs, actual, true)
          case Err(_) =>
            exists desired: bv32 ::
              SpecPlannedModeRelation(plan, before, isDir, desired) &&
              var err := IOContract.MetadataFailureErrFields(fs, actual, true);
              result == SpecPathResult(
                fs,
                if cmd.verbose then FailedChangeMessageSpec(path, before, desired) else [],
                if cmd.silent then []
                else ChangeErrorMessageSpec(path, ErrnoTextSpec(err)),
                false,
                SpecPathChangeFailed(before, desired, err)
              )
          case Ok(changeTarget) =>
            exists desired: bv32 ::
              SpecPlannedModeRelation(plan, before, isDir, desired) &&
              if !BenchWorld.FsContainsPath(fs, changeTarget) then
                var err := IOContract.MetadataFailureErrFields(fs, actual, true);
                result == SpecPathResult(
                  fs,
                  if cmd.verbose then
                    FailedChangeMessageSpec(path, before, desired)
                  else [],
                  if cmd.silent then []
                  else ChangeErrorMessageSpec(path, ErrnoTextSpec(err)),
                  false,
                  SpecPathChangeFailed(before, desired, err)
                )
              else
                var fs2 := SpecModeSetFs(
                  fs, true, changeTarget, desired, now
                );
                var after := BenchWorld.NormalizeMode(desired);
                SpecSuccessfulChangeResultRelation(
                  cmd,
                  plan,
                  path,
                  actual,
                  true,
                  before,
                  after,
                  isDir,
                  fs2,
                  result
                )
    else
      SpecPathStepForResolutionRelation(
        cmd,
        plan,
        cwd,
        fs,
        path,
        IOContract.ResolvePathForMetadataFields(
          fs, actual, ShouldDereference(cmd)
        ),
        result,
        now
      )
  }

  datatype SpecBatchTrace =
    | SpecBatchEnd(
        fs: BenchWorld.FileSystem,
        stdout: BenchWorld.Bytes,
        stderr: BenchWorld.Bytes,
        allOk: bool
      )
    | SpecBatchNext(
        fs: BenchWorld.FileSystem,
        stdout: BenchWorld.Bytes,
        stderr: BenchWorld.Bytes,
        allOk: bool,
        rest: SpecBatchTrace
      )

  ghost predicate SpecBatchTraceRelation(
    files: seq<string>,
    cmd: Schema.ChmodCmd,
    plan: SpecModePlan,
    cwd: BenchWorld.Path,
    fs0: BenchWorld.FileSystem,
    stdout0: BenchWorld.Bytes,
    stderr0: BenchWorld.Bytes,
    allOk0: bool,
    fs2: BenchWorld.FileSystem,
    stdout2: BenchWorld.Bytes,
    stderr2: BenchWorld.Bytes,
    allOk2: bool,
    trace: SpecBatchTrace,
    now: int
  )
    decreases |files|
  {
    if |files| == 0 then
      trace == SpecBatchEnd(fs0, stdout0, stderr0, allOk0) &&
      fs2 == fs0 &&
      stdout2 == stdout0 &&
      stderr2 == stderr0 &&
      allOk2 == allOk0
    else
      exists step: SpecPathResult ::
        SpecPathStepRelation(cmd, plan, cwd, fs0, files[0], step, now) &&
        trace.SpecBatchNext? &&
        trace.fs == fs0 &&
        trace.stdout == stdout0 &&
        trace.stderr == stderr0 &&
        trace.allOk == allOk0 &&
        SpecBatchTraceRelation(
          files[1..],
          cmd,
          plan,
          cwd,
          step.fs,
          stdout0 + step.stdoutChunk,
          stderr0 + step.stderrChunk,
          allOk0 && step.ok,
          fs2,
          stdout2,
          stderr2,
          allOk2,
          trace.rest,
          now
        )
  }

  ghost predicate SpecBatchOutcome(
    cmd: Schema.ChmodCmd,
    plan: SpecModePlan,
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
    exists trace: SpecBatchTrace, allOk: bool ::
      SpecBatchTraceRelation(
        cmd.files,
        cmd,
        plan,
        cwd0,
        fs0,
        stdout0,
        stderr0,
        true,
        fs2,
        stdout2,
        stderr2,
        allOk,
        trace,
        now
      ) &&
      exit == (if allOk then 0 else 1)
  }

  ghost predicate SpecReferenceFailure(
    cmd: Schema.ChmodCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path
  )
  {
    exists mode: bv32, err: int ::
      IOContract.GetFileModeContractFields(
        fs,
        MakeAbsolute(cwd, cmd.referenceFile),
        true,
        false,
        mode,
        err
      )
  }

  ghost predicate SpecReferenceFailureOutcome(
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
        MakeAbsolute(cwd0, cmd.referenceFile),
        true,
        false,
        mode,
        err
      ) &&
      fs2 == fs0 && stdout2 == stdout0 &&
      stderr2 == stderr0 + ReferenceErrorMessageSpec(
        cmd.referenceFile,
        ErrnoTextSpec(err)
      ) && exit == 1
  }

  ghost predicate SpecReferenceBatchOutcome(
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
        MakeAbsolute(cwd0, cmd.referenceFile),
        true,
        true,
        refMode,
        0
      ) &&
      SpecBatchOutcome(
        cmd,
        SpecReferenceModePlan(refMode),
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

  // The normalized external world represents argv and paths as NUL-free Unicode scalars.
  predicate SpecExternalDomain(raw: Schema.ChmodCmdRaw)
  {
    var cmd := Schema.Command(raw);
    Utf8.ValidExternalText(cmd.modeExpr) &&
    Utf8.ValidExternalText(cmd.referenceFile) &&
    forall i :: 0 <= i < |cmd.files| ==>
                  Utf8.ValidExternalText(cmd.files[i])
  }

  twostate predicate Spec(raw: Schema.ChmodCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    !SpecExternalDomain(raw) ||
    (if cmd.mode == Schema.ModeHelp then
       io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) + HelpTextSpec() && io.stderr() == old(io.stderr()) && exit == 0
     else if cmd.mode == Schema.ModeVersion then
       io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) + VersionTextSpec() && io.stderr() == old(io.stderr()) && exit == 0
     else if cmd.seenReference && cmd.diagnoseSurprises then
       io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) && io.stderr() == old(io.stderr()) + CombineModeReferenceMessageSpec() && exit == 1
     else if |cmd.files| == 0 then
       io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) && io.stderr() == old(io.stderr()) + MissingOperandMessageSpec(cmd) && exit == 1
     else if cmd.seenReference &&
             SpecReferenceFailure(cmd, old(io.fs()), old(io.cwd())) then
       SpecReferenceFailureOutcome(
         cmd, old(io.fs()), old(io.cwd()), io.fs(),
         old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(), exit
       )
     else if !cmd.seenReference && !Schema.IsValidModeExpr(cmd.modeExpr) then
       io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) && io.stderr() == old(io.stderr()) + InvalidModeMessageSpec(cmd.modeExpr) && exit == 1
     else if cmd.recursive then
       io.fs() == old(io.fs()) && io.stdout() == old(io.stdout()) && io.stderr() == old(io.stderr()) + UnsupportedRecursiveMessageSpec() && exit == 1
     else if cmd.seenReference then
       SpecReferenceBatchOutcome(
         cmd, old(io.fs()), old(io.cwd()), io.fs(),
         old(io.stdout()), io.stdout(), old(io.stderr()), io.stderr(), exit,
         old(io.now())
       )
     else
       exists plan: SpecModePlan ::
         SpecGeneralModePlanRelation(
           cmd.modeExpr,
           IOContract.GetUmaskResultFields(old(io.props())),
           plan
         ) &&
         SpecBatchOutcome(
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
         ))
  }

}
