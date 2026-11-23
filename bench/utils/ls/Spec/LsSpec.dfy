include "../../../core/Errno.dfy"
include "../../../core/World.dfy"
include "../../../core/IO.dfy"
include "../../../core/IOContract.dfy"
include "../../../core/StringEscaping.dfy"
include "LsSchema.dfy"
include "LsTime.dfy"
include "LsNativeSpec.dfy"
include "LsNativeObservationSpec.dfy"
include "LsNativeDirectorySpec.dfy"

module LsMaximumModel {
  export provides MaximumWidth

  lemma MaximumExists(values: set<nat>)
    requires values != {}
    ensures exists maximum: nat :: maximum in values && (forall value: nat | value in values :: value <= maximum)
    decreases |values|
  {
    ghost var member :| member in values;
    ghost var remaining := values - {member};
    if remaining == {} {
      assert values == {member};
      assert forall value: nat | value in values :: value <= member;
    } else {
      MaximumExists(remaining);
      ghost var tail: nat :| tail in remaining &&
                             forall value: nat | value in remaining :: value <= tail;
      ghost var maximum := if member > tail then member else tail;
      assert forall value: nat | value in values :: value <= maximum by {
        forall value: nat | value in values
          ensures value <= maximum
        {
          if value != member { assert value in remaining; }
        }
      }
      assert maximum in values;
    }
  }

  ghost function MaximumWidth(values: set<nat>): (maximum: nat)
    ensures values == {} ==> maximum == 0
    ensures values != {} ==> maximum in values
    ensures forall value: nat | value in values :: value <= maximum
  {
    if values == {} then 0
    else
      MaximumExists(values);
      var maximum: nat :| maximum in values &&
                          forall value: nat | value in values :: value <= maximum;
      maximum
  }

}

module LsSpec {
  import MaximumModel = LsMaximumModel
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Errno = Errnos
  import Result = Results
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import IOContract
  import Schema = LsSchema
  import Time = LsTime
  import SE = StringEscaping
  import Native = LsNativeSpec
  import NativeObservation = LsNativeObservationSpec
  import NativeDirectory = LsNativeDirectorySpec

  datatype DirentKindEvidence =
    KnownDirectory | KnownSymlink | KnownNonDirectory | UnknownDirentKind

  datatype EntryEvidenceSource =
    StatusEntryEvidence(ordinal: nat) |
    DirentEntryEvidence(entry: BenchWorld.DirEntry, kind: DirentKindEvidence) |
    ImpliedDotEntryEvidence

  datatype EntryObservation = EntryObservation(
    displayName: string,
    renderName: string,
    accessPath: BenchWorld.Path,
    followSymlink: bool,
    ok: bool,
    status: BenchWorld.FileStatus,
    err: int,
    linkErr: int,
    entryKind: BenchWorld.DirectoryEntryKind,
    ghost statusOrdinal: nat,
    ghost source: EntryEvidenceSource,
    ghost nativeCalls: seq<Native.Call> := [],
    ghost directoryRead: seq<Native.Call> := []
  )

  datatype DirectoryReadStep = DirectoryReadStep(
    before: map<int, BenchWorld.DirectoryCapabilityState>,
    after: map<int, BenchWorld.DirectoryCapabilityState>,
    more: bool, name: string, kind: BenchWorld.DirectoryEntryKind, err: int,
    ghost nativeCalls: seq<Native.Call> := [])

  datatype DirectoryTrace = NoDirectoryTrace | DirectoryTrace(
                              openedHandles: map<int, BenchWorld.DirectoryCapabilityState>, handle: int,
                              openOk: bool, openErr: int,
                              readSteps: seq<DirectoryReadStep>, terminal: DirectoryReadStep,
                              closed: map<int, BenchWorld.DirectoryCapabilityState>, closeOk: bool, closeErr: int,
                              raw: seq<EntryObservation>, positions: seq<nat>,
                              ghost openCalls: seq<Native.Call> := [],
                              ghost statusCalls: seq<Native.Call> := [],
                              ghost closeCalls: seq<Native.Call> := [],
                              ghost readCalls: seq<Native.Call> := [],
                              ghost nativeCalls: seq<Native.Call> := [],
                              ghost nativePieces: seq<seq<Native.Call>> := [],
                              ghost nativeCuts: seq<nat> := [])

  datatype OperandClass = AccessFailure | DirectOperand | ExpandedDirectory

  datatype OperandObservation = OperandObservation(
    index: nat,
    operand: BenchWorld.Path,
    renderName: string,
    path: BenchWorld.Path,
    ok: bool,
    status: BenchWorld.FileStatus,
    err: int,
    operandClass: OperandClass,
    sectionAvailable: bool,
    body: BenchWorld.Bytes,
    accessErrors: BenchWorld.Bytes,
    sectionErrors: BenchWorld.Bytes,
    failed: bool,
    hasCycle: bool,
    directoryFailed: bool,
    ghost firstStatus: nat,
    ghost afterStatus: nat,
    ghost nativeTrace: DirectoryTrace,
    ghost statusCalls: seq<Native.Call> := [],
    ghost renderCalls: seq<Native.Call> := [],
    ghost nativeCalls: seq<Native.Call> := [],
    ghost linkErr: int := 0
  )

  datatype OutputGroup = OutputGroup(
    indices: seq<nat>,
    body: BenchWorld.Bytes,
    isDirectoryBundle: bool
  )

  datatype RecursiveWitness = RecursiveWitness(
    observations: seq<EntryObservation>,
    readErr: int,
    listingOutput: BenchWorld.Bytes,
    listingErrors: BenchWorld.Bytes,
    listingHadError: bool,
    children: map<nat, RecursiveWitness>,
    cycles: set<nat>,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool,
    openOk: bool,
    openErr: int,
    statusOk: bool,
    openedStatus: BenchWorld.FileStatus,
    statusErr: int,
    cycle: bool,
    ghost firstStatus: nat,
    ghost listingFirstStatus: nat,
    ghost listingAfterStatus: nat,
    ghost afterStatus: nat,
    ghost nativeTrace: DirectoryTrace,
    ghost openedStatusCalls: seq<Native.Call> := [],
    ghost nativeCalls: seq<Native.Call> := [],
    ghost childNativePieces: seq<seq<Native.Call>> := [],
    ghost childNativeCuts: seq<nat> := []
  )

  predicate DirectoryOperationFailed(trace: DirectoryTrace, readErr: int)
  {
    trace.DirectoryTrace? && (!trace.openOk || readErr != 0 || trace.closeErr != 0)
  }

  ghost predicate RecursiveRootFailed(tree: RecursiveWitness)
  {
    !tree.openOk || !tree.statusOk || DirectoryOperationFailed(tree.nativeTrace, tree.readErr)
  }

  ghost predicate RecursiveHasCycle(tree: RecursiveWitness)
    decreases tree
  {
    tree.cycle || tree.cycles != {} ||
    exists i: nat :: i in tree.children && RecursiveHasCycle(tree.children[i])
  }

  function RecursiveEntryEligible(observation: EntryObservation): bool
  {
    observation.displayName != "." && observation.displayName != ".." &&
    (observation.entryKind == BenchWorld.DirectoryDirentKind ||
     (observation.ok && observation.status.kind == BenchWorld.DirectoryKind))
  }

  const HelpTextSpec: BenchWorld.Bytes :=
    "Usage: ls [OPTION]... [FILE]...\n"
    + "List information about the FILEs (the current directory by default).\n"
    + "Sort entries alphabetically if none of -cftuvSUX nor --sort is specified.\n"
    + "\n"
    + "Mandatory arguments to long options are mandatory for short options too.\n"
    + "  -a, --all\n"
    + "         do not ignore entries starting with .\n"
    + "  -A, --almost-all\n"
    + "         do not list implied . and ..\n"
    + "      --author\n"
    + "         with -l, print the author of each file\n"
    + "  -b, --escape\n"
    + "         print C-style escapes for nongraphic characters\n"
    + "      --block-size=SIZE\n"
    + "         with -l, scale sizes by SIZE when printing them;\n"
    + "         e.g., '--block-size=M'; see SIZE format below\n"
    + "  -B, --ignore-backups\n"
    + "         do not list implied entries ending with ~\n"
    + "  -c\n"
    + "         with -lt: sort by, and show, ctime\n"
    + "           (time of last change of file status information);\n"
    + "         with -l: show ctime and sort by name;\n"
    + "         otherwise: sort by ctime, newest first\n"
    + "  -C\n"
    + "         list entries by columns\n"
    + "      --color[=WHEN]\n"
    + "         color the output WHEN; more info below\n"
    + "  -d, --directory\n"
    + "         list directories themselves, not their contents\n"
    + "  -D, --dired\n"
    + "         generate output designed for Emacs' dired mode\n"
    + "  -f\n"
    + "         same as -a -U\n"
    + "  -F, --classify[=WHEN]\n"
    + "         append indicator (one of */=>@|) to entries WHEN\n"
    + "      --file-type\n"
    + "         like -F, except do not append '*'\n"
    + "      --format=WORD\n"
    + "         across,horizontal (-x), commas (-m), long (-l),\n"
    + "         single-column (-1), verbose (-l), vertical (-C)\n"
    + "      --full-time\n"
    + "         like -l --time-style=full-iso\n"
    + "  -g\n"
    + "         like -l, but do not list owner\n"
    + "      --group-directories-first\n"
    + "         group directories before files\n"
    + "  -G, --no-group\n"
    + "         in a long listing, don't print group names\n"
    + "  -h, --human-readable\n"
    + "         with -l and -s, print sizes like 1K 234M 2G etc.\n"
    + "      --si\n"
    + "         likewise, but use powers of 1000 not 1024\n"
    + "  -H, --dereference-command-line\n"
    + "         follow symbolic links listed on the command line\n"
    + "      --dereference-command-line-symlink-to-dir\n"
    + "         follow each command line symbolic link that points to a directory\n"
    + "      --hide=PATTERN\n"
    + "         do not list implied entries matching shell PATTERN\n"
    + "         (overridden by -a or -A)\n"
    + "      --hyperlink[=WHEN]\n"
    + "         hyperlink file names WHEN\n"
    + "      --indicator-style=WORD\n"
    + "         append indicator with style WORD to entry names:\n"
    + "           none (default), slash (-p), file-type (--file-type), classify (-F)\n"
    + "  -i, --inode\n"
    + "         print the index number of each file\n"
    + "  -I, --ignore=PATTERN\n"
    + "         do not list implied entries matching shell PATTERN\n"
    + "  -k, --kibibytes\n"
    + "         default to 1024-byte blocks for file system usage;\n"
    + "         used only with -s and per directory totals\n"
    + "  -l\n"
    + "         use a long listing format\n"
    + "  -L, --dereference\n"
    + "         when showing file information for a symbolic link,\n"
    + "         show information for the file the link references\n"
    + "         rather than for the link itself\n"
    + "  -m\n"
    + "         fill width with a comma separated list of entries\n"
    + "  -n, --numeric-uid-gid\n"
    + "         like -l, but list numeric user and group IDs\n"
    + "  -N, --literal\n"
    + "         print entry names without quoting\n"
    + "  -o\n"
    + "         like -l, but do not list group information\n"
    + "  -p, --indicator-style=slash\n"
    + "         append / indicator to directories\n"
    + "  -q, --hide-control-chars\n"
    + "         print ? instead of nongraphic characters\n"
    + "      --show-control-chars\n"
    + "         show nongraphic characters as-is;\n"
    + "         the default, unless program is 'ls' and output is a terminal\n"
    + "  -Q, --quote-name\n"
    + "         enclose entry names in double quotes\n"
    + "      --quoting-style=WORD\n"
    + "         use quoting style WORD for entry names:\n"
    + "           literal, locale, shell, shell-always,\n"
    + "           shell-escape, shell-escape-always, c, escape\n"
    + "         (overrides QUOTING_STYLE environment variable)\n"
    + "  -r, --reverse\n"
    + "         reverse order while sorting\n"
    + "  -R, --recursive\n"
    + "         list subdirectories recursively\n"
    + "  -s, --size\n"
    + "         print the allocated size of each file, in blocks\n"
    + "  -S\n"
    + "         sort by file size, largest first\n"
    + "      --sort=WORD\n"
    + "         change default 'name' sort to WORD:\n"
    + "           none (-U), size (-S), time (-t),\n"
    + "           version (-v), extension (-X), name, width\n"
    + "      --time=WORD\n"
    + "         select which timestamp used to display or sort;\n"
    + "           access time (-u): atime, access, use;\n"
    + "           metadata change time (-c): ctime, status;\n"
    + "           modified time (default): mtime, modification;\n"
    + "           birth time: birth, creation;\n"
    + "         with -l, WORD determines which time to show;\n"
    + "         with --sort=time, sort by WORD (newest first)\n"
    + "      --time-style=TIME_STYLE\n"
    + "         time/date format with -l; see TIME_STYLE below\n"
    + "  -t\n"
    + "         sort by time, newest first; see --time\n"
    + "  -T, --tabsize=COLS\n"
    + "         assume tab stops at each COLS instead of 8\n"
    + "  -u\n"
    + "         with -lt: sort by, and show, access time;\n"
    + "         with -l: show access time and sort by name;\n"
    + "         otherwise: sort by access time, newest first\n"
    + "  -U\n"
    + "         do not sort directory entries\n"
    + "  -v\n"
    + "         natural sort of (version) numbers within text\n"
    + "  -w, --width=COLS\n"
    + "         set output width to COLS.  0 means no limit\n"
    + "  -x\n"
    + "         list entries by lines instead of by columns\n"
    + "  -X\n"
    + "         sort alphabetically by entry extension\n"
    + "  -Z, --context\n"
    + "         print any security context of each file\n"
    + "      --zero\n"
    + "         end each output line with NUL, not newline\n"
    + "  -1\n"
    + "         list one file per line\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "The SIZE argument is an integer and optional unit (example: 10K is 10*1024).\n"
    + "Units are K,M,G,T,P,E,Z,Y,R,Q (powers of 1024) or KB,MB,... (powers of 1000).\n"
    + "Binary prefixes can be used, too: KiB=K, MiB=M, and so on.\n"
    + "\n"
    + "The TIME_STYLE argument can be full-iso, long-iso, iso, locale, or +FORMAT.\n"
    + "FORMAT is interpreted like in date(1).  If FORMAT is FORMAT1<newline>FORMAT2,\n"
    + "then FORMAT1 applies to non-recent files and FORMAT2 to recent files.\n"
    + "TIME_STYLE prefixed with 'posix-' takes effect only outside the POSIX locale.\n"
    + "Also the TIME_STYLE environment variable sets the default style to use.\n"
    + "\n"
    + "The WHEN argument defaults to 'always' and can also be 'auto' or 'never'.\n"
    + "\n"
    + "Using color to distinguish file types is disabled both by default and\n"
    + "with --color=never.  With --color=auto, ls emits color codes only when\n"
    + "standard output is connected to a terminal.  The LS_COLORS environment\n"
    + "variable can change the settings.  Use the dircolors(1) command to set it.\n"
    + "\n"
    + "Exit status:\n"
    + " 0  if OK,\n"
    + " 1  if minor problems (e.g., cannot access subdirectory),\n"
    + " 2  if serious trouble (e.g., cannot access command-line argument).\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/ls>\n"
    + "or available locally via: info '(coreutils) ls invocation'\n"

  const VersionTextSpec: BenchWorld.Bytes :=
    "ls (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Richard M. Stallman and David MacKenzie.\n"

  function ErrnoTextSpec(err: int): string
  {
    if err == Errno.ENOENT then "No such file or directory"
    else if err == Errno.EACCES then "Permission denied"
    else if err == Errno.ENOTDIR then "Not a directory"
    else if err == Errno.ELOOP then "Too many levels of symbolic links"
    else if err == Errno.EBADF then "Bad file descriptor"
    else if err == Errno.EINTR then "Interrupted system call"
    else if err == Errno.EIO then "Input/output error"
    else if err == Errno.ENOMEM then "Cannot allocate memory"
    else if err == Errno.ENAMETOOLONG then "File name too long"
    else if err == Errno.EOVERFLOW then "Value too large for defined data type"
    else if err == Errno.EINVAL then "Invalid argument"
    else if err == Errno.ENFILE then "Too many open files in system"
    else if err == Errno.EMFILE then "Too many open files"
    else "I/O error"
  }

  function AccessErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    "ls: cannot access " + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
    ": " + ErrnoTextSpec(err) + "\n"
  }

  function ReadLinkErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    if err == 0 then []
    else
      "ls: cannot read symbolic link " + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
      ": " + ErrnoTextSpec(err) + "\n"
  }

  function ObservationFailedSpec(observation: EntryObservation): bool
  {
    !observation.ok || observation.linkErr != 0
  }

  function EntryErrorTextSpec(path: BenchWorld.Path, observation: EntryObservation): BenchWorld.Bytes
  {
    if !observation.ok then AccessErrorMessageSpec(path, observation.err)
    else ReadLinkErrorMessageSpec(path, observation.linkErr)
  }

  function ReadDirectoryErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    "ls: reading directory " + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
    ": " + ErrnoTextSpec(err) + "\n"
  }

  function CloseDirectoryErrorMessageSpec(path: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    if err == 0 then []
    else
      "ls: closing directory " + SE.SpecQuoteAfBytes(Utf8.Encode(path)) +
      ": " + ErrnoTextSpec(err) + "\n"
  }

  ghost predicate BoundOpenDirectoryTrace(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                          path: BenchWorld.Path, trace: DirectoryTrace, ok: bool, err: int)
  {
    trace.DirectoryTrace? && trace.openOk == ok && trace.openErr == err &&
    |trace.openCalls| == 1 && NativeCallsFields(cmd,fs,trace.openCalls) &&
    var call := trace.openCalls[0];
    call.action.OpenAction? && call.action.path == path && call.action.dots &&
    call.action.openResult.Ok? == ok && IOContract.ResultErrno(call.action.openResult) == err &&
    trace.handle == IOContract.ResultValue(call.action.openResult,0) &&
    trace.openedHandles == call.after.context.capabilities
  }

  ghost predicate FailedOpenDirectoryTrace(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                           path: BenchWorld.Path, trace: DirectoryTrace)
  {
    trace.DirectoryTrace? && BoundOpenDirectoryTrace(cmd,fs,path,trace,false,trace.openErr) &&
    trace.readSteps == [] && trace.raw == [] && trace.positions == [] &&
    trace.statusCalls == [] && trace.closeCalls == [] && trace.readCalls == [] &&
    trace.nativePieces == [] && trace.nativeCuts == [0] &&
    trace.nativeCalls == trace.openCalls &&
    trace.closed == trace.openCalls[0].before.context.capabilities && !trace.closeOk && trace.closeErr == 0
  }

  ghost predicate DirectoryReadStepFields(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                          handle: int, step: DirectoryReadStep)
  {
    |step.nativeCalls| == 1 && NativeCallsFields(cmd,fs,step.nativeCalls) &&
    var call := step.nativeCalls[0];
    call.action.ReadAction? && call.action.handle == handle &&
    step.before == call.before.context.capabilities && step.after == call.after.context.capabilities &&
    var result := call.action.readResult;
    step.more == (result.Ok? && result.v.DirectoryItem?) &&
    step.name == (if step.more then result.v.name else "") &&
    step.kind == (if step.more then result.v.kind else BenchWorld.UnknownDirentKind) &&
    step.err == IOContract.ResultErrno(result)
  }

  ghost predicate DirectoryReadPrefix(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                      openedHandles: map<int,BenchWorld.DirectoryCapabilityState>, handle: int,
                                      steps: seq<DirectoryReadStep>, after: map<int,BenchWorld.DirectoryCapabilityState>)
  {
    cmd.statusContext.BoundStatusObservations? &&
    (if |steps| == 0 then after == openedHandles
     else steps[0].before == openedHandles && steps[|steps|-1].after == after) &&
    forall i: nat | i < |steps| :: steps[i].more && steps[i].err == 0 &&
                                   DirectoryReadStepFields(cmd,fs,handle,steps[i]) &&
                                   (i > 0 ==> steps[i-1].after == steps[i].before)
  }

  ghost predicate DirectoryReadEvidence(cmd: Schema.LsCmd,
                                        steps: seq<DirectoryReadStep>, raw: seq<EntryObservation>, positions: seq<nat>)
  {
    |positions| == |raw| &&
    (forall i: nat | i < |raw| ::
       positions[i] < |steps| &&
       raw[i].displayName == steps[positions[i]].name &&
       raw[i].directoryRead == steps[positions[i]].nativeCalls &&
       (raw[i].entryKind == steps[positions[i]].kind ||
        ((raw[i].displayName == "." || raw[i].displayName == "..") &&
         raw[i].entryKind == BenchWorld.DirectoryDirentKind)) &&
       (i > 0 ==> positions[i-1] < positions[i])) &&
    (forall i: nat | i < |steps| && VisibleNameSpec(cmd, steps[i].name) ::
       exists j: nat :: j < |raw| && raw[j].displayName == steps[i].name)
  }

  ghost predicate NativeCallFragments(pieces: seq<seq<Native.Call>>, combined: seq<Native.Call>, cuts: seq<nat>)
  {
    |cuts| == |pieces|+1 && cuts[0] == 0 && cuts[|pieces|] == |combined| &&
    forall i: nat {:trigger pieces[i]} | i < |pieces| :: cuts[i] <= cuts[i+1] <= |combined| &&
                                                         combined[cuts[i]..cuts[i+1]] == pieces[i]
  }

  ghost predicate DirectoryCallPieces(trace: DirectoryTrace)
  {
    trace.DirectoryTrace? && |trace.nativePieces| == |trace.readSteps| &&
    NativeCallFragments(trace.nativePieces,trace.readCalls,trace.nativeCuts) &&
    (forall i: nat | i < |trace.readSteps| ::
       if exists j: nat :: j < |trace.positions| && trace.positions[j] == i then
         exists j: nat :: j < |trace.positions| && j < |trace.raw| && trace.positions[j] == i &&
                          trace.nativePieces[i] == trace.readSteps[i].nativeCalls+trace.raw[j].nativeCalls
       else trace.nativePieces[i] == trace.readSteps[i].nativeCalls)
  }

  ghost predicate ReadCloseDirectoryTrace(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                          path: BenchWorld.Path, trace: DirectoryTrace, readErr: int, closeErr: int)
  {
    BoundOpenDirectoryTrace(cmd,fs,path,trace,true,0) &&
    DirectoryReadPrefix(cmd,fs,trace.openedHandles,trace.handle,trace.readSteps,trace.terminal.before) &&
    DirectoryReadEvidence(cmd,trace.readSteps,trace.raw,trace.positions) &&
    DirectoryReadStepFields(cmd,fs,trace.handle,trace.terminal) &&
    !trace.terminal.more && trace.terminal.err == readErr &&
    |trace.closeCalls| == 1 && NativeCallsFields(cmd,fs,trace.closeCalls) &&
    trace.closeCalls[0].action.CloseAction? && trace.closeCalls[0].action.handle == trace.handle &&
    trace.closeCalls[0].before.context.capabilities == trace.terminal.after &&
    trace.closeCalls[0].after.context.capabilities == trace.closed &&
    IOContract.ResultErrno(trace.closeCalls[0].action.closeResult) == closeErr &&
    trace.closeOk == (closeErr == 0) && trace.closeErr == closeErr &&
    trace.closed == trace.openCalls[0].before.context.capabilities &&
    DirectoryCallPieces(trace) &&
    trace.nativeCalls == trace.openCalls+trace.statusCalls+trace.readCalls+
    trace.terminal.nativeCalls+trace.closeCalls && NativeCallsFields(cmd,fs,trace.nativeCalls)
  }

  ghost predicate RecursiveNativeDirectoryTrace(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                                path: BenchWorld.Path, tree: RecursiveWitness)
  {
    BoundOpenDirectoryTrace(cmd,fs,path,tree.nativeTrace,tree.openOk,tree.openErr) &&
    if !tree.openOk then FailedOpenDirectoryTrace(cmd,fs,path,tree.nativeTrace)
    else
      var trace := tree.nativeTrace;
      trace.statusCalls == tree.openedStatusCalls && |tree.openedStatusCalls| == 1 &&
      NativeCallsFields(cmd,fs,tree.openedStatusCalls) &&
      var call := tree.openedStatusCalls[0];
      call.before.status == tree.firstStatus && call.action.HandleStatusAction? &&
      call.action.handle == trace.handle &&
      NativeObservation.StatusFields(call.action.statusResult,tree.statusOk,tree.openedStatus,tree.statusErr) &&
      if !tree.statusOk || tree.cycle then
        trace.readSteps == [] && trace.raw == [] && trace.positions == [] &&
        |trace.closeCalls| == 1 && NativeCallsFields(cmd,fs,trace.closeCalls) &&
        trace.closeCalls[0].action.CloseAction? && trace.closeCalls[0].action.handle == trace.handle &&
        IOContract.ResultErrno(trace.closeCalls[0].action.closeResult) == trace.closeErr &&
        trace.closeOk == (trace.closeErr == 0) &&
        trace.closed == trace.openCalls[0].before.context.capabilities &&
        trace.nativeCalls == trace.openCalls+trace.statusCalls+trace.closeCalls &&
        NativeCallsFields(cmd,fs,trace.nativeCalls)
      else true
  }

  ghost predicate OpenDirectoryObservation(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                           path: BenchWorld.Path, ok: bool, err: int)
  {
    exists call: Native.Call :: NativeCallsFields(cmd,fs,[call]) &&
                                call.action.OpenAction? && call.action.path == path && call.action.dots &&
                                call.action.openResult.Ok? == ok && IOContract.ResultErrno(call.action.openResult) == err
  }

  ghost predicate OpenedDirectoryStatusObservation(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                                   path: BenchWorld.Path, firstStatus: nat, ok: bool, status: BenchWorld.FileStatus, err: int)
  {
    exists call: Native.Call :: NativeCallsFields(cmd,fs,[call]) &&
                                call.before.status == firstStatus && call.action.HandleStatusAction? &&
                                NativeObservation.StatusFields(call.action.statusResult,ok,status,err)
  }

  ghost predicate DirectoryCloseObservation(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                            path: BenchWorld.Path, readErr: int, err: int)
  {
    exists read: Native.Call, closed: Native.Call :: NativeCallsFields(cmd,fs,[read,closed]) &&
                                                     read.action.ReadAction? && closed.action.CloseAction? &&
                                                     read.action.handle == closed.action.handle &&
                                                     (read.action.readResult.Err? || read.action.readResult.v.DirectoryEnd?) &&
                                                     IOContract.ResultErrno(read.action.readResult) == readErr &&
                                                     IOContract.ResultErrno(closed.action.closeResult) == err
  }

  function OpenDirectoryErrorMessageSpec(displayPath: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    "ls: cannot open directory " + SE.SpecQuoteAfBytes(Utf8.Encode(displayPath)) +
    ": " + ErrnoTextSpec(err) + "\n"
  }

  function DirectoryIdentityErrorMessageSpec(displayPath: BenchWorld.Path, err: int): BenchWorld.Bytes
  {
    "ls: cannot determine device and inode of " +
    SE.SpecQuoteAfBytes(Utf8.Encode(displayPath)) +
    ": " + ErrnoTextSpec(err) + "\n"
  }

  opaque function DirectoryHeaderSpec(displayPath: BenchWorld.Path): BenchWorld.Bytes
  {
    Utf8.Encode(displayPath) + ":\n"
  }

  function InvalidModeMessageSpec(mode: Schema.LsMode): BenchWorld.Bytes
  {
    match mode
    case ModeInvalidBlockSize(value) =>
      Utf8.Encode("ls: invalid --block-size argument '") + Utf8.Encode(value) + "'\n"
    case ModeInvalidTime(value) =>
      Utf8.Encode("ls: invalid argument ") + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
      Utf8.Encode(" for '--time'\n" +
                  "Valid arguments are:\n" +
                  "  - 'atime', 'access', 'use'\n" +
                  "  - 'ctime', 'status'\n" +
                  "  - 'mtime', 'modification'\n" +
                  "  - 'birth', 'creation'\n" +
                  "Try 'ls --help' for more information.\n")
    case ModeInvalidTimeStyle(value) =>
      Utf8.Encode("ls: invalid argument ") + SE.SpecLocaleQuoteBytes(Utf8.Encode(value)) +
      Utf8.Encode(" for 'time style'\n" +
                  "Valid arguments are:\n" +
                  "  - [posix-]full-iso\n" +
                  "  - [posix-]long-iso\n" +
                  "  - [posix-]iso\n" +
                  "  - [posix-]locale\n" +
                  "  - +FORMAT (e.g., +%H:%M) for a 'date'-style format\n" +
                  "Try 'ls --help' for more information.\n")
    case _ => []
  }

  function IntTextSpec(n: int): string
  {
    if n < 0 then "-" + Time.NatText((-n) as nat) else Time.NatText(n as nat)
  }

  function ParsedPositiveOrZeroSpec(text: string): nat
  {
    match Schema.ParsePositive(text)
    case PositiveNat(value) => value
    case InvalidPositiveNat => 0
  }

  function EnvironmentBlockSizeSpec(env: map<string, string>): nat
  {
    if "LS_BLOCK_SIZE" in env && ParsedPositiveOrZeroSpec(env["LS_BLOCK_SIZE"]) > 0 then
      ParsedPositiveOrZeroSpec(env["LS_BLOCK_SIZE"])
    else if "BLOCK_SIZE" in env && ParsedPositiveOrZeroSpec(env["BLOCK_SIZE"]) > 0 then
      ParsedPositiveOrZeroSpec(env["BLOCK_SIZE"])
    else if "BLOCKSIZE" in env && ParsedPositiveOrZeroSpec(env["BLOCKSIZE"]) > 0 then
      ParsedPositiveOrZeroSpec(env["BLOCKSIZE"])
    else
      1024
  }

  function EnvironmentFileSizeBlockSizeSpec(env: map<string, string>): nat
  {
    if "LS_BLOCK_SIZE" in env && ParsedPositiveOrZeroSpec(env["LS_BLOCK_SIZE"]) > 0 then
      ParsedPositiveOrZeroSpec(env["LS_BLOCK_SIZE"])
    else if "BLOCK_SIZE" in env && ParsedPositiveOrZeroSpec(env["BLOCK_SIZE"]) > 0 then
      ParsedPositiveOrZeroSpec(env["BLOCK_SIZE"])
    else
      1
  }

  function EffectiveCommandSpec(
    raw: Schema.LsCmdRaw, env: map<string, string>, referenceNow: int
  ): Schema.LsCmd
  {
    var cmd := Schema.Command(raw);
    Schema.WithReferenceNow(Schema.WithBlockSize(
                              cmd,
                              if cmd.cliBlockSize > 0 then cmd.cliBlockSize else EnvironmentBlockSizeSpec(env),
                              if cmd.cliBlockSize > 0 then cmd.cliBlockSize
                              else EnvironmentFileSizeBlockSizeSpec(env)
                            ), referenceNow)
  }

  function DisplayedBlocksSpec(blocks512: nat, blockSize: nat): nat
  {
    if blockSize == 0 then 0 else (blocks512 * 512 + blockSize - 1) / blockSize
  }

  function DisplayedFileSizeSpec(size: nat, blockSize: nat): nat
  {
    if blockSize == 0 then 0 else (size + blockSize - 1) / blockSize
  }

  function HasModeBitSpec(mode: bv32, bit: bv32): bool
  {
    (mode & bit) != 0 as bv32
  }

  function PermissionCharSpec(mode: bv32, bit: bv32, present: char): char
  {
    if HasModeBitSpec(mode, bit) then present else '-'
  }

  function ExecuteCharSpec(
    mode: bv32,
    executeBit: bv32,
    specialBit: bv32,
    specialExecute: char,
    specialNoExecute: char
  ): char
  {
    if HasModeBitSpec(mode, specialBit) then
      if HasModeBitSpec(mode, executeBit) then specialExecute else specialNoExecute
    else
      PermissionCharSpec(mode, executeBit, 'x')
  }

  function KindCharSpec(kind: BenchWorld.FileKind): char
  {
    match kind
    case RegularKind => '-'
    case DirectoryKind => 'd'
    case SymlinkKind => 'l'
    case BlockDeviceKind => 'b'
    case CharacterDeviceKind => 'c'
    case FifoKind => 'p'
    case SocketKind => 's'
  }

  function ModeTextSpec(status: BenchWorld.FileStatus): string
  {
    [KindCharSpec(status.kind),
     PermissionCharSpec(status.mode, 256 as bv32, 'r'),
     PermissionCharSpec(status.mode, 128 as bv32, 'w'),
     ExecuteCharSpec(status.mode, 64 as bv32, 2048 as bv32, 's', 'S'),
     PermissionCharSpec(status.mode, 32 as bv32, 'r'),
     PermissionCharSpec(status.mode, 16 as bv32, 'w'),
     ExecuteCharSpec(status.mode, 8 as bv32, 1024 as bv32, 's', 'S'),
     PermissionCharSpec(status.mode, 4 as bv32, 'r'),
     PermissionCharSpec(status.mode, 2 as bv32, 'w'),
     ExecuteCharSpec(status.mode, 1 as bv32, 512 as bv32, 't', 'T')]
  }

  datatype ColumnWidths = ColumnWidths(blocks: nat, links: nat, owner: nat, group: nat, size: nat)

  ghost function MaximumWidth(values: set<nat>): (maximum: nat)
    ensures values == {} ==> maximum == 0
    ensures values != {} ==> maximum in values
    ensures forall value: nat | value in values :: value <= maximum
  {
    MaximumModel.MaximumWidth(values)
  }

  function PadColumn(text: string, width: nat, right: bool): string
  {
    var blanks := seq((if width > |text| then width - |text| else 0), i => ' ');
    if right then blanks + text else text + blanks
  }

  ghost function StatusWidthsSpec(cmd: Schema.LsCmd, statuses: set<BenchWorld.FileStatus>): ColumnWidths
  {
    ColumnWidths(
      MaximumWidth(set status <- statuses :: |Time.NatText(DisplayedBlocksSpec(status.storage.allocatedBlocks, cmd.cliBlockSize))|),
      MaximumWidth(set status <- statuses :: |Time.NatText(status.linkCount)|),
      MaximumWidth(set status <- statuses :: |Time.NatText(status.ownership.uid)|),
      MaximumWidth(set status <- statuses :: |Time.NatText(status.ownership.gid)|),
      MaximumWidth(set status <- statuses :: |Time.NatText(DisplayedFileSizeSpec(status.storage.size, cmd.fileSizeBlockSize))|))
  }

  ghost function ObservationWidthsSpec(cmd: Schema.LsCmd, observations: seq<EntryObservation>): ColumnWidths
  {
    StatusWidthsSpec(cmd, set i: nat | i < |observations| && observations[i].ok :: observations[i].status)
  }

  ghost function OperandWidthsSpec(cmd: Schema.LsCmd, observations: seq<OperandObservation>): ColumnWidths
  {
    StatusWidthsSpec(cmd, set i: nat | i < |observations| && observations[i].ok :: observations[i].status)
  }

  ghost function RenderOperandSpec(cmd: Schema.LsCmd, observations: seq<OperandObservation>, index: nat): BenchWorld.Bytes
    requires index < |observations|
  {
    RenderAlignedEntrySpec(cmd, observations[index].renderName, observations[index].status,
                           OperandWidthsSpec(cmd, observations))
  }

  function RenderEntrySpec(cmd: Schema.LsCmd, displayName: string, status: BenchWorld.FileStatus): BenchWorld.Bytes
  {
    RenderAlignedEntrySpec(cmd, displayName, status, ColumnWidths(0, 0, 0, 0, 0))
  }

  function RenderAlignedEntrySpec(
    cmd: Schema.LsCmd,
    displayName: string,
    status: BenchWorld.FileStatus,
    widths: ColumnWidths
  ): BenchWorld.Bytes
  {
    var blockPrefix := if cmd.showBlocks then
                         PadColumn(Time.NatText(DisplayedBlocksSpec(status.storage.allocatedBlocks, cmd.cliBlockSize)), widths.blocks, true) + " "
                       else "";
    Utf8.Encode(blockPrefix + if !cmd.numericLong then
                  displayName + "\n"
                else
                  ModeTextSpec(status) + " " +
                  PadColumn(Time.NatText(status.linkCount), widths.links, true) + " " +
                  PadColumn(Time.NatText(status.ownership.uid), widths.owner, true) + " " +
                  PadColumn(Time.NatText(status.ownership.gid), widths.group, true) + " " +
                  PadColumn(Time.NatText(DisplayedFileSizeSpec(
                                           status.storage.size, cmd.fileSizeBlockSize)), widths.size, true) + " " +
                  TimeTextSpec(cmd, SelectedSecondsSpec(cmd, status),
                               SelectedNanosecondsSpec(cmd, status)) + " " +
                  displayName + "\n")
  }

  function ClassifiedDirentKindSpec(kind: BenchWorld.DirectoryEntryKind): DirentKindEvidence
  {
    match kind
    case UnknownDirentKind => UnknownDirentKind
    case DirectoryDirentKind => KnownDirectory
    case SymlinkDirentKind => KnownSymlink
    case _ => KnownNonDirectory
  }

  function DirectoryEntryKindCharSpec(kind: BenchWorld.DirectoryEntryKind): char
  {
    match kind
    case UnknownDirentKind => '?'
    case RegularDirentKind => '-'
    case DirectoryDirentKind => 'd'
    case SymlinkDirentKind => 'l'
    case FifoDirentKind => 'p'
    case BlockDeviceDirentKind => 'b'
    case CharacterDeviceDirentKind => 'c'
    case SocketDirentKind => 's'
  }

  function FailedTimeWidthSpec(cmd: Schema.LsCmd): nat
  {
    match cmd.timeStyle
    case DefaultC => 12
    case FullIso => 35
    case LongIso => 16
    case Iso => 11
    case EpochSeconds => 1
  }

  function RenderFailedEntrySpec(
    cmd: Schema.LsCmd, observation: EntryObservation, widths: ColumnWidths
  ): BenchWorld.Bytes
  {
    var blocks := if cmd.showBlocks then PadColumn("?", widths.blocks, true) + " " else "";
    Utf8.Encode(blocks + (if cmd.numericLong then
                            [DirectoryEntryKindCharSpec(observation.entryKind)] + "????????? " +
                            PadColumn("?", widths.links, true) + " " +
                            PadColumn("?", widths.owner, false) + " " +
                            PadColumn("?", widths.group, false) + " " +
                            PadColumn("?", widths.size, true) + " " +
                            PadColumn("?", FailedTimeWidthSpec(cmd), true) + " "
                          else "") + observation.displayName + "\n")
  }

  function EntryDiagnosticPathSpec(displayPath: BenchWorld.Path, name: string): BenchWorld.Path
  {
    if displayPath == "." then name
    else if |displayPath| > 0 && displayPath[|displayPath| - 1] == '/' then displayPath + name
    else BenchWorld.AppendPath(displayPath, name)
  }

  function OperandFailureExitSpec(observation: OperandObservation): nat
  {
    if !observation.failed then 0
    else if observation.operandClass == AccessFailure || !observation.sectionAvailable ||
            observation.hasCycle || observation.directoryFailed then 2
    else 1
  }

  ghost function OperandExitSpec(observations: seq<OperandObservation>): nat
  {
    MaximumWidth(set i: nat | i < |observations| :: OperandFailureExitSpec(observations[i]))
  }

  function TimeTextSpec(cmd: Schema.LsCmd, seconds: int, nanoseconds: int): string
  {
    match cmd.timeStyle
    case EpochSeconds => IntTextSpec(seconds)
    case FullIso => Time.FullIso(seconds, nanoseconds)
    case LongIso => Time.LongIso(seconds)
    case Iso => Time.Iso(seconds, nanoseconds, cmd.referenceNow)
    case DefaultC => Time.DefaultC(seconds, nanoseconds, cmd.referenceNow)
  }

  function AllocatedBlocksSumSpec(observations: seq<EntryObservation>): nat
    decreases |observations|
  {
    if |observations| == 0 then 0
    else
      (if observations[0].ok then observations[0].status.storage.allocatedBlocks else 0) +
      AllocatedBlocksSumSpec(observations[1..])
  }

  function TotalLineSpec(cmd: Schema.LsCmd, observations: seq<EntryObservation>): BenchWorld.Bytes
  {
    if cmd.numericLong || cmd.showBlocks then
      Utf8.Encode("total " + Time.NatText(
                    DisplayedBlocksSpec(AllocatedBlocksSumSpec(observations), cmd.cliBlockSize)) + "\n")
    else
      []
  }

  function MakeAbsoluteSpec(cwd: BenchWorld.Path, path: BenchWorld.Path): BenchWorld.Path
  {
    if path == "" || BenchWorld.IsAbsolutePath(path) then path
    else BenchWorld.AppendPath(cwd, path)
  }

  // The native request retains its operand spelling; only the ghost filesystem
  // lookup uses the supplied current-directory context.
  ghost function ModelPathSpec(cmd: Schema.LsCmd, path: BenchWorld.Path): BenchWorld.Path
  {
    if cmd.statusContext.BoundStatusObservations? then
      IOContract.AtCwdPathFields(cmd.workingDirectory, path)
    else path
  }

  ghost function OperandPathSpec(cmd: Schema.LsCmd, cwd: BenchWorld.Path,
                                 operand: BenchWorld.Path): BenchWorld.Path
  {
    if cmd.statusContext.BoundStatusObservations? then operand
    else MakeAbsoluteSpec(cwd, operand)
  }

  function VisibleNameSpec(cmd: Schema.LsCmd, name: string): bool
  {
    if name == "." || name == ".." then cmd.hiddenMode == Schema.All
    else cmd.hiddenMode != Schema.HideDotFiles || |name| == 0 || name[0] != '.'
  }

  function ExplicitCommandLineFollowSpec(cmd: Schema.LsCmd): bool
  {
    cmd.followMode == Schema.FollowAlways ||
    cmd.followMode == Schema.FollowCommandLine
  }

  function EntryMetadataRequiredSpec(cmd: Schema.LsCmd): bool
  {
    cmd.numericLong || cmd.showBlocks ||
    cmd.sortMode != Schema.SortName || cmd.recursive
  }

  function EntryRenderSortMetadataRequiredSpec(cmd: Schema.LsCmd): bool
  {
    cmd.numericLong || cmd.showBlocks || cmd.sortMode != Schema.SortName
  }

  function EntryStatusRequiredSpec(
    cmd: Schema.LsCmd, kind: DirentKindEvidence, name: string
  ): bool
  {
    EntryRenderSortMetadataRequiredSpec(cmd) ||
    (cmd.recursive && name != "." && name != ".." &&
     (kind == UnknownDirentKind ||
      (kind == KnownSymlink && cmd.followMode == Schema.FollowAlways)))
  }

  function DirentKindMatchesEntrySpec(
    kind: DirentKindEvidence, entry: BenchWorld.DirEntry
  ): bool
  {
    match kind
    case KnownDirectory => entry.isDir && !entry.isSymlink
    case KnownSymlink => !entry.isDir && entry.isSymlink
    case KnownNonDirectory => !entry.isDir && !entry.isSymlink
    case UnknownDirentKind => true
  }

  ghost function EntryStatusCallCount(observation: EntryObservation): nat
  {
    match observation.source
    case StatusEntryEvidence(_) => 1
    case _ => 0
  }

  function ImplicitDirectoryFollowSpec(cmd: Schema.LsCmd): bool
  {
    cmd.followMode == Schema.FollowNever &&
    !cmd.numericLong && !cmd.listDirectories
  }

  // The unbound model remains a pure filesystem relation. Bound execution uses
  // finite actual native receipts in MetadataObservationRelation instead.
  ghost function StatusResultSpec(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, ordinal: nat,
    path: BenchWorld.Path, followSymlink: bool
  ): BenchWorld.IOResult<BenchWorld.FileStatus>
  {
    IOContract.GetFileStatusResultFields(fs,path,followSymlink)
  }

  ghost function OperandStatusCallCountSpec(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    firstStatus: nat
  ): nat
  {
    if !ImplicitDirectoryFollowSpec(cmd) then 1
    else
      var first := StatusResultSpec(cmd, fs, firstStatus, path, true);
      if first.Ok? && first.v.kind == BenchWorld.DirectoryKind then 1 else 2
  }

  ghost function OperandStatusResultSpec(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    firstStatus: nat
  ): BenchWorld.IOResult<BenchWorld.FileStatus>
  {
    if ImplicitDirectoryFollowSpec(cmd) then
      match StatusResultSpec(cmd, fs, firstStatus, path, true)
      case Ok(status) =>
        if status.kind == BenchWorld.DirectoryKind then Result.Ok(status)
        else StatusResultSpec(cmd, fs, firstStatus + 1, path, false)
      case Err(_) => StatusResultSpec(cmd, fs, firstStatus + 1, path, false)
    else StatusResultSpec(cmd, fs, firstStatus, path,
                          ExplicitCommandLineFollowSpec(cmd))
  }

  ghost function ReadLinkResultSpec(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                    path: BenchWorld.Path): BenchWorld.IOResult<BenchWorld.Path>
  {
    IOContract.ReadLinkResultFields(fs,path)
  }

  ghost function LinkReadErrorSpec(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                   path: BenchWorld.Path, followSymlink: bool, showTarget: bool,
                                   status: BenchWorld.FileStatus): int
  {
    if status.kind != BenchWorld.SymlinkKind || followSymlink || !showTarget then 0
    else IOContract.ResultErrno(ReadLinkResultSpec(cmd, fs, path))
  }

  ghost function RenderNameSpec(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, displayName: string,
    path: BenchWorld.Path, followSymlink: bool, showTarget: bool,
    status: BenchWorld.FileStatus
  ): string
  {
    if status.kind != BenchWorld.SymlinkKind || followSymlink || !showTarget then displayName
    else
      match ReadLinkResultSpec(cmd, fs, path)
      case Ok(target) => NativeObservation.LinkNameText(displayName,target)
      case Err(_) => displayName
  }

  opaque function StringLessSpec(left: string, right: string): bool
    decreases |left|
  {
    if |left| == 0 then |right| > 0
    else if |right| == 0 then false
    else if left[0] == right[0] then StringLessSpec(left[1..], right[1..])
    else left[0] < right[0]
  }

  function SelectedSecondsSpec(cmd: Schema.LsCmd, status: BenchWorld.FileStatus): int
  {
    match cmd.timeField
    case ModificationTime => status.times.mtimeSec
    case AccessTime => status.times.atimeSec
    case ChangeTime => status.times.ctimeSec
  }

  function SelectedNanosecondsSpec(cmd: Schema.LsCmd, status: BenchWorld.FileStatus): int
  {
    match cmd.timeField
    case ModificationTime => status.times.mtimeNsec
    case AccessTime => status.times.atimeNsec
    case ChangeTime => status.times.ctimeNsec
  }

  opaque function BaseEntryBeforeSpec(
    cmd: Schema.LsCmd,
    left: EntryObservation,
    right: EntryObservation
  ): bool
  {
    if cmd.sortMode == Schema.SortSize &&
       (if left.ok then left.status.storage.size else 0) != (if right.ok then right.status.storage.size else 0) then
      (if left.ok then left.status.storage.size else 0) > (if right.ok then right.status.storage.size else 0)
    else if cmd.sortMode == Schema.SortTime &&
            (if left.ok then SelectedSecondsSpec(cmd, left.status) else 0) != (if right.ok then SelectedSecondsSpec(cmd, right.status) else 0) then
      (if left.ok then SelectedSecondsSpec(cmd, left.status) else 0) > (if right.ok then SelectedSecondsSpec(cmd, right.status) else 0)
    else if cmd.sortMode == Schema.SortTime &&
            (if left.ok then SelectedNanosecondsSpec(cmd, left.status) else 0) != (if right.ok then SelectedNanosecondsSpec(cmd, right.status) else 0) then
      (if left.ok then SelectedNanosecondsSpec(cmd, left.status) else 0) > (if right.ok then SelectedNanosecondsSpec(cmd, right.status) else 0)
    else
      StringLessSpec(left.displayName, right.displayName)
  }

  opaque function EntryBeforeSpec(
    cmd: Schema.LsCmd,
    left: EntryObservation,
    right: EntryObservation
  ): bool
  {
    if cmd.reverse then BaseEntryBeforeSpec(cmd, right, left)
    else BaseEntryBeforeSpec(cmd, left, right)
  }

  ghost predicate EntriesOrderedRelation(cmd: Schema.LsCmd, entries: seq<EntryObservation>)
  {
    forall i: nat, j: nat | i < j < |entries| ::
      !EntryBeforeSpec(cmd, entries[j], entries[i])
  }

  ghost predicate EntrySortingRelation(
    cmd: Schema.LsCmd,
    input: seq<EntryObservation>,
    output: seq<EntryObservation>
  )
  {
    multiset(output) == multiset(input) && EntriesOrderedRelation(cmd, output)
  }

  ghost predicate NativeCommandFields(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem)
  {
    cmd.statusContext.BoundStatusObservations? && |cmd.nativeInputs| == 1 &&
    cmd.nativeInputs[0].fs == fs &&
    cmd.nativeInputs[0].times == cmd.statusContext.observations &&
    cmd.nativeInputs[0].failures == cmd.statusContext.failures
  }

  ghost predicate NativeCallsFields(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                    calls: seq<Native.Call>)
  {
    NativeCommandFields(cmd,fs) &&
    if |calls| == 0 then true
    else Native.TraceFields(cmd.nativeInputs[0],calls[0].before,calls[|calls|-1].after,calls)
  }

  ghost opaque predicate MetadataObservationRelation(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, observation: EntryObservation)
  {
    if cmd.statusContext.BoundStatusObservations? then
      NativeCommandFields(cmd,fs) && |observation.nativeCalls| >= 1 &&
      observation.nativeCalls[0].before.status == observation.statusOrdinal &&
      NativeObservation.PathFields(cmd.nativeInputs[0],observation.nativeCalls[0].before,
                                   observation.nativeCalls[|observation.nativeCalls|-1].after,observation.displayName,
                                   observation.accessPath,observation.followSymlink,cmd.numericLong,observation.ok,
                                   observation.status,observation.err,observation.renderName,observation.linkErr,
                                   observation.nativeCalls)
    else
      match StatusResultSpec(cmd, fs, observation.statusOrdinal,
                             observation.accessPath, observation.followSymlink)
      case Ok(expected) =>
        observation.ok && observation.status == expected && observation.err == 0 &&
        observation.renderName == RenderNameSpec(cmd, fs, observation.displayName,
                                                 observation.accessPath, observation.followSymlink, cmd.numericLong, expected) &&
        observation.linkErr == LinkReadErrorSpec(cmd, fs, observation.accessPath,
                                                 observation.followSymlink, cmd.numericLong, expected)
      case Err(error) =>
        !observation.ok && observation.err == IOContract.IOErrorErrno(error) &&
        observation.linkErr == 0 && observation.renderName == observation.displayName
  }

  ghost predicate CanonicalDirentFields(observation: EntryObservation)
  {
    observation.ok &&
    observation.status == BenchWorld.DEFAULT_FILE_STATUS &&
    observation.err == 0 && observation.linkErr == 0 &&
    observation.renderName == observation.displayName &&
    !observation.followSymlink
  }

  ghost predicate NativeDirectoryReadFields(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                            observation: EntryObservation)
  {
    |observation.directoryRead| == 1 && NativeCallsFields(cmd,fs,observation.directoryRead) &&
    var call := observation.directoryRead[0];
    call.action.ReadAction? && call.action.readResult.Ok? && call.action.readResult.v.DirectoryItem? &&
    call.action.readResult.v.name == observation.displayName &&
    call.action.readResult.v.kind == observation.entryKind &&
    call.action.handle in call.before.context.capabilities &&
    var capability := call.before.context.capabilities[call.action.handle];
    capability.position in call.before.context.topology.nodes &&
    (observation.displayName == "." || observation.displayName == ".." ||
     observation.displayName in call.before.context.topology.nodes[capability.position].entries)
  }

  ghost predicate NativeDirentEntryFields(observation: EntryObservation, entry: BenchWorld.DirEntry)
  {
    |observation.directoryRead| == 1 && observation.directoryRead[0].action.ReadAction? &&
    var call := observation.directoryRead[0];
    call.action.handle in call.before.context.capabilities &&
    var capability := call.before.context.capabilities[call.action.handle];
    capability.position in call.before.context.topology.nodes &&
    (observation.displayName == "." || observation.displayName == ".." ||
     observation.displayName in call.before.context.topology.nodes[capability.position].entries) &&
    entry == NativeDirectory.EntryForName(call.before.context.topology,capability.position,observation.displayName)
  }

  ghost predicate DirectorySourceRelation(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                          path: BenchWorld.Path, observation: EntryObservation)
  {
    if cmd.statusContext.BoundStatusObservations? then
      VisibleNameSpec(cmd,observation.displayName) && NativeDirectoryReadFields(cmd,fs,observation) &&
      observation.accessPath == BenchWorld.AppendPath(path,observation.displayName) &&
      match observation.source
      case StatusEntryEvidence(ordinal) =>
        ordinal == observation.statusOrdinal &&
        EntryStatusRequiredSpec(cmd,ClassifiedDirentKindSpec(observation.entryKind),observation.displayName) &&
        MetadataObservationRelation(cmd,fs,observation) &&
        observation.followSymlink == (cmd.followMode == Schema.FollowAlways && EntryMetadataRequiredSpec(cmd))
      case DirentEntryEvidence(entry,kind) =>
        kind == ClassifiedDirentKindSpec(observation.entryKind) &&
        !EntryStatusRequiredSpec(cmd,kind,observation.displayName) &&
        DirentKindMatchesEntrySpec(kind,entry) &&
        IOContract.DirectoryEntryKindMatchesEntry(observation.entryKind,entry) &&
        NativeDirentEntryFields(observation,entry) && entry.name == observation.displayName &&
        CanonicalDirentFields(observation) && observation.nativeCalls == []
      case ImpliedDotEntryEvidence =>
        observation.entryKind == BenchWorld.DirectoryDirentKind &&
        !EntryRenderSortMetadataRequiredSpec(cmd) && CanonicalDirentFields(observation) &&
        observation.nativeCalls == [] && cmd.hiddenMode == Schema.All &&
        (observation.displayName == "." || observation.displayName == "..")
    else
      VisibleNameSpec(cmd, observation.displayName) &&
      match observation.source
      case StatusEntryEvidence(ordinal) =>
        ordinal == observation.statusOrdinal &&
        EntryStatusRequiredSpec(
          cmd, ClassifiedDirentKindSpec(observation.entryKind), observation.displayName) &&
        MetadataObservationRelation(cmd, fs, observation) &&
        observation.followSymlink ==
        (cmd.followMode == Schema.FollowAlways && EntryMetadataRequiredSpec(cmd)) &&
        ((cmd.hiddenMode == Schema.All && observation.displayName == "." &&
          observation.accessPath == BenchWorld.AppendPath(path, ".") &&
          observation.entryKind == BenchWorld.DirectoryDirentKind) ||
         (cmd.hiddenMode == Schema.All && observation.displayName == ".." &&
          observation.accessPath == BenchWorld.AppendPath(path, "..") &&
          observation.entryKind == BenchWorld.DirectoryDirentKind) ||
         (observation.accessPath == BenchWorld.AppendPath(path, observation.displayName) &&
          exists resolved: BenchWorld.Path, entry: BenchWorld.DirEntry ::
            IOContract.ResolvePathForMetadataFields(fs, ModelPathSpec(cmd, path), true) == Result.Ok(resolved) &&
            BenchWorld.FsContainsPath(fs, resolved) &&
            entry in IOContract.DirectoryEntriesForPathFields(fs, resolved) &&
            entry.name == observation.displayName &&
            IOContract.DirectoryEntryKindMatchesFilesystemFields(
              fs, resolved, entry.name, observation.entryKind)))
      case DirentEntryEvidence(entry, kind) =>
        kind == ClassifiedDirentKindSpec(observation.entryKind) &&
        !EntryStatusRequiredSpec(cmd, kind, observation.displayName) &&
        DirentKindMatchesEntrySpec(kind, entry) &&
        IOContract.DirectoryEntryKindMatchesEntry(observation.entryKind, entry) &&
        CanonicalDirentFields(observation) &&
        observation.accessPath == BenchWorld.AppendPath(path, observation.displayName) &&
        entry.name == observation.displayName &&
        (exists resolved: BenchWorld.Path ::
           IOContract.ResolvePathForMetadataFields(fs, ModelPathSpec(cmd, path), true) == Result.Ok(resolved) &&
           BenchWorld.FsContainsPath(fs, resolved) &&
           entry in IOContract.DirectoryEntriesForPathFields(fs, resolved) &&
           IOContract.DirectoryEntryKindMatchesFilesystemFields(
             fs, resolved, entry.name, observation.entryKind))
      case ImpliedDotEntryEvidence =>
        observation.entryKind == BenchWorld.DirectoryDirentKind &&
        !EntryRenderSortMetadataRequiredSpec(cmd) &&
        CanonicalDirentFields(observation) &&
        cmd.hiddenMode == Schema.All &&
        (observation.displayName == "." || observation.displayName == "..") &&
        observation.accessPath == BenchWorld.AppendPath(path, observation.displayName)
  }

  ghost opaque predicate DistinctDisplayNames(observations: seq<EntryObservation>)
    decreases |observations|
  {
    |observations| == 0 ||
    (DistinctDisplayNames(observations[..|observations| - 1]) &&
     forall i: nat :: i < |observations| - 1 ==>
                        observations[i].displayName != observations[|observations| - 1].displayName)
  }

  ghost predicate DirectoryObservationRelation(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    firstStatus: nat,
    afterStatus: nat,
    complete: bool,
    observations: seq<EntryObservation>, expected: set<BenchWorld.DirEntry>
  )
  {
    (exists statusCuts: seq<nat> ::
       |statusCuts| == |observations| + 1 &&
       statusCuts[0] == firstStatus &&
       statusCuts[|observations|] == afterStatus &&
       (forall i: nat | i < |observations| ::
          observations[i].statusOrdinal == statusCuts[i] &&
          statusCuts[i + 1] == statusCuts[i] + EntryStatusCallCount(observations[i]))) &&
    DistinctDisplayNames(observations) &&
    (forall i: nat :: i < |observations| ==>
                        DirectorySourceRelation(cmd, fs, path, observations[i])) &&
    (complete ==>
       (cmd.hiddenMode == Schema.All ==>
          (exists i: nat :: i < |observations| && observations[i].displayName == ".") &&
          (exists i: nat :: i < |observations| && observations[i].displayName == "..")) &&
       if cmd.statusContext.BoundStatusObservations? then
         forall entry | entry in expected && VisibleNameSpec(cmd,entry.name) ::
           exists i: nat :: i < |observations| && observations[i].displayName == entry.name
       else match IOContract.ResolvePathForMetadataFields(fs, ModelPathSpec(cmd, path), true)
            case Err(_) => true
            case Ok(resolved) =>
              BenchWorld.FsContainsPath(fs, resolved) ==>
                forall entry: BenchWorld.DirEntry ::
                  entry in IOContract.DirectoryEntriesForPathFields(fs, resolved) &&
                  VisibleNameSpec(cmd, entry.name) ==>
                    exists i: nat ::
                      i < |observations| && observations[i].displayName == entry.name)
  }

  ghost predicate FragmentsConcatenate(
    fragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |combined| &&
    forall i: nat {:trigger cuts[i]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] <= |combined| &&
      cuts[i + 1] == cuts[i] + |fragments[i]| &&
      combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate ObservationPiecesRelation(
    cmd: Schema.LsCmd,
    observations: seq<EntryObservation>,
    outputFragments: seq<BenchWorld.Bytes>
  )
  {
    |outputFragments| == |observations| &&
    forall i: nat | i < |observations| ::
      outputFragments[i] ==
      (if observations[i].ok
       then RenderAlignedEntrySpec(cmd, observations[i].renderName, observations[i].status, ObservationWidthsSpec(cmd, observations))
       else RenderFailedEntrySpec(cmd, observations[i], ObservationWidthsSpec(cmd, observations)))
  }

  ghost predicate ObservationErrorsRelation(
    displayPath: BenchWorld.Path,
    observations: seq<EntryObservation>,
    errorFragments: seq<BenchWorld.Bytes>
  )
  {
    |errorFragments| == |observations| &&
    forall i: nat | i < |observations| :: errorFragments[i] ==
                                          EntryErrorTextSpec(EntryDiagnosticPathSpec(displayPath, observations[i].displayName), observations[i])
  }

  ghost predicate DirectoryExpectedEntries(trace: DirectoryTrace, expected: set<BenchWorld.DirEntry>)
  {
    trace.DirectoryTrace? && |trace.openCalls| == 1 &&
    var context := trace.openCalls[0].after.context;
    trace.handle in context.capabilities &&
    var capability := context.capabilities[trace.handle];
    capability.position in context.topology.nodes &&
    capability.remaining <= context.topology.nodes[capability.position].entries.Keys+{".",".."} &&
    expected == NativeDirectory.EntriesForNames(context.topology,capability.position,capability.remaining)
  }

  ghost opaque predicate DirectoryListingRelation(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    firstStatus: nat,
    afterStatus: nat,
    observations: seq<EntryObservation>,
    readErr: int,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool, nativeTrace: DirectoryTrace
  )
  {
    exists rawObservations: seq<EntryObservation>,
      outputFragments: seq<BenchWorld.Bytes>, outputCuts: seq<nat>,
      errorFragments: seq<BenchWorld.Bytes>, errorCuts: seq<nat>,
      entryOutput: BenchWorld.Bytes, entryErrors: BenchWorld.Bytes, closeErr: int,
      expectedEntries: set<BenchWorld.DirEntry> ::
      DirectoryCloseObservation(cmd, fs, path, readErr, closeErr) &&
      ReadCloseDirectoryTrace(cmd, fs, path, nativeTrace, readErr, closeErr) &&
      nativeTrace.raw == rawObservations && DirectoryExpectedEntries(nativeTrace,expectedEntries) &&
      DirectoryObservationRelation(cmd, fs, path, firstStatus, afterStatus,
                                   readErr == 0, rawObservations,expectedEntries) &&
      EntrySortingRelation(cmd, rawObservations, observations) &&
      ObservationPiecesRelation(cmd, observations, outputFragments) &&
      ObservationErrorsRelation(displayPath, rawObservations, errorFragments) &&
      FragmentsConcatenate(outputFragments, entryOutput, outputCuts) &&
      output == TotalLineSpec(cmd, rawObservations) + entryOutput &&
      FragmentsConcatenate(errorFragments, entryErrors, errorCuts) &&
      errors == entryErrors +
      (if readErr == 0 then [] else ReadDirectoryErrorMessageSpec(displayPath, readErr)) +
      CloseDirectoryErrorMessageSpec(displayPath, closeErr) &&
      hadError == (readErr != 0 || closeErr != 0 ||
                   exists i: nat :: i < |observations| && ObservationFailedSpec(observations[i]))
  }

  function ChildDisplayPath(displayPath: BenchWorld.Path, name: string): BenchWorld.Path
  {
    TrailingSlashCutExists(displayPath);
    var cut: nat :| cut <= |displayPath| && TrailingSlashCut(displayPath, cut);
    displayPath[..cut] + "/" + name
  }

  predicate TrailingSlashCut(path: string, cut: nat)
  {
    cut <= |path| && (cut == 0 || path[cut - 1] != '/') &&
    (forall j: nat :: cut <= j < |path| ==> path[j] == '/')
  }

  lemma TrailingSlashCutExists(path: string)
    ensures exists cut: nat :: TrailingSlashCut(path, cut)
    decreases |path|
  {
    if |path| > 0 && path[|path| - 1] == '/' {
      TrailingSlashCutExists(path[..|path| - 1]);
      var cut: nat :| TrailingSlashCut(path[..|path| - 1], cut);
      assert forall j: nat :: cut <= j < |path| ==> path[j] == '/';
      assert TrailingSlashCut(path, cut);
    } else {
      assert TrailingSlashCut(path, |path|);
    }
  }

  function RecursiveCycleMessageSpec(displayPath: BenchWorld.Path): BenchWorld.Bytes
  {
    "ls: " + SE.SpecQuoteFBytes(Utf8.Encode(displayPath)) +
    ": not listing already-listed directory\n"
  }

  function RecursiveNodeListed(tree: RecursiveWitness): bool
  {
    tree.openOk && tree.statusOk && !tree.cycle
  }

  function RecursiveOutputFragments(tree: RecursiveWitness): seq<BenchWorld.Bytes>
  {
    seq(|tree.observations|, i requires i < |tree.observations| =>
      if i in tree.children && RecursiveNodeListed(tree.children[i])
      then "\n" + tree.children[i].output else [])
  }

  ghost function RecursiveErrorFragments(
    displayPath: BenchWorld.Path, tree: RecursiveWitness
  ): seq<BenchWorld.Bytes>
  {
    seq(|tree.observations|, i requires i < |tree.observations| =>
      if i in tree.cycles then
        RecursiveCycleMessageSpec(
          ChildDisplayPath(displayPath, tree.observations[i].displayName))
      else if i in tree.children then tree.children[i].errors
      else [])
  }

  ghost predicate RecursiveNativeCallsFields(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                             tree: RecursiveWitness)
  {
    tree.nativeTrace.DirectoryTrace? && NativeCallsFields(cmd,fs,tree.nativeCalls) &&
    |tree.nativeCalls| >= |tree.nativeTrace.nativeCalls| > 0 &&
    tree.nativeCalls[..|tree.nativeTrace.nativeCalls|] == tree.nativeTrace.nativeCalls &&
    tree.nativeCalls[0].before.status == tree.firstStatus &&
    tree.nativeCalls[|tree.nativeCalls|-1].after.status == tree.afterStatus &&
    if !tree.openOk || !tree.statusOk || tree.cycle then
      tree.nativeCalls == tree.nativeTrace.nativeCalls && tree.childNativePieces == [] && tree.childNativeCuts == [0]
    else |tree.childNativePieces| == |tree.observations| &&
         NativeCallFragments(tree.childNativePieces,tree.nativeCalls[|tree.nativeTrace.nativeCalls|..],tree.childNativeCuts) &&
         forall i: nat | i < |tree.observations| ::
           tree.childNativePieces[i] == (if i in tree.children then tree.children[i].nativeCalls else [])
  }

  ghost predicate RecursiveDirectoryRelation(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path,
    accessPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>,
    tree: RecursiveWitness
  )
    decreases tree
  {
    RecursiveNativeDirectoryTrace(cmd, fs, accessPath, tree) &&
    RecursiveNativeCallsFields(cmd,fs,tree) &&
    cmd.statusContext.BoundStatusObservations? &&
    OpenDirectoryObservation(cmd, fs, accessPath, tree.openOk, tree.openErr) &&
    (tree.openOk ==> OpenedDirectoryStatusObservation(
         cmd, fs, accessPath, tree.firstStatus, tree.statusOk,
         tree.openedStatus, tree.statusErr)) &&
    (if !tree.openOk then
       tree.openErr > 0 && !tree.statusOk && !tree.cycle &&
       tree.listingFirstStatus == tree.firstStatus &&
       tree.listingAfterStatus == tree.firstStatus &&
       tree.afterStatus == tree.firstStatus &&
       tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
       tree.output == [] &&
       tree.errors == OpenDirectoryErrorMessageSpec(displayPath, tree.openErr) &&
       tree.hadError
     else if !tree.statusOk then
       tree.openErr == 0 && tree.statusErr > 0 && !tree.cycle &&
       tree.listingFirstStatus == tree.firstStatus+1 &&
       tree.listingAfterStatus == tree.firstStatus+1 &&
       tree.afterStatus == tree.firstStatus+1 &&
       tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
       tree.output == [] &&
       tree.errors == DirectoryIdentityErrorMessageSpec(displayPath, tree.statusErr) &&
       tree.hadError
     else
       tree.openErr == 0 && tree.statusErr == 0 &&
       tree.listingFirstStatus == tree.firstStatus + 1 &&
       tree.openedStatus.kind == BenchWorld.DirectoryKind &&
       (if tree.cycle then
          tree.openedStatus.hostKey in ancestors &&
          tree.listingAfterStatus == tree.listingFirstStatus &&
          tree.afterStatus == tree.listingFirstStatus &&
          tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
          tree.output == [] && tree.errors == RecursiveCycleMessageSpec(displayPath) &&
          tree.hadError
        else
          tree.openedStatus.hostKey !in ancestors &&
          DirectoryListingRelation(
            cmd, displayPath, fs, accessPath, tree.listingFirstStatus,
            tree.listingAfterStatus,
            tree.observations, tree.readErr,
            tree.listingOutput, tree.listingErrors, tree.listingHadError, tree.nativeTrace) &&
          (exists statusCuts: seq<nat> ::
             |statusCuts| == |tree.observations| + 1 &&
             statusCuts[0] == tree.listingAfterStatus &&
             statusCuts[|tree.observations|] == tree.afterStatus &&
             (forall i: nat | i < |tree.observations| ::
                (if i in tree.children then
                   tree.children[i].firstStatus == statusCuts[i] &&
                   tree.children[i].afterStatus == statusCuts[i + 1]
                 else statusCuts[i] == statusCuts[i + 1]))) &&
          tree.cycles <= tree.children.Keys &&
          (forall i: nat :: i < |tree.observations| ==>
                              (i in tree.children <==> RecursiveEntryEligible(tree.observations[i])) &&
                              (i in tree.cycles <==> i in tree.children && tree.children[i].cycle)) &&
          (forall i: nat :: i in tree.children ==>
                              i < |tree.observations| &&
                              RecursiveDirectoryRelation(
                                cmd, fs,
                                ChildDisplayPath(displayPath, tree.observations[i].displayName),
                                tree.observations[i].accessPath,
                                ancestors + {tree.openedStatus.hostKey}, tree.children[i])) &&
          (exists outputCuts: seq<nat>, errorCuts: seq<nat>,
             childOutput: BenchWorld.Bytes, childErrors: BenchWorld.Bytes ::
             FragmentsConcatenate(RecursiveOutputFragments(tree), childOutput, outputCuts) &&
             FragmentsConcatenate(
               RecursiveErrorFragments(displayPath, tree), childErrors, errorCuts) &&
             tree.output == DirectoryHeaderSpec(displayPath) + tree.listingOutput + childOutput &&
             tree.errors == tree.listingErrors + childErrors) &&
          tree.hadError ==
          (tree.listingHadError ||
           exists i: nat :: i in tree.children && tree.children[i].hadError)))
  }

  function OperandAsEntry(observation: OperandObservation): EntryObservation
  {
    EntryObservation(
      observation.operand, observation.operand, observation.path, false,
      observation.ok, observation.status, observation.err, 0,
      BenchWorld.UnknownDirentKind, 0, StatusEntryEvidence(0))
  }

  function OperandClassRank(kind: OperandClass): nat
  {
    match kind
    case DirectOperand => 0
    case ExpandedDirectory => 1
    case AccessFailure => 2
  }

  opaque function OperandBeforeSpec(
    cmd: Schema.LsCmd, left: OperandObservation, right: OperandObservation
  ): bool
  {
    if left.operandClass != right.operandClass then
      OperandClassRank(left.operandClass) < OperandClassRank(right.operandClass)
    else
      EntryBeforeSpec(cmd, OperandAsEntry(left), OperandAsEntry(right))
  }

  ghost predicate OperandSortingRelation(
    cmd: Schema.LsCmd,
    input: seq<OperandObservation>,
    output: seq<OperandObservation>
  )
  {
    multiset(output) == multiset(input) &&
    OperandObservationsOrdered(cmd, output)
  }

  ghost predicate OperandObservationsOrdered(
    cmd: Schema.LsCmd, observations: seq<OperandObservation>
  )
  {
    forall i: nat, j: nat | i < j < |observations| ::
      !OperandBeforeSpec(cmd, observations[j], observations[i])
  }

  ghost function ObservedOperandStatusResult(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                             observation: OperandObservation): BenchWorld.IOResult<BenchWorld.FileStatus>
  {
    if cmd.statusContext.BoundStatusObservations? && |observation.statusCalls| > 0 &&
       observation.statusCalls[|observation.statusCalls|-1].action.StatusAction?
    then observation.statusCalls[|observation.statusCalls|-1].action.statusResult
    else OperandStatusResultSpec(cmd,fs,observation.path,observation.firstStatus)
  }

  ghost function ObservedOperandStatusCallCount(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                                observation: OperandObservation): nat
  {
    if cmd.statusContext.BoundStatusObservations? then |observation.statusCalls|
    else OperandStatusCallCountSpec(cmd,fs,observation.path,observation.firstStatus)
  }

  ghost predicate OperandNativeFields(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                      observation: OperandObservation)
  {
    if !cmd.statusContext.BoundStatusObservations? then true
    else NativeCommandFields(cmd,fs) && |observation.statusCalls| > 0 &&
         var first := observation.statusCalls[0].before;
         var last := observation.statusCalls[|observation.statusCalls|-1].after;
         first.status == observation.firstStatus &&
         NativeObservation.OperandFields(cmd.nativeInputs[0],first,last,observation.path,
                                         ImplicitDirectoryFollowSpec(cmd),ExplicitCommandLineFollowSpec(cmd),
                                         observation.ok,observation.status,observation.err,observation.statusCalls) &&
         NativeCallsFields(cmd,fs,observation.nativeCalls) && |observation.nativeCalls| > 0 &&
         observation.nativeCalls[0].before == first &&
         observation.nativeCalls[|observation.nativeCalls|-1].after.status == observation.afterStatus &&
         if observation.operandClass == DirectOperand then
           observation.nativeCalls == observation.statusCalls+observation.renderCalls &&
           NativeObservation.RenderFields(cmd.nativeInputs[0],last,
                                          observation.nativeCalls[|observation.nativeCalls|-1].after,
                                          observation.operand,observation.path,ExplicitCommandLineFollowSpec(cmd),cmd.numericLong,
                                          observation.status,observation.renderName,observation.linkErr,observation.renderCalls)
         else observation.renderCalls == [] && observation.linkErr == 0 &&
              (observation.operandClass == AccessFailure ==> observation.nativeCalls == observation.statusCalls)
  }

  ghost predicate DirectOperandRenderFields(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                            observation: OperandObservation, status: BenchWorld.FileStatus)
  {
    if cmd.statusContext.BoundStatusObservations? then
      OperandNativeFields(cmd,fs,observation) &&
      observation.accessErrors == ReadLinkErrorMessageSpec(observation.operand,observation.linkErr) &&
      observation.failed == (observation.linkErr != 0)
    else observation.renderName == RenderNameSpec(cmd,fs,observation.operand,observation.path,
                                                  ExplicitCommandLineFollowSpec(cmd),cmd.numericLong,status) &&
         observation.accessErrors == ReadLinkErrorMessageSpec(observation.operand,
                                                              LinkReadErrorSpec(cmd,fs,observation.path,ExplicitCommandLineFollowSpec(cmd),cmd.numericLong,status)) &&
         observation.failed == (LinkReadErrorSpec(cmd,fs,observation.path,
                                                  ExplicitCommandLineFollowSpec(cmd),cmd.numericLong,status) != 0)
  }

  ghost predicate OperandObservationRelation(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    observation: OperandObservation
  )
  {
    OperandNativeFields(cmd,fs,observation) &&
    observation.index < |cmd.operands| &&
    observation.operand == cmd.operands[observation.index] &&
    observation.path == OperandPathSpec(cmd, cwd, observation.operand) &&
    (observation.sectionAvailable ==>
       observation.operandClass == ExpandedDirectory &&
       OpenDirectoryObservation(cmd, fs, observation.path, true, 0)) &&
    (observation.operandClass == ExpandedDirectory ==>
       observation.nativeTrace.DirectoryTrace? &&
       BoundOpenDirectoryTrace(cmd, fs, observation.path, observation.nativeTrace,
                               observation.sectionAvailable,
                               if observation.sectionAvailable then 0 else observation.nativeTrace.openErr) &&
       (!observation.sectionAvailable ==>
          FailedOpenDirectoryTrace(cmd, fs, observation.path, observation.nativeTrace) &&
          observation.sectionErrors == OpenDirectoryErrorMessageSpec(
            observation.operand, observation.nativeTrace.openErr))) &&
    match ObservedOperandStatusResult(cmd,fs,observation)
    case Err(error) =>
      !observation.ok && !observation.sectionAvailable &&
      observation.err == IOContract.IOErrorErrno(error) &&
      observation.operandClass == AccessFailure &&
      observation.afterStatus == observation.firstStatus +
      ObservedOperandStatusCallCount(cmd,fs,observation) &&
      observation.body == [] &&
      observation.accessErrors == AccessErrorMessageSpec(
        observation.operand, observation.err) &&
      observation.sectionErrors == [] && observation.failed && !observation.hasCycle &&
      !observation.directoryFailed
    case Ok(status) =>
      observation.ok && observation.status == status && observation.err == 0 &&
      if status.kind == BenchWorld.DirectoryKind && !cmd.listDirectories then
        observation.accessErrors == [] &&
        observation.operandClass == ExpandedDirectory &&
        if observation.sectionAvailable then
          if cmd.recursive then
            exists tree: RecursiveWitness ::
              RecursiveDirectoryRelation(
                cmd, fs, observation.operand, observation.path,
                {}, tree) &&
              tree.openOk && tree.nativeTrace == observation.nativeTrace &&
              observation.nativeCalls == observation.statusCalls+tree.nativeCalls &&
              tree.firstStatus == observation.firstStatus +
              ObservedOperandStatusCallCount(cmd,fs,observation) &&
              tree.afterStatus == observation.afterStatus &&
              observation.body == tree.output &&
              observation.sectionErrors == tree.errors &&
              observation.failed == tree.hadError &&
              observation.hasCycle == RecursiveHasCycle(tree) &&
              observation.directoryFailed == RecursiveRootFailed(tree)
          else
            !observation.hasCycle &&
            exists entries: seq<EntryObservation>, readErr: int,
              listingOutput: BenchWorld.Bytes
              {:trigger DirectoryListingRelation(
                cmd, observation.operand, fs, observation.path,
                observation.firstStatus + ObservedOperandStatusCallCount(cmd,fs,observation),
                observation.afterStatus, entries, readErr,
                listingOutput, observation.sectionErrors, observation.failed, observation.nativeTrace)} ::
              DirectoryListingRelation(
                cmd, observation.operand, fs, observation.path,
                observation.firstStatus + ObservedOperandStatusCallCount(cmd,fs,observation),
                observation.afterStatus, entries, readErr,
                listingOutput, observation.sectionErrors, observation.failed, observation.nativeTrace) &&
              observation.directoryFailed == DirectoryOperationFailed(observation.nativeTrace, readErr) &&
              observation.nativeCalls == observation.statusCalls+observation.nativeTrace.nativeCalls &&
              observation.body ==
              (if |cmd.operands| > 1
               then DirectoryHeaderSpec(observation.operand)
               else []) + listingOutput
        else
          observation.afterStatus == observation.firstStatus +
          ObservedOperandStatusCallCount(cmd,fs,observation) &&
          observation.body == [] &&
          observation.nativeCalls == observation.statusCalls+observation.nativeTrace.nativeCalls &&
          (exists openErr: int ::
             OpenDirectoryObservation(cmd, fs, observation.path, false, openErr) &&
             observation.sectionErrors == OpenDirectoryErrorMessageSpec(
               observation.operand, openErr)) &&
          observation.failed && !observation.hasCycle && observation.directoryFailed
      else
        observation.operandClass == DirectOperand &&
        observation.afterStatus == observation.firstStatus +
        ObservedOperandStatusCallCount(cmd,fs,observation) &&
        !observation.sectionAvailable &&
        DirectOperandRenderFields(cmd,fs,observation,status) &&
        observation.body == RenderEntrySpec(cmd,observation.renderName,status) &&
        observation.sectionErrors == [] && !observation.hasCycle && !observation.directoryFailed
  }

  ghost predicate DirectPositionRelation(
    sorted: seq<OperandObservation>, positions: seq<nat>
  )
  {
    (forall k: nat :: k < |positions| ==> positions[k] < |sorted|) &&
    (forall k: nat :: k + 1 < |positions| ==> positions[k] < positions[k + 1]) &&
    (forall i: nat :: i < |sorted| ==>
                        (sorted[i].operandClass == DirectOperand <==>
                         exists k: nat :: k < |positions| && positions[k] == i))
  }

  ghost predicate DirectoryPositionRelation(
    sorted: seq<OperandObservation>, positions: seq<nat>
  )
  {
    (forall k: nat :: k < |positions| ==> positions[k] < |sorted|) &&
    (forall k: nat :: k + 1 < |positions| ==> positions[k] < positions[k + 1]) &&
    (forall i: nat :: i < |sorted| ==>
                        (sorted[i].operandClass == ExpandedDirectory && sorted[i].sectionAvailable <==>
                         exists k: nat :: k < |positions| && positions[k] == i))
  }

  ghost predicate {:isolate_assertions} OutputGroupsRelation(
    cmd: Schema.LsCmd,
    sorted: seq<OperandObservation>,
    groups: seq<OutputGroup>
  )
  {
    exists direct: seq<nat>, directories: seq<nat>, cuts: seq<nat>, body: BenchWorld.Bytes
      {:trigger DirectPositionRelation(sorted, direct), DirectoryPositionRelation(sorted, directories), |cuts|, |body|} ::
      DirectPositionRelation(sorted, direct) &&
      DirectoryPositionRelation(sorted, directories) &&
      FragmentsConcatenate(
        seq(|direct|, k requires 0 <= k < |direct| => RenderOperandSpec(cmd, sorted, direct[k])),
        body, cuts) &&
      // A queued directory still calls for a separator after the direct listings
      // when every directory section is unavailable.
      var suffix := if |directories| == 0 &&
                       (exists i: nat :: i < |sorted| && sorted[i].operandClass == ExpandedDirectory)
                    then "\n" else [];
      var directGroup := if |direct| == 0 then [] else [
        OutputGroup(seq(|direct|, k requires 0 <= k < |direct| => sorted[direct[k]].index),
                    body + suffix, false)];
      var directoryGroups := seq(|directories|, k requires 0 <= k < |directories| =>
        OutputGroup([sorted[directories[k]].index], sorted[directories[k]].body, true));
      groups == directGroup + directoryGroups
  }

  ghost predicate SeparatedGroupsRelation(
    groups: seq<OutputGroup>, output: BenchWorld.Bytes
  )
  {
    var fragments := seq(|groups|, i requires 0 <= i < |groups| =>
      (if i == 0 then [] else "\n") + groups[i].body);
    exists cuts: seq<nat> :: FragmentsConcatenate(fragments, output, cuts)
  }

  ghost predicate OperandErrorsRelation(
    observations: seq<OperandObservation>, sorted: seq<OperandObservation>,
    errors: BenchWorld.Bytes
  )
  {
    var access := seq(|observations|, i requires 0 <= i < |observations| => observations[i].accessErrors);
    var sections := seq(|sorted|, i requires 0 <= i < |sorted| => sorted[i].sectionErrors);
    exists accessCuts: seq<nat>, sectionCuts: seq<nat>,
      accessErrors: BenchWorld.Bytes, sectionErrors: BenchWorld.Bytes ::
      FragmentsConcatenate(access, accessErrors, accessCuts) &&
      FragmentsConcatenate(sections, sectionErrors, sectionCuts) &&
      errors == accessErrors + sectionErrors
  }

  ghost predicate OperandStatusIntervals(
    observations: seq<OperandObservation>, firstStatus: nat, afterStatus: nat
  )
  {
    if |observations| == 0 then afterStatus == firstStatus
    else observations[0].firstStatus == firstStatus &&
         observations[|observations| - 1].afterStatus == afterStatus &&
         (forall i: nat | i + 1 < |observations| ::
           observations[i].afterStatus == observations[i + 1].firstStatus)
  }

  ghost predicate RunNativeFields(cmd: Schema.LsCmd, fs: BenchWorld.FileSystem,
                                  firstStatus: nat, afterStatus: nat, observations: seq<OperandObservation>,
                                  afterNative: seq<Native.State>)
  {
    if !cmd.statusContext.BoundStatusObservations? then true
    else NativeCommandFields(cmd,fs) && |cmd.nativeStart| == 1 && |afterNative| == 1 &&
         cmd.nativeStart[0].status == firstStatus && afterNative[0].status == afterStatus &&
         exists calls: seq<Native.Call>, cuts: seq<nat>
           {:trigger |calls|, |cuts|} ::
           NativeCallFragments(seq(|observations|,i requires 0 <= i < |observations| => observations[i].nativeCalls),calls,cuts) &&
           Native.TraceFields(cmd.nativeInputs[0],cmd.nativeStart[0],afterNative[0],calls)
  }

  ghost opaque predicate RunRelation(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    firstStatus: nat,
    afterStatus: nat,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    exit: int, afterNative: seq<Native.State> := []
  )
  {
    exists observations: seq<OperandObservation>,
      sorted: seq<OperandObservation>, groups: seq<OutputGroup> ::
      RunNativeFields(cmd,fs,firstStatus,afterStatus,observations,afterNative) &&
      |observations| == |cmd.operands| &&
      OperandStatusIntervals(observations, firstStatus, afterStatus) &&
      (forall i: nat | i < |observations| ::
         observations[i].index == i &&
         OperandObservationRelation(cmd, fs, cwd, observations[i])) &&
      OperandSortingRelation(cmd, observations, sorted) &&
      OutputGroupsRelation(cmd, sorted, groups) &&
      SeparatedGroupsRelation(groups, output) &&
      OperandErrorsRelation(observations, sorted, errors) &&
      exit == OperandExitSpec(observations)
  }

  // The same observable relation is available to exact execution classifiers.
  datatype NativeRunContext = NativeRunContext(
    ghost inputs: seq<Native.Inputs>, ghost before: seq<Native.State>, ghost after: seq<Native.State>)

  ghost predicate ObservedSpec(
    raw: Schema.LsCmdRaw,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    env: map<string, string>,
    now: int,
    observations: BenchWorld.StatusTimeObservations,
    failures: (BenchWorld.NativeFailureRequest) -> int,
    handles: map<int, BenchWorld.DirHandleState>,
    firstStatus: nat,
    afterStatus: nat,
    beforeStdout: BenchWorld.Bytes,
    afterStdout: BenchWorld.Bytes,
    beforeStderr: BenchWorld.Bytes,
    afterStderr: BenchWorld.Bytes,
    exit: int,
    native: NativeRunContext := NativeRunContext([],[],[])
  )
  {
    var cmd := Schema.WithStatusObservations(
                 EffectiveCommandSpec(raw,env,now),observations,firstStatus,failures,handles,cwd,native.inputs,native.before);
    (cmd.mode != Schema.ModeRun ==> afterStatus == firstStatus) &&
    if cmd.mode == Schema.ModeHelp then
      afterStdout == beforeStdout + HelpTextSpec &&
      afterStderr == beforeStderr &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      afterStdout == beforeStdout + VersionTextSpec &&
      afterStderr == beforeStderr &&
      exit == 0
    else if cmd.mode != Schema.ModeRun then
      afterStdout == beforeStdout &&
      afterStderr == beforeStderr + InvalidModeMessageSpec(cmd.mode) &&
      exit == (if cmd.mode.ModeInvalidTime? then 1 else 2)
    else
      exists output: BenchWorld.Bytes, errors: BenchWorld.Bytes ::
        RunRelation(cmd, fs, cwd, firstStatus, afterStatus,
                    output,errors,exit,native.after) &&
        afterStdout == beforeStdout + output &&
        afterStderr == beforeStderr + errors
  }


  function WriteErrorText(reason: string): StreamWorld.Bytes
  {
    "ls: write error: " + Utf8.Encode(reason) + "\n"
  }

  ghost predicate EmissionOutcomeFields(
    beforeOut: StreamWorld.Bytes, beforeErr: StreamWorld.Bytes,
    afterOut: StreamWorld.Bytes, afterErr: StreamWorld.Bytes,
    observations: (StreamWorld.TrustedStreamRequest) -> StreamWorld.TrustedStreamResult,
    output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
    normalExit: int, exit: int,
    committed: nat, outErr: int, errCommitted: nat, errErr: int
  )
  {
    (if |output| == 0 then afterOut == beforeOut && committed == 0 && outErr == 0
     else StreamContract.WriteStdoutSpec(beforeOut, observations, afterOut, output, committed, outErr)) &&
    var finalDiagnostics := diagnostics +
                            (if outErr == 0 then [] else WriteErrorText(StreamContract.CLocaleErrnoTextResult(outErr)));
    (if |finalDiagnostics| == 0 then afterErr == beforeErr && errCommitted == 0 && errErr == 0
     else StreamContract.WriteStderrSpec(beforeErr, observations, afterErr, finalDiagnostics, errCommitted, errErr)) &&
    exit == (if outErr != 0 || errErr != 0 then 2 else normalExit)
  }

  ghost predicate EmissionFields(
    beforeOut: StreamWorld.Bytes, beforeErr: StreamWorld.Bytes,
    afterOut: StreamWorld.Bytes, afterErr: StreamWorld.Bytes,
    observations: (StreamWorld.TrustedStreamRequest) -> StreamWorld.TrustedStreamResult,
    output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes,
    normalExit: int, exit: int
  )
  {
    exists committed: nat, outErr: int, errCommitted: nat, errErr: int ::
      EmissionOutcomeFields(beforeOut, beforeErr, afterOut, afterErr, observations,
                            output, diagnostics, normalExit, exit,
                            committed, outErr, errCommitted, errErr)
  }
  twostate predicate PreparedSpec(raw: Schema.LsCmdRaw, io: BenchIO.IO, exit: int, plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    reads io.fsRegion, io.cwdRegion, io.envRegion, io.nowRegion,
          io.statusObservationsRegion, io.trustedNativeFailuresRegion, io.dirHandlesRegion, io.directoryStateRegion
  {
    io.dirHandles() == old(io.dirHandles()) &&
    ObservedSpec(raw, old(io.fs()), old(io.cwd()), old(io.env()), old(io.now()),
                 io.statusObservations(), io.trustedNativeFailures(), old(io.dirHandles()), old(io.statusCursor()), io.statusCursor(),
                 [],plannedStdout,[],plannedStderr,exit,NativeRunContext(
                   [Native.Inputs(old(io.fs()),io.statusObservations(),old(io.trustedNativeFailures()),old(io.directoryObservations()))],
                   [Native.State(old(io.cwdContext()),old(io.statusCursor()))],
                   [Native.State(io.cwdContext(),io.statusCursor())]))
  }

  twostate predicate Spec(raw: Schema.LsCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int ::
      PreparedSpec(raw, io, normalExit, output, diagnostics) &&
      EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                     io.trustedStreams(), output, diagnostics, normalExit, exit)
  }
}
