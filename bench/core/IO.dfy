include "World.dfy"
include "IOContract.dfy"
include "SecurityModel.dfy"

module {:verify false} BenchIO {
  import opened BenchWorld
  import C = IOContract
  import Sec = SecurityModel

  // Public trusted-library API: observers, immutable footprints and operations.
  // See ../../docs/core-api.md for the module map, contracts and frames.
  export
    reveals IO, FsRegion, PropsRegion, CwdRegion, EnvRegion, StdinRegion, StdoutRegion, StderrRegion, DirHandlesRegion, NowRegion, CredentialsRegion, TrustedTimeParsesRegion, TrustedStreamsRegion, TrustedFilesystemRegion, StdoutTimestampRegion
    provides Process, IO.Init
    reveals IO.Footprint
    reveals SecurityRegion, UmaskRegion
    provides BenchWorld, C, Sec, Exit
    reveals CLocaleErrnoTextResult, QuoteafPathResult, QuoteArgumentResult
    provides IO.securityRegion, IO.security
    provides IO.umaskRegion, IO.umask
    provides IO.fsRegion, IO.fs
    provides IO.propsRegion, IO.props
    provides IO.cwdRegion, IO.cwd
    provides IO.envRegion, IO.env
    provides IO.stdinRegion, IO.stdin
    provides IO.stdoutRegion, IO.stdout
    provides IO.stderrRegion, IO.stderr
    provides IO.dirHandlesRegion, IO.dirHandles
    provides IO.nowRegion, IO.now
    provides IO.trustedTimeParsesRegion, IO.trustedTimeParses
    provides IO.trustedStreamsRegion, IO.trustedStreams
    provides IO.trustedFilesystemRegion, IO.trustedFilesystem
    provides IO.stdoutTimestampRegion, IO.stdoutTimestamp
    provides IO.credentialsRegion, IO.credentials
    provides IO.ReadFile, IO.ReadLink, IO.ReadStdinAll
    provides IO.AppendStdout, IO.AppendStderr
    provides IO.ReadFileWithOutcome, IO.ReadStdinWithOutcome
    provides IO.WriteStdoutWithOutcome, IO.WriteStderrWithOutcome
    provides IO.GetCLocaleErrnoText, IO.QuoteafPath, IO.QuoteArgument
    provides IO.GetCwd, IO.GetEnv, IO.GetEnvironment, IO.GetLoginName, IO.Now
    provides IO.ParseTimestamp, IO.ParseDate
    provides IO.PathExists, IO.CreateFile, IO.WriteFile, IO.CreateSymlink, IO.DeletePath
    provides IO.CreateDirectory, IO.RemoveDirectory, IO.CreateHardLink, IO.UnlinkPath
    provides IO.TruncateFile, IO.CreateSpecialNode, IO.Sync
    provides IO.SetFileTimesNow, IO.SetFileAccessTimeNow, IO.SetFileModificationTimeNow
    provides IO.GetFileTimes, IO.SetFileTimes
    provides IO.SetStdoutTimesNow, IO.SetStdoutAccessTimeNow, IO.SetStdoutModificationTimeNow
    provides IO.SetStdoutTimes
    provides IO.GetFileMode, IO.GetFileStatus, IO.SetFileMode, IO.GetUmask
    provides IO.OpenDir, IO.ResolvePathIdentity, IO.ReadDir, IO.CloseDir
    provides IO.IsDirectory, IO.IsDirectoryStrict, IO.IsSymlink, IO.RenamePath

  class SecurityRegion {
    ghost var value: Sec.FilesystemSecurityContext

    ghost constructor Init(initial: Sec.FilesystemSecurityContext)
      ensures value == initial
    {
      value := initial;
    }
  }

  class UmaskRegion {
    ghost var value: bv32

    ghost constructor Init(initial: bv32)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class FsRegion {
    ghost var value: FileSystem

    ghost constructor Init(initial: FileSystem)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class PropsRegion {
    ghost var value: map<string, string>

    ghost constructor Init(initial: map<string, string>)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class CwdRegion {
    ghost var value: Path

    ghost constructor Init(initial: Path)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class EnvRegion {
    ghost var value: C.Environment

    ghost constructor Init(initial: C.Environment)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class StdinRegion {
    ghost var value: Bytes

    ghost constructor Init(initial: Bytes)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class StdoutRegion {
    ghost var value: Bytes

    ghost constructor Init(initial: Bytes)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class StderrRegion {
    ghost var value: Bytes

    ghost constructor Init(initial: Bytes)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class DirHandlesRegion {
    ghost var value: map<int, DirHandleState>

    ghost constructor Init(initial: map<int, DirHandleState>)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class NowRegion {
    ghost var value: int

    ghost constructor Init(initial: int)
      ensures value == initial
    {
      value := initial;
    }
  }

  class TrustedTimeParsesRegion {
    ghost var value: map<TimeParseRequest, ParsedTimeResult>

    ghost constructor Init(initial: map<TimeParseRequest, ParsedTimeResult>)
      ensures value == initial
    {
      value := initial;
    }
  }

  class TrustedStreamsRegion {
    ghost var value: (TrustedStreamRequest) -> TrustedStreamResult

    ghost constructor Init(
      initial: (TrustedStreamRequest) -> TrustedStreamResult
    )
      ensures value == initial
    {
      value := initial;
    }
  }

  class TrustedFilesystemRegion {
    ghost var value: C.DirectoryValidFilesystemObservations

    ghost constructor Init(
      initial: C.DirectoryValidFilesystemObservations
    )
      ensures value == initial
    {
      value := initial;
    }
  }

  class StdoutTimestampRegion {
    ghost var value: StdoutTimestampState

    ghost constructor Init(initial: StdoutTimestampState)
      ensures value == initial
    {
      value := initial;
    }
  }

  // The representation and its named constructor are not exported.
  class CredentialsRegion {
    ghost var value: ProcessCredentials

    ghost constructor Init(initial: ProcessCredentials)
      ensures value == initial
    {
      value := initial;
    }
  }

  // Exits the process with the given status code.
  method {:extern "BenchIOExtern", "Exit"} Exit(code: int)

  // Trusted libc/gnulib-compatible diagnostic results. These names forward to
  // abstract IOContract values, so clients prove message composition without
  // implementing library lookup tables or quoting loops.
  ghost function CLocaleErrnoTextResult(err: int): string { C.CLocaleErrnoTextResult(err) }

  ghost function QuoteafPathResult(path: Path): Bytes { C.QuoteafPathResult(path) }

  ghost function QuoteArgumentResult(value: Bytes): Bytes { C.QuoteArgumentResult(value) }

  // The host provides one pre-existing process handle. This pure accessor
  // promises identity only, never fresh regions or mutable world invariants.
  const {:extern "BenchIOExtern", "ProcessHandle"} ProcessHandle: IO

  function Process(): IO {
    ProcessHandle
  }

  class {:termination false} IO {
    ghost const fsRegion: FsRegion
    ghost const propsRegion: PropsRegion
    ghost const cwdRegion: CwdRegion
    ghost const envRegion: EnvRegion
    ghost const stdinRegion: StdinRegion
    ghost const stdoutRegion: StdoutRegion
    ghost const stderrRegion: StderrRegion
    ghost const dirHandlesRegion: DirHandlesRegion
    ghost const nowRegion: NowRegion
    ghost const trustedTimeParsesRegion: TrustedTimeParsesRegion
    ghost const trustedStreamsRegion: TrustedStreamsRegion
    ghost const trustedFilesystemRegion: TrustedFilesystemRegion
    ghost const stdoutTimestampRegion: StdoutTimestampRegion
    ghost const credentialsRegion: CredentialsRegion
    ghost const securityRegion: SecurityRegion
    ghost const umaskRegion: UmaskRegion

    // Dafny's revealed-class export requires a constructor for these fields.
    // No consistent verified client can call it. The native singleton allocates
    // its C# object directly; it never invokes this ghost-state initializer.
    constructor Init()
      requires false
    {
      ghost var initialFileSystem: FileSystem :| true;
      fsRegion := new FsRegion.Init(initialFileSystem);
      ghost var initialPropsRegion: map<string, string> :| true;
      propsRegion := new PropsRegion.Init(initialPropsRegion);
      ghost var initialCwdRegion: Path :| true;
      cwdRegion := new CwdRegion.Init(initialCwdRegion);
      ghost var initialEnvRegion: C.Environment :| true;
      envRegion := new EnvRegion.Init(initialEnvRegion);
      ghost var initialStdinRegion: Bytes :| true;
      stdinRegion := new StdinRegion.Init(initialStdinRegion);
      ghost var initialStdoutRegion: Bytes :| true;
      stdoutRegion := new StdoutRegion.Init(initialStdoutRegion);
      ghost var initialStderrRegion: Bytes :| true;
      stderrRegion := new StderrRegion.Init(initialStderrRegion);
      ghost var initialDirHandlesRegion: map<int, DirHandleState> :| true;
      dirHandlesRegion := new DirHandlesRegion.Init(initialDirHandlesRegion);
      ghost var initialNowRegion: int :| true;
      nowRegion := new NowRegion.Init(initialNowRegion);
      ghost var initialTrustedTimeParses: map<TimeParseRequest, ParsedTimeResult> :| true;
      trustedTimeParsesRegion := new TrustedTimeParsesRegion.Init(initialTrustedTimeParses);
      ghost var initialTrustedStreams:
        (TrustedStreamRequest) -> TrustedStreamResult :| true;
      trustedStreamsRegion := new TrustedStreamsRegion.Init(initialTrustedStreams);
      ghost var initialTrustedFilesystem:
        C.DirectoryValidFilesystemObservations :| true;
      trustedFilesystemRegion := new TrustedFilesystemRegion.Init(initialTrustedFilesystem);
      ghost var initialStdoutTimestamp: StdoutTimestampState :| true;
      stdoutTimestampRegion := new StdoutTimestampRegion.Init(initialStdoutTimestamp);
      ghost var initialCredentialsRegion: ProcessCredentials :| true;
      credentialsRegion := new CredentialsRegion.Init(initialCredentialsRegion);
      ghost var initialSecurityRegion: Sec.FilesystemSecurityContext :| true;
      securityRegion := new SecurityRegion.Init(initialSecurityRegion);
      umaskRegion := new UmaskRegion.Init(C.GetUmaskResultFields(initialPropsRegion));
    }

    // Stable aggregate for predicates that formerly read the entire IO object.
    ghost function Footprint(): set<object>
    {
      { fsRegion, propsRegion, cwdRegion, envRegion, stdinRegion, stdoutRegion, stderrRegion, dirHandlesRegion, nowRegion, trustedTimeParsesRegion, trustedStreamsRegion, trustedFilesystemRegion, stdoutTimestampRegion, credentialsRegion, securityRegion, umaskRegion }
    }

    ghost function security(): Sec.FilesystemSecurityContext
      reads securityRegion
    {
      securityRegion.value
    }

    ghost function umask(): bv32
      reads umaskRegion
    {
      umaskRegion.value
    }

    ghost function fs(): FileSystem
      reads fsRegion
    {
      fsRegion.value
    }

    ghost function props(): map<string, string>
      reads propsRegion
    {
      propsRegion.value
    }

    ghost function cwd(): Path
      reads cwdRegion
    {
      cwdRegion.value
    }

    ghost function env(): C.Environment
      reads envRegion
    {
      envRegion.value
    }

    ghost function stdin(): Bytes
      reads stdinRegion
    {
      stdinRegion.value
    }

    ghost function stdout(): Bytes
      reads stdoutRegion
    {
      stdoutRegion.value
    }

    ghost function stderr(): Bytes
      reads stderrRegion
    {
      stderrRegion.value
    }

    ghost function dirHandles(): map<int, DirHandleState>
      reads dirHandlesRegion
    {
      dirHandlesRegion.value
    }

    ghost function now(): int
      reads nowRegion
    {
      nowRegion.value
    }

    ghost function trustedTimeParses(): map<TimeParseRequest, ParsedTimeResult>
      reads trustedTimeParsesRegion
    {
      trustedTimeParsesRegion.value
    }

    ghost function trustedStreams():
      (TrustedStreamRequest) -> TrustedStreamResult
      reads trustedStreamsRegion
    {
      trustedStreamsRegion.value
    }

    ghost function trustedFilesystem():
      C.DirectoryValidFilesystemObservations
      reads trustedFilesystemRegion
    {
      trustedFilesystemRegion.value
    }

    ghost function stdoutTimestamp(): StdoutTimestampState
      reads stdoutTimestampRegion
    {
      stdoutTimestampRegion.value
    }

    ghost function credentials(): ProcessCredentials
      reads credentialsRegion
    {
      credentialsRegion.value
    }

    // Reads the contents of the file at the given path.
    method {:extern "ReadFile"} {:axiom} ReadFile(path: Path) returns (r: Result<Bytes>)
      ensures C.ReadFileSpec(old(fs()), path, r)

    // Reads a file through the trusted stream boundary and preserves any
    // successfully read prefix when the logical library operation fails.
    method {:extern "ReadFileWithOutcome"} {:axiom} ReadFileWithOutcome(path: Path)
      returns (data: Bytes, err: int)
      ensures C.ReadFileWithOutcomeSpec(old(fs()), old(trustedStreams()), path, data, err)

    // Reads the raw target of the symbolic link at the given path.
    method {:extern "ReadLink"} {:axiom} ReadLink(path: Path) returns (r: Result<Path>)
      ensures C.ReadLinkSpec(old(fs()), path, r)

    // Reads all stdin bytes and records stdin as consumed.
    method {:extern "ReadStdinAll"} {:axiom} ReadStdinAll() returns (b: Bytes)
      modifies stdinRegion
      ensures C.ReadStdinAllSpec(old(stdin()), stdin(), b)

    // Reads stdin to EOF or an error and retains the unconsumed suffix.
    method {:extern "ReadStdinWithOutcome"} {:axiom} ReadStdinWithOutcome()
      returns (data: Bytes, err: int)
      modifies stdinRegion
      ensures C.ReadStdinWithOutcomeSpec(old(stdin()), old(trustedStreams()), stdin(), data, err)

    // Appends bytes to stdout.
    method {:extern "AppendStdout"} {:axiom} AppendStdout(b: Bytes)
      modifies stdoutRegion
      ensures C.AppendStdoutSpec(old(stdout()), stdout(), b)

    // Appends bytes to stderr.
    method {:extern "AppendStderr"} {:axiom} AppendStderr(b: Bytes)
      modifies stderrRegion
      ensures C.AppendStderrSpec(old(stderr()), stderr(), b)

    // Attempts to deliver all bytes to stdout and reports the committed prefix.
    method {:extern "WriteStdoutWithOutcome"} {:axiom} WriteStdoutWithOutcome(b: Bytes)
      returns (committed: nat, err: int)
      modifies stdoutRegion
      ensures C.WriteStdoutWithOutcomeSpec(old(stdout()), old(trustedStreams()), stdout(), b, committed, err)

    // Attempts to deliver all bytes to stderr and reports the committed prefix.
    method {:extern "WriteStderrWithOutcome"} {:axiom} WriteStderrWithOutcome(b: Bytes)
      returns (committed: nat, err: int)
      modifies stderrRegion
      ensures C.WriteStderrWithOutcomeSpec(old(stderr()), old(trustedStreams()), stderr(), b, committed, err)

    // Returns libc's diagnostic text under the benchmark's C locale.
    method {:extern "GetCLocaleErrnoText"} {:axiom} GetCLocaleErrnoText(err: int)
      returns (text: string)
      ensures C.GetCLocaleErrnoTextSpec(err, text)

    // Returns gnulib quoteaf-compatible bytes for a public text path.
    method {:extern "QuoteafPath"} {:axiom} QuoteafPath(path: Path)
      returns (quoted: Bytes)
      ensures C.QuoteafPathSpec(path, quoted)

    // C-locale gnulib quote_mem style, retaining the full raw-byte argument.
    method {:extern "QuoteArgument"} {:axiom} QuoteArgument(value: Bytes)
      returns (quoted: Bytes)
      ensures C.QuoteArgumentSpec(value, quoted)

    // Returns the current working directory.
    method {:extern "GetCwd"} {:axiom} GetCwd() returns (cwd: Path)
      ensures C.GetCwdSpec(old(this.cwd()), cwd)

    // Looks up an environment variable by name.
    method {:extern "GetEnv"} {:axiom} GetEnv(key: string) returns (r: Result<string>)
      ensures C.GetEnvSpec(old(env()), key, r)

    // Returns the current environment as KEY=VALUE entries.
    method {:extern "GetEnvironment"} {:axiom} GetEnvironment() returns (entries: seq<string>)
      requires C.ValidEnvironment(env())
      ensures C.GetEnvironmentSpec(old(env()), entries)

    // Looks up the login user name.
    method {:extern "GetLoginName"} {:axiom} GetLoginName() returns (r: Result<string>)
      ensures C.GetLoginNameSpec(old(props()), r)

    // Returns the current time as an integer timestamp.
    method {:extern "Now"} {:axiom} Now() returns (t: int)
      ensures C.NowSpec(old(now()), t)

    // Parses a touch -t timestamp relative to a reference time.
    method {:extern "ParseTimestamp"} {:axiom} ParseTimestamp(timestamp: string, nowSec: int, nowNsec: int)
      returns (ok: bool, sec: int, nsec: int)
      ensures C.ParseTimestampSpec(old(trustedTimeParses()), timestamp, nowSec, nowNsec, ok, sec, nsec)

    // Parses a touch -d date string relative to a reference time.
    method {:extern "ParseDate"} {:axiom} ParseDate(date: string, refSec: int, refNsec: int)
      returns (ok: bool, sec: int, nsec: int)
      ensures C.ParseDateSpec(old(trustedTimeParses()), date, refSec, refNsec, ok, sec, nsec)

    // Checks whether a path exists, optionally following symlinks.
    method {:extern "PathExists"} {:axiom} PathExists(path: Path, followSymlink: bool) returns (found: bool, err: int)
      ensures C.PathExistsSpec(old(fs()), old(trustedFilesystem()), path, followSymlink, found, err)

    // Attempts to create an empty file at the given path.
    method {:extern "CreateFile"} {:axiom} CreateFile(path: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateFileSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, ok, err)

    // Attempts to write bytes to a regular file, creating or truncating it.
    method {:extern "WriteFile"} {:axiom} WriteFile(path: Path, data: Bytes) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.WriteFileSpec(
        old(fs()),
        old(props()),
        old(now()),
        old(credentials()),
        fs(),
        path,
        data,
        ok,
        err
      )

    // Attempts to create a symbolic link at path with the given raw target.
    method {:extern "CreateSymlink"} {:axiom} CreateSymlink(path: Path, target: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateSymlinkSpec(old(fs()), old(now()), old(credentials()), fs(), path, target, ok, err)

    // Attempts to delete a non-directory filesystem entry without following a terminal symlink.
    method {:extern "DeletePath"} {:axiom} DeletePath(path: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.DeletePathSpec(old(fs()), old(now()), fs(), path, ok, err)

    // Creates one directory. Recursive parent creation remains utility-owned.
    method {:extern "CreateDirectory"} {:axiom} CreateDirectory(path: Path, mode: bv32)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateDirectorySpec(
        old(fs()),
        old(now()),
        old(trustedFilesystem()),
        old(umask()),
        fs(),
        path,
        mode,
        ok,
        err
      )

    // Removes one empty directory without following a terminal symlink.
    method {:extern "RemoveDirectory"} {:axiom} RemoveDirectory(path: Path)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.RemoveDirectorySpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, ok, err)

    // Creates a hard-link alias for an existing filesystem object.
    method {:extern "CreateHardLink"} {:axiom} CreateHardLink(source: Path, target: Path)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateHardLinkSpec(
        old(fs()),
        old(now()),
        old(trustedFilesystem()),
        fs(),
        source,
        target,
        ok,
        err
      )

    // Performs exact libc unlink behavior without the legacy derived-success rule.
    method {:extern "UnlinkPath"} {:axiom} UnlinkPath(path: Path)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.UnlinkPathSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, ok, err)

    // Resizes one regular file, preserving the observed post-filesystem on failure.
    method {:extern "TruncateFile"} {:axiom} TruncateFile(path: Path, size: nat)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.TruncateFileSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, size, ok, err)

    // Creates one FIFO, block device, or character device node.
    method {:extern "CreateSpecialNode"} {:axiom} CreateSpecialNode(
      path: Path,
      kind: SpecialNodeKind,
      mode: bv32,
      major: nat,
      minor: nat
    ) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateSpecialNodeSpec(
        old(fs()),
        old(now()),
        old(trustedFilesystem()),
        old(umask()),
        fs(),
        path,
        kind,
        mode,
        major,
        minor,
        ok,
        err
      )

    // Requests global, file, data-only, or containing-filesystem synchronization.
    method {:extern "Sync"} {:axiom} Sync(target: SyncTarget, mode: SyncMode)
      returns (ok: bool, err: int)
      ensures C.SyncSpec(old(fs()), old(trustedFilesystem()), target, mode, ok, err)

    // Attempts to update a file timestamp to the current time.
    method {:extern "SetFileTimesNow"} {:axiom} SetFileTimesNow(path: Path, followSymlink: bool)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.SetFileTimesNowSpec(
        old(fs()),
        old(now()),
        old(trustedFilesystem()),
        fs(),
        path,
        followSymlink,
        ok,
        err
      )

    // Attempts to update only the access timestamp to the current time.
    method {:extern "SetFileAccessTimeNow"} {:axiom} SetFileAccessTimeNow(path: Path, followSymlink: bool)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.SetFileAccessTimeNowSpec(
        old(fs()),
        old(now()),
        old(trustedFilesystem()),
        fs(),
        path,
        followSymlink,
        ok,
        err
      )

    // Attempts to update only the modification timestamp to the current time.
    method {:extern "SetFileModificationTimeNow"} {:axiom} SetFileModificationTimeNow(path: Path, followSymlink: bool)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.SetFileModificationTimeNowSpec(
        old(fs()),
        old(now()),
        old(trustedFilesystem()),
        fs(),
        path,
        followSymlink,
        ok,
        err
      )

    // Reads the access and modification timestamps for a file.
    method {:extern "GetFileTimes"} {:axiom} GetFileTimes(path: Path, followSymlink: bool)
      returns (
        ok: bool,
        atimeSec: int, atimeNsec: int,
        mtimeSec: int, mtimeNsec: int,
        isDir: bool, isSymlink: bool,
        device: int, inode: int, linkCount: int,
        err: int
      )
      ensures C.GetFileTimesSpec(
        old(fs()),
        old(trustedFilesystem()),
        path,
        followSymlink,
        ok,
        atimeSec,
        atimeNsec,
        mtimeSec,
        mtimeNsec,
        isDir,
        isSymlink,
        device,
        inode,
        linkCount,
        err
      )

    // Attempts to update a file timestamp to explicit access and modification times.
    method {:extern "SetFileTimes"} {:axiom} SetFileTimes(
      path: Path,
      followSymlink: bool,
      atimeSec: int,
      atimeNsec: int,
      mtimeSec: int,
      mtimeNsec: int
    ) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.SetFileTimesSpec(
        old(fs()),
        old(now()),
        old(trustedFilesystem()),
        fs(),
        path,
        followSymlink,
        atimeSec,
        atimeNsec,
        mtimeSec,
        mtimeNsec,
        ok,
        err
      )

    // Attempts to update the stdout target timestamp to the current time.
    method {:extern "SetStdoutTimesNow"} {:axiom} SetStdoutTimesNow()
      returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutTimesNowSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), ok, err)

    // Attempts to update only the stdout target access timestamp to the current time.
    method {:extern "SetStdoutAccessTimeNow"} {:axiom} SetStdoutAccessTimeNow()
      returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutAccessTimeNowSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), ok, err)

    // Attempts to update only the stdout target modification timestamp to the current time.
    method {:extern "SetStdoutModificationTimeNow"} {:axiom} SetStdoutModificationTimeNow()
      returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutModificationTimeNowSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), ok, err)

    // Attempts the selected stdout timestamp updates, preserving fields requested as Keep.
    method {:extern "SetStdoutTimes"} {:axiom} SetStdoutTimes(
      atime: TimestampUpdate,
      mtime: TimestampUpdate
    ) returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutTimesSpec(old(now()), old(stdoutTimestamp()), stdoutTimestamp(), atime, mtime, ok, err)

    // Reads the file mode for the given path.
    method {:extern "GetFileMode"} {:axiom} GetFileMode(path: Path, followSymlink: bool) returns (ok: bool, mode: bv32, err: int)
      ensures C.GetFileModeSpec(old(fs()), path, followSymlink, ok, mode, err)

    // Reads all modeled inode metadata for the given path.
    method {:extern "GetFileStatus"} {:axiom} GetFileStatus(
      path: Path,
      followSymlink: bool
    ) returns (ok: bool, status: FileStatus, err: int)
      ensures C.GetFileStatusSpec(old(fs()), path, followSymlink, ok, status, err)

    // Attempts to set the file mode for the given path.
    method {:extern "SetFileMode"} {:axiom} SetFileMode(path: Path, followSymlink: bool, mode: bv32) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.SetFileModeSpec(old(fs()), old(now()), fs(), path, followSymlink, mode, ok, err)

    // Returns the current process umask value.
    method {:extern "GetUmask"} {:axiom} GetUmask() returns (mask: bv32)
      ensures C.GetUmaskSpec(old(props()), mask)

    // Opens a directory and returns a handle for iteration.
    method {:extern "OpenDir"} {:axiom} OpenDir(path: Path)
      returns (ok: bool, handle: int, err: int)
      modifies dirHandlesRegion
      ensures C.OpenDirSpec(old(fs()), old(dirHandles()), dirHandles(), path, ok, handle, err)

    // Resolves a path identity without opening or mutating the target.
    method {:extern "ResolvePathIdentity"} {:axiom} ResolvePathIdentity(path: Path)
      returns (ok: bool, resolvedPath: Path, err: int)
      ensures C.ResolvePathIdentitySpec(old(fs()), old(cwd()), path, ok, resolvedPath, err)

    // Reads the next entry from an open directory handle.
    method {:extern "ReadDir"} {:axiom} ReadDir(handle: int) returns (hasMore: bool, name: string, isDir: bool, isSymlink: bool, err: int)
      modifies dirHandlesRegion
      ensures C.ReadDirSpec(old(dirHandles()), dirHandles(), handle, hasMore, name, isDir, isSymlink, err)

    // Closes a directory handle and removes its tracked state.
    method {:extern "CloseDir"} {:axiom} CloseDir(handle: int)
      modifies dirHandlesRegion
      ensures C.CloseDirSpec(old(dirHandles()), dirHandles(), handle)

    // Checks whether a path refers to a directory.
    method {:extern "IsDirectory"} {:axiom} IsDirectory(path: Path, followSymlink: bool) returns (ok: bool, isDir: bool, err: int)
      ensures C.IsDirectorySpec(old(fs()), path, followSymlink, ok, isDir, err)

    // Checks whether a path refers to a directory, with modeled paths required to succeed.
    method {:extern "IsDirectoryStrict"} {:axiom} IsDirectoryStrict(path: Path, followSymlink: bool) returns (ok: bool, isDir: bool, err: int)
      ensures C.IsDirectoryStrictSpec(old(fs()), path, followSymlink, ok, isDir, err)

    // Checks whether a path refers to a symlink.
    method {:extern "IsSymlink"} {:axiom} IsSymlink(path: Path) returns (ok: bool, isSymlink: bool, err: int)
      ensures C.IsSymlinkSpec(old(fs()), path, ok, isSymlink, err)

    // Renames a filesystem entry, moving directory subtrees as a unit.
    method {:extern "RenamePath"} {:axiom} RenamePath(source: Path, target: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.RenamePathSpec(old(fs()), old(now()), fs(), source, target, ok, err)

  }
}
