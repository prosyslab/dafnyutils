include "World.dfy"
include "IOContract.dfy"
include "SecurityModel.dfy"

module BenchIO {
  import Result = Results
  import opened BenchWorld
  import C = IOContract
  import Sec = SecurityModel

  // Public trusted-library API: observers, immutable footprints and operations.
  // See ../../docs/core-api.md for the module map, contracts and frames.
  export
    provides Result
    reveals IO, FsRegion, PropsRegion, CwdRegion, EnvRegion, StdinRegion, StdoutRegion, StderrRegion, DirHandlesRegion, NowRegion, CredentialsRegion, TrustedTimeParsesRegion, TrustedStreamsRegion, TrustedFilesystemRegion, TrustedNativeFailuresRegion, StdoutTimestampRegion, StatusObservationsRegion
    provides Process, IO.Init
    provides IO.directoryStateRegion, IO.directoryModel
    provides IO.cwdContext, IO.directoryState, IO.directoryTopology, IO.currentDirectoryPath, IO.directoryPosition, IO.directoryCapabilities, IO.directoryOrdinal, IO.directoryObservations
    provides IO.GetCwdDirectoryIdentity, IO.OpenParentDirectory, IO.GetDirectoryDescriptor
    provides IO.FchdirDirectory, IO.ChdirParent, IO.FstatDirectory, IO.ReadDirectoryCapability, IO.LstatCwdEntry, IO.CloseDirectoryCapability
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
    provides IO.dirHandlesRegion, IO.dirHandles, IO.directoryOrigins
    provides IO.nowRegion, IO.now
    provides IO.trustedTimeParsesRegion, IO.trustedTimeParses
    provides IO.trustedStreamsRegion, IO.trustedStreams
    provides IO.trustedFilesystemRegion, IO.trustedFilesystem
    provides IO.trustedNativeFailuresRegion, IO.trustedNativeFailures
    provides IO.stdoutTimestampRegion, IO.stdoutTimestamp
    provides IO.statusObservationsRegion, IO.statusObservations, IO.statusCursor
    provides IO.credentialsRegion, IO.credentials
    provides IO.ReadFile, IO.ProbeReadFile, IO.ReadLink, IO.ReadStdin, IO.ReadStdinChunk
    provides IO.WriteStdout, IO.WriteStderr
    provides IO.GetCLocaleErrnoText, IO.QuoteafPath, IO.QuoteArgument
    provides IO.GetCwd, IO.GetEnv, IO.GetEnvironment, IO.GetLoginName, IO.Now
    provides IO.ParseTimestamp, IO.ParseDate
    provides IO.PathExists, IO.CreateFile, IO.WriteFile, IO.AppendFile, IO.CreateSymlink, IO.DeletePath
    provides IO.CreateDirectory, IO.RemoveDirectory, IO.CreateHardLink, IO.UnlinkPath
    provides IO.TruncateFile, IO.CreateSpecialNode, IO.Sync
    provides IO.SetFileTimesNow, IO.SetFileAccessTimeNow, IO.SetFileModificationTimeNow
    provides IO.GetFileTimes, IO.SetFileTimes
    provides IO.SetStdoutTimesNow, IO.SetStdoutAccessTimeNow, IO.SetStdoutModificationTimeNow
    provides IO.SetStdoutTimes
    provides IO.GetFileMode, IO.GetFileStatus, IO.GetOpenDirectoryStatus, IO.SetFileMode, IO.GetUmask
    provides IO.OpenDir, IO.ResolvePathIdentity
    provides IO.ReadLinkAtCwd, IO.GetFileStatusAtCwd, IO.SetFileModeAtCwd, IO.OpenDirAtCwd
    provides IO.GetFileStatusAtDir, IO.SetFileModeAtDir, IO.OpenDirAtDir
    provides IO.GetOpenDirectoryCapabilityStatus
    provides IO.ReadDir, IO.CloseDir
    provides IO.IsDirectory, IO.IsSymlink, IO.RenamePath


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
    ghost var resources: C.ValidDirectoryResources

    ghost constructor Init(initial: map<int, DirHandleState>)
      ensures resources.legacy == initial && resources.origins == map[]
      ensures resources.live.capabilities == map[]
    {
      resources := C.DirectoryResourcesFromLegacy(initial);
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
    ghost var value: C.ValidTimeParseObservations

    ghost constructor Init(initial: C.ValidTimeParseObservations)
      ensures value == initial
    {
      value := initial;
    }
  }

  class TrustedStreamsRegion {
    ghost var value: C.ValidStreamObservations

    ghost constructor Init(
      initial: C.ValidStreamObservations
    )
      ensures value == initial
    {
      value := initial;
    }
  }

  class TrustedFilesystemRegion {
    ghost var value: C.ValidFilesystemObservations

    ghost constructor Init(
      initial: C.ValidFilesystemObservations
    )
      ensures value == initial
    {
      value := initial;
    }
  }

  class TrustedNativeFailuresRegion {
    ghost var value: C.ValidNativeFailureObservations

    ghost constructor Init(initial: C.ValidNativeFailureObservations)
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

  class StatusObservationsRegion {
    ghost const observations: StatusTimeObservations
    ghost var cursor: nat

    ghost constructor Init(initial: StatusTimeObservations, first: nat)
      ensures observations == initial && cursor == first
    {
      observations := initial;
      cursor := first;
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
    ghost const directoryStateRegion: DirHandlesRegion := dirHandlesRegion
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
    ghost const trustedNativeFailuresRegion: TrustedNativeFailuresRegion
    ghost const stdoutTimestampRegion: StdoutTimestampRegion
    ghost const statusObservationsRegion: StatusObservationsRegion
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
      ghost var initialTrustedTimeParses: C.ValidTimeParseObservations :| true;
      trustedTimeParsesRegion := new TrustedTimeParsesRegion.Init(initialTrustedTimeParses);
      ghost var initialTrustedStreams:
                C.ValidStreamObservations :| true;
      trustedStreamsRegion := new TrustedStreamsRegion.Init(initialTrustedStreams);
      ghost var initialTrustedFilesystem:
                C.ValidFilesystemObservations :| true;
      trustedFilesystemRegion := new TrustedFilesystemRegion.Init(initialTrustedFilesystem);
      ghost var initialTrustedNativeFailures: C.ValidNativeFailureObservations :| true;
      trustedNativeFailuresRegion := new TrustedNativeFailuresRegion.Init(initialTrustedNativeFailures);
      ghost var initialStdoutTimestamp: StdoutTimestampState :| true;
      stdoutTimestampRegion := new StdoutTimestampRegion.Init(initialStdoutTimestamp);
      ghost var initialStatusObservations: StatusTimeObservations :| true;
      statusObservationsRegion := new StatusObservationsRegion.Init(initialStatusObservations, 0);
      ghost var initialCredentialsRegion: ProcessCredentials :| true;
      credentialsRegion := new CredentialsRegion.Init(initialCredentialsRegion);
      ghost var initialSecurityRegion: Sec.FilesystemSecurityContext :| true;
      securityRegion := new SecurityRegion.Init(initialSecurityRegion);
      umaskRegion := new UmaskRegion.Init(C.GetUmaskResultFields(initialPropsRegion));
    }

    // Stable aggregate for predicates that formerly read the entire IO object.
    ghost function Footprint(): set<object>
    {
      { directoryStateRegion, fsRegion, propsRegion, cwdRegion, envRegion, stdinRegion, stdoutRegion, stderrRegion, dirHandlesRegion, nowRegion, trustedTimeParsesRegion, trustedStreamsRegion, trustedFilesystemRegion, trustedNativeFailuresRegion, stdoutTimestampRegion, statusObservationsRegion, credentialsRegion, securityRegion, umaskRegion }
    }


    ghost function cwdContext(): (context: CwdContext)
      reads directoryStateRegion, fsRegion, cwdRegion
      ensures C.CwdContextFields(fs(),context)
      ensures context.hint == cwd()
      ensures context.topology == directoryTopology()
      ensures context.position == directoryPosition()
      ensures context.ordinal == directoryOrdinal()
      ensures context.capabilities == directoryCapabilities()
      ensures context.legacyHandles == dirHandles() && context.legacyOrigins == directoryOrigins()
    {
      C.DirectoryResourcesContextViewFields(fs(),dirHandlesRegion.resources,cwd())
    }

    ghost function directoryState(): (state: C.ValidDirectoryState)
      reads directoryStateRegion, fsRegion
      ensures state.model == directoryModel()
      ensures state.position == directoryPosition()
      ensures state.capabilities == directoryCapabilities()
      ensures state.ordinal == directoryOrdinal()
      ensures state.model.views(fs()) == directoryTopology()
      ensures state.model.observations == directoryObservations()
    {
      directoryStateRegion.resources.live
    }

    ghost function directoryModel(): DirectoryModel
      reads directoryStateRegion
    { directoryStateRegion.resources.live.model }
    ghost function directoryTopology(): LiveDirectoryTopology
      reads directoryStateRegion, fsRegion
    { directoryModel().views(fs()) }
    ghost function currentDirectoryPath(): seq<Path>
      reads directoryStateRegion, fsRegion
    {
      C.DirectoryStateAdmitsRequest(directoryStateRegion.resources.live,fs(),DirectoryGetCwd,0,0,"",0,"",dirHandles().Keys);
      directoryTopology().nodes[directoryPosition()].pathname
    }
    ghost function directoryPosition(): DirectoryPosition
      reads directoryStateRegion
    { directoryStateRegion.resources.live.position }
    ghost function directoryCapabilities(): map<int,DirectoryCapabilityState>
      reads directoryStateRegion
    { directoryStateRegion.resources.live.capabilities }
    ghost function directoryOrdinal(): nat
      reads directoryStateRegion
    { directoryStateRegion.resources.live.ordinal }
    ghost function directoryObservations(): DirectoryObservations
      reads directoryStateRegion
    { directoryModel().observations }

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
      dirHandlesRegion.resources.legacy
    }

    ghost function directoryOrigins(): (origins: map<int, FileSystem>)
      reads dirHandlesRegion
      ensures origins.Keys <= dirHandles().Keys
    {
      dirHandlesRegion.resources.origins
    }

    ghost function now(): int
      reads nowRegion
    {
      nowRegion.value
    }

    ghost function trustedTimeParses(): (parses: map<TimeParseRequest, ParsedTimeResult>)
      reads trustedTimeParsesRegion
      ensures C.TimeParseObservationsValid(parses)
    {
      trustedTimeParsesRegion.value
    }

    ghost function trustedStreams():
      (observations: (TrustedStreamRequest) -> TrustedStreamResult)
      reads trustedStreamsRegion
      ensures C.StreamObservationsValid(observations)
    {
      trustedStreamsRegion.value
    }

    ghost function trustedFilesystem():
      C.ValidFilesystemObservations
      reads trustedFilesystemRegion
    {
      trustedFilesystemRegion.value
    }

    ghost function trustedNativeFailures(): C.ValidNativeFailureObservations
      reads trustedNativeFailuresRegion
    {
      trustedNativeFailuresRegion.value
    }

    ghost function stdoutTimestamp(): StdoutTimestampState
      reads stdoutTimestampRegion
    {
      stdoutTimestampRegion.value
    }

    ghost function statusObservations(): StatusTimeObservations
    {
      statusObservationsRegion.observations
    }

    ghost function statusCursor(): nat
      reads statusObservationsRegion
    {
      statusObservationsRegion.cursor
    }

    ghost function credentials(): ProcessCredentials
      reads credentialsRegion
    {
      credentialsRegion.value
    }

    // Reads a file and returns the committed prefix, errno and terminal stage.
    method {:extern "NativeReadFile"} {:axiom} NativeReadFile(path: Path, readContents: bool)
      returns (data: Bytes, err: int, stage: BenchWorld.FileReadStage)
      ensures readContents ==> C.ReadFileSpec(
                  old(fs()), old(trustedStreams()), path, data, err, stage)
      ensures !readContents ==> C.OpenReadFileSpec(
                  old(fs()), old(trustedStreams()), path, data, err, stage)

    method ReadFile(path: Path) returns (result: IOResult<Bytes>)
      ensures C.ReadFileSpec(
                old(fs()), old(trustedStreams()), path, C.ReadResultData(result), C.ResultErrno(result), C.ReadResultStage(result))
      ensures result == C.ObservedReadFileResultFields(old(fs()), old(trustedStreams()), path)
    {
      var data, err, stage := NativeReadFile(path, true);
      assert err == 0 ==> stage == ReadSucceeded by {
        hide *;
        reveal C.ReadFileSpec(), C.TrustedReadFileContractFields();
      }
      assert C.ObservedReadFileResultFields(fs(), trustedStreams(), path) ==
             C.FileReadResultFromOutcome(data, err, stage, C.CLocaleErrnoTextResult(err)) by {
        hide *;
        reveal C.ReadFileSpec(), C.TrustedReadFileContractFields();
        reveal C.ObservedReadFileResultFields();
      }
      hide C.ReadFileSpec(), C.TrustedReadFileContractFields();
      if err == 0 {
        result := Result.Ok(data);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(ReadFailure(err, message, data, stage));
      }
    }

    // Opens read-only and closes without consuming file contents.
    method ProbeReadFile(path: Path) returns (result: IOResult<Bytes>)
      ensures C.OpenReadFileSpec(
                old(fs()), old(trustedStreams()), path, C.ReadResultData(result), C.ResultErrno(result), C.ReadResultStage(result))
      ensures result == C.ObservedOpenReadFileResultFields(old(fs()), old(trustedStreams()), path)
    {
      var data, err, stage := NativeReadFile(path, false);
      if err == 0 {
        assert stage == ReadSucceeded by {
          hide *;
          reveal C.OpenReadFileSpec(), C.TrustedOpenReadFileContractFields();
        }
        result := Result.Ok(data);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(ReadFailure(err, message, data, stage));
      }
    }

    // Reads the raw target of the symbolic link at the given path.
    method {:extern "ReadLink"} {:axiom} ReadLink(path: Path) returns (r: IOResult<Path>)
      ensures C.ReadLinkSpec(old(fs()), old(trustedNativeFailures()), path, r)

    // Uses the native operand directly, with its model path anchored to cwd.
    method {:extern "ReadLinkAtCwd"} {:axiom} ReadLinkAtCwd(path: Path) returns (result: IOResult<Path>)
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures directoryModel() == old(directoryModel())
      ensures C.CwdContextReadStepFields(old(cwdContext()),cwdContext())
      ensures C.ReadLinkAtCwdSpec(old(fs()),old(cwdContext()),old(trustedNativeFailures()),path,result)
      ensures result.Ok? <==> C.ResultErrno(result) == 0

    // Whole-input policy is verified here; the native boundary reads one chunk.
    method ReadStdin() returns (result: IOResult<Bytes>)
      modifies stdinRegion
      ensures C.ReadStdinSpec(old(stdin()), old(trustedStreams()), stdin(), C.ReadResultData(result), C.ResultErrno(result))
      ensures result == C.ObservedReadStdinResultFields(old(stdin()), old(trustedStreams()))
      ensures stdin() == C.ObservedReadStdinRemainingFields(old(stdin()), old(trustedStreams()))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      ghost var before := stdin();
      ghost var observations := trustedStreams();
      ghost var cuts: seq<nat> := [0];
      var data: Bytes := [];
      var err := 0;
      var done := false;
      while !done
        invariant C.ReadStdinPrefixFields(before, observations, cuts)
        invariant data == before[..cuts[|cuts| - 1]]
        invariant stdin() == before[cuts[|cuts| - 1]..]
        invariant !done ==> err == 0
        invariant done ==> C.ReadStdinChunkSpec(stdin(), observations, stdin(), C.StdinReadChunkSize, [], err)
        decreases |stdin()| + (if done then 0 else 1)
      {
        var read := ReadStdinChunk(C.StdinReadChunkSize);
        var chunk := C.ReadResultData(read);
        err := C.ResultErrno(read);
        if err != 0 || chunk == [] {
          assert chunk == [];
          done := true;
        } else {
          C.ReadStdinPrefixAppendFields(before, observations, cuts, chunk, stdin());
          data := data + chunk;
          cuts := cuts + [|data|];
        }
      }
      C.ReadStdinDerivedOutcomeFields(before, observations, cuts, err);
      assert C.ReadStdinSpec(before, observations, stdin(), data, err) by { hide *; }
      if err == 0 {
        result := Result.Ok(data);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(StreamFailure(err, message, data, |data|));
      }
      assert C.ReadResultData(result) == data by { hide *; reveal C.ReadResultData(); }
      assert C.ResultErrno(result) == err by { hide *; reveal C.ResultErrno(), C.IOErrorErrno(); }
      assert C.ReadStdinSpec(before, observations, stdin(),
                             C.ReadResultData(result), C.ResultErrno(result)) by { hide *; }
    }

    // The trusted operation is a bounded native read, with no block policy.
    method {:extern "NativeReadStdinChunk"} {:axiom} NativeReadStdinChunk(limit: nat)
      returns (data: Bytes, err: int)
      requires 0 < limit <= 9223372036854775806
      modifies stdinRegion
      ensures C.ReadStdinChunkSpec(old(stdin()), old(trustedStreams()), stdin(), limit, data, err)

    method ReadStdinChunk(limit: nat) returns (result: IOResult<Bytes>)
      requires 0 < limit <= 9223372036854775806
      modifies stdinRegion
      ensures C.ReadStdinChunkSpec(old(stdin()), old(trustedStreams()), stdin(), limit,
                                   C.ReadResultData(result), C.ResultErrno(result))
      ensures result == C.ObservedReadStdinChunkResultFields(old(stdin()), old(trustedStreams()), limit)
      ensures stdin() == C.ObservedReadStdinChunkRemainingFields(old(stdin()), old(trustedStreams()), limit)
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      var data, err := NativeReadStdinChunk(limit);
      if err == 0 {
        result := Result.Ok(data);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(StreamFailure(err, message, [], 0));
      }
    }

    // Writes stdout and reports the committed prefix and any terminal error.
    method {:extern "NativeWriteStdout"} {:axiom} NativeWriteStdout(b: Bytes)
      returns (committed: nat, err: int)
      modifies stdoutRegion
      ensures C.WriteStdoutSpec(old(stdout()), old(trustedStreams()), stdout(), b, committed, err)

    method WriteStdout(b: Bytes) returns (result: IOResult<WriteReceipt>)
      modifies stdoutRegion
      ensures C.WriteStdoutSpec(old(stdout()), old(trustedStreams()), stdout(), b, C.WriteResultCommitted(result), C.ResultErrno(result))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
      ensures result == C.StreamWriteResultFromOutcome(C.WriteResultCommitted(result), C.ResultErrno(result),
                                                       C.CLocaleErrnoTextResult(C.ResultErrno(result)))
    {
      var committed, err := NativeWriteStdout(b);
      if err == 0 {
        result := Result.Ok(WriteReceipt(committed));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(StreamFailure(err, message, [], committed));
      }
    }

    // Writes stderr and reports the committed prefix and any terminal error.
    method {:extern "NativeWriteStderr"} {:axiom} NativeWriteStderr(b: Bytes)
      returns (committed: nat, err: int)
      modifies stderrRegion
      ensures C.WriteStderrSpec(old(stderr()), old(trustedStreams()), stderr(), b, committed, err)

    method WriteStderr(b: Bytes) returns (result: IOResult<WriteReceipt>)
      modifies stderrRegion
      ensures C.WriteStderrSpec(old(stderr()), old(trustedStreams()), stderr(), b, C.WriteResultCommitted(result), C.ResultErrno(result))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
      ensures result == C.StreamWriteResultFromOutcome(C.WriteResultCommitted(result), C.ResultErrno(result),
                                                       C.CLocaleErrnoTextResult(C.ResultErrno(result)))
    {
      var committed, err := NativeWriteStderr(b);
      if err == 0 {
        result := Result.Ok(WriteReceipt(committed));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(StreamFailure(err, message, [], committed));
      }
    }

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

    method {:extern "GetEnv"} {:axiom} GetEnv(key: string) returns (r: IOResult<string>)
      ensures C.GetEnvSpec(old(env()), key, r)

    // Returns the current environment as KEY=VALUE entries.
    method {:extern "GetEnvironment"} {:axiom} GetEnvironment() returns (entries: seq<string>)
      requires C.ValidEnvironment(env())
      ensures C.GetEnvironmentSpec(old(env()), entries)

    // Looks up the login user name.
    method {:extern "GetLoginName"} {:axiom} GetLoginName() returns (r: IOResult<string>)
      ensures C.GetLoginNameSpec(old(props()), r)

    // Returns the current time as an integer timestamp.
    method {:extern "Now"} {:axiom} Now() returns (t: int)
      ensures C.NowSpec(old(now()), t)

    // Parses a touch -t timestamp relative to a reference time.
    method {:extern "NativeParseTimestamp"} {:axiom} NativeParseTimestamp(timestamp: string, nowSec: int, nowNsec: int)
      returns (ok: bool, sec: int, nsec: int)
      ensures C.ParseTimestampSpec(old(trustedTimeParses()), timestamp, nowSec, nowNsec, ok, sec, nsec)

    method ParseTimestamp(timestamp: string, nowSec: int, nowNsec: int) returns (result: IOResult<ParsedInstant>)
      ensures C.ParseTimestampSpec(old(trustedTimeParses()), timestamp, nowSec, nowNsec, result.Ok?, C.ParsedResultValue(result).sec, C.ParsedResultValue(result).nsec)
    {
      var ok, sec, nsec := NativeParseTimestamp(timestamp, nowSec, nowNsec);
      if ok {
        result := Result.Ok(ParsedInstant(sec, nsec));
      } else {
        result := Result.Err(TimeParseFailure("invalid time", sec, nsec));
      }
    }

    // Parses a touch -d date string relative to a reference time.
    method {:extern "NativeParseDate"} {:axiom} NativeParseDate(date: string, refSec: int, refNsec: int)
      returns (ok: bool, sec: int, nsec: int)
      ensures C.ParseDateSpec(old(trustedTimeParses()), date, refSec, refNsec, ok, sec, nsec)

    method ParseDate(date: string, refSec: int, refNsec: int) returns (result: IOResult<ParsedInstant>)
      ensures C.ParseDateSpec(old(trustedTimeParses()), date, refSec, refNsec, result.Ok?, C.ParsedResultValue(result).sec, C.ParsedResultValue(result).nsec)
    {
      var ok, sec, nsec := NativeParseDate(date, refSec, refNsec);
      if ok {
        result := Result.Ok(ParsedInstant(sec, nsec));
      } else {
        result := Result.Err(TimeParseFailure("invalid time", sec, nsec));
      }
    }

    // Checks whether a path exists, optionally following symlinks.
    method {:extern "NativePathExists"} {:axiom} NativePathExists(path: Path, followSymlink: bool) returns (found: bool, err: int)
      ensures C.PathExistsSpec(old(fs()), old(trustedFilesystem()), path, followSymlink, found, err)

    method PathExists(path: Path, followSymlink: bool) returns (result: IOResult<Unit>)
      ensures C.PathExistsSpec(old(fs()), old(trustedFilesystem()), path, followSymlink, result.Ok?, C.ResultErrno(result))
    {
      var found, err := NativePathExists(path, followSymlink);
      assert found ==> err == 0;
      hide C.PathExistsSpec();
      if found {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to create an empty file at the given path.
    method {:extern "NativeCreateFile"} {:axiom} NativeCreateFile(path: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateFileSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, ok, err)

    method CreateFile(path: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.CreateFileSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeCreateFile(path);
      assert ok ==> err == 0;
      hide C.CreateFileSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to write bytes to a regular file, creating or truncating it.
    method {:extern "NativeWriteFile"} {:axiom} NativeWriteFile(path: Path, data: Bytes, createMode: bv32)
      returns (ok: bool, err: int, committed: nat, stage: FileWriteStage)
      requires (createMode & (511 as bv32)) == createMode
      modifies fsRegion
      ensures C.WriteFileSpec(
                old(fs()),
                old(props()),
                old(now()),
                old(credentials()),
                old(trustedFilesystem()),
                fs(),
                path,
                data,
                ok,
                err,
                committed,
                stage, createMode
              )

    method WriteFile(path: Path, data: Bytes, createMode: bv32 := CREATE_FILE_MODE) returns (result: IOResult<WriteReceipt>)
      requires (createMode & (511 as bv32)) == createMode
      modifies fsRegion
      ensures C.WriteFileSpec(
                old(fs()),
                old(props()),
                old(now()),
                old(credentials()),
                old(trustedFilesystem()),
                fs(),
                path,
                data,
                result.Ok?,
                C.ResultErrno(result),
                C.WriteResultCommitted(result),
                C.WriteResultStage(result), createMode
              )
    {
      var ok, err, committed, stage := NativeWriteFile(path, data, createMode);
      assert ok ==> err == 0 && stage == WriteSucceeded;
      hide C.WriteFileSpec();
      if ok {
        result := Result.Ok(WriteReceipt(committed));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(WriteFailure(err, message, committed, stage));
      }
    }

    // Opens for append and writes without reading or truncating the referent.
    method {:extern "NativeAppendFile"} {:axiom} NativeAppendFile(path: Path, data: Bytes)
      returns (ok: bool, err: int, committed: nat, stage: FileWriteStage)
      modifies fsRegion
      ensures C.AppendFileSpec(
                old(fs()), old(props()), old(now()), old(credentials()),
                old(trustedFilesystem()), fs(), path, data, ok, err, committed, stage
              )

    method AppendFile(path: Path, data: Bytes) returns (result: IOResult<WriteReceipt>)
      modifies fsRegion
      ensures C.AppendFileSpec(
                old(fs()), old(props()), old(now()), old(credentials()),
                old(trustedFilesystem()), fs(), path, data, result.Ok?, C.ResultErrno(result), C.WriteResultCommitted(result), C.WriteResultStage(result)
              )
    {
      var ok, err, committed, stage := NativeAppendFile(path, data);
      assert ok ==> err == 0 && stage == WriteSucceeded;
      hide C.AppendFileSpec();
      if ok {
        result := Result.Ok(WriteReceipt(committed));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(WriteFailure(err, message, committed, stage));
      }
    }

    // Attempts to create a symbolic link at path with the given raw target.
    method {:extern "NativeCreateSymlink"} {:axiom} NativeCreateSymlink(path: Path, target: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.CreateSymlinkSpec(old(fs()), old(now()), old(credentials()), old(trustedNativeFailures()), fs(), path, target, ok, err)

    method CreateSymlink(path: Path, target: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.CreateSymlinkSpec(old(fs()), old(now()), old(credentials()), old(trustedNativeFailures()), fs(), path, target, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeCreateSymlink(path, target);
      assert ok ==> err == 0;
      hide C.CreateSymlinkSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to delete a non-directory filesystem entry without following a terminal symlink.
    method {:extern "NativeDeletePath"} {:axiom} NativeDeletePath(path: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.DeletePathSpec(old(fs()), old(now()), old(trustedNativeFailures()), fs(), path, ok, err)

    method DeletePath(path: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.DeletePathSpec(old(fs()), old(now()), old(trustedNativeFailures()), fs(), path, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeDeletePath(path);
      assert ok ==> err == 0;
      hide C.DeletePathSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Creates one directory. Recursive parent creation remains utility-owned.
    method {:extern "NativeCreateDirectory"} {:axiom} NativeCreateDirectory(path: Path, mode: bv32)
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

    method CreateDirectory(path: Path, mode: bv32) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.CreateDirectorySpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                old(umask()),
                fs(),
                path,
                mode,
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeCreateDirectory(path, mode);
      assert ok ==> err == 0;
      hide C.CreateDirectorySpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Removes one empty directory without following a terminal symlink.
    method {:extern "NativeRemoveDirectory"} {:axiom} NativeRemoveDirectory(path: Path)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.RemoveDirectorySpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, ok, err)

    method RemoveDirectory(path: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.RemoveDirectorySpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeRemoveDirectory(path);
      assert ok ==> err == 0;
      hide C.RemoveDirectorySpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Creates a hard-link alias for an existing filesystem object.
    method {:extern "NativeCreateHardLink"} {:axiom} NativeCreateHardLink(source: Path, target: Path, followSource: bool)
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
                err, followSource
              )

    method CreateHardLink(source: Path, target: Path, followSource: bool := false) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.CreateHardLinkSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                source,
                target,
                result.Ok?,
                C.ResultErrno(result), followSource
              )
    {
      var ok, err := NativeCreateHardLink(source, target, followSource);
      assert ok ==> err == 0;
      hide C.CreateHardLinkSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Performs exact libc unlink behavior without the legacy derived-success rule.
    method {:extern "NativeUnlinkPath"} {:axiom} NativeUnlinkPath(path: Path)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.UnlinkPathSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, ok, err)

    method UnlinkPath(path: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.UnlinkPathSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeUnlinkPath(path);
      assert ok ==> err == 0;
      hide C.UnlinkPathSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Resizes one regular file, preserving the observed post-filesystem on failure.
    method {:extern "NativeTruncateFile"} {:axiom} NativeTruncateFile(path: Path, size: nat)
      returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.TruncateFileSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, size, ok, err)

    method TruncateFile(path: Path, size: nat) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.TruncateFileSpec(old(fs()), old(now()), old(trustedFilesystem()), fs(), path, size, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeTruncateFile(path, size);
      assert ok ==> err == 0;
      hide C.TruncateFileSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Creates one FIFO, block device, or character device node.
    method {:extern "NativeCreateSpecialNode"} {:axiom} NativeCreateSpecialNode(
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

    method CreateSpecialNode(
      path: Path,
      kind: SpecialNodeKind,
      mode: bv32,
      major: nat,
      minor: nat
    ) returns (result: IOResult<Unit>)
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
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeCreateSpecialNode(path, kind, mode, major, minor);
      assert ok ==> err == 0;
      hide C.CreateSpecialNodeSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Requests global, file, data-only, or containing-filesystem synchronization.
    method {:extern "NativeSync"} {:axiom} NativeSync(target: SyncTarget, mode: SyncMode)
      returns (ok: bool, err: int)
      ensures C.SyncSpec(old(fs()), old(trustedFilesystem()), target, mode, ok, err)

    method Sync(target: SyncTarget, mode: SyncMode) returns (result: IOResult<Unit>)
      ensures C.SyncSpec(old(fs()), old(trustedFilesystem()), target, mode, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSync(target, mode);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update a file timestamp to the current time.
    method {:extern "NativeSetFileTimesNow"} {:axiom} NativeSetFileTimesNow(path: Path, followSymlink: bool)
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

    method SetFileTimesNow(path: Path, followSymlink: bool) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.SetFileTimesNowSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                path,
                followSymlink,
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeSetFileTimesNow(path, followSymlink);
      assert ok ==> err == 0;
      hide C.SetFileTimesNowSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update only the access timestamp to the current time.
    method {:extern "NativeSetFileAccessTimeNow"} {:axiom} NativeSetFileAccessTimeNow(path: Path, followSymlink: bool)
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

    method SetFileAccessTimeNow(path: Path, followSymlink: bool) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.SetFileAccessTimeNowSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                path,
                followSymlink,
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeSetFileAccessTimeNow(path, followSymlink);
      assert ok ==> err == 0;
      hide C.SetFileAccessTimeNowSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update only the modification timestamp to the current time.
    method {:extern "NativeSetFileModificationTimeNow"} {:axiom} NativeSetFileModificationTimeNow(path: Path, followSymlink: bool)
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

    method SetFileModificationTimeNow(path: Path, followSymlink: bool) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.SetFileModificationTimeNowSpec(
                old(fs()),
                old(now()),
                old(trustedFilesystem()),
                fs(),
                path,
                followSymlink,
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeSetFileModificationTimeNow(path, followSymlink);
      assert ok ==> err == 0;
      hide C.SetFileModificationTimeNowSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Reads the access and modification timestamps for a file.
    method {:extern "NativeGetFileTimes"} {:axiom} NativeGetFileTimes(path: Path, followSymlink: bool)
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

    method GetFileTimes(path: Path, followSymlink: bool) returns (result: IOResult<FileTimeStatus>)
      ensures C.GetFileTimesSpec(
                old(fs()),
                old(trustedFilesystem()),
                path,
                followSymlink,
                result.Ok?,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).atimeSec,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).atimeNsec,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).mtimeSec,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).mtimeNsec,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).isDir,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).isSymlink,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).device,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).inode,
                C.ResultValue(result, FileTimeStatus(0, 0, 0, 0, false, false, 0, 0, 0)).linkCount,
                C.ResultErrno(result)
              )
    {
      var ok, atimeSec, atimeNsec, mtimeSec, mtimeNsec, isDir, isSymlink, device, inode, linkCount, err := NativeGetFileTimes(path, followSymlink);
      assert ok ==> err == 0;
      if !ok {
        assert C.GetFileTimesSpec(fs(), trustedFilesystem(), path, followSymlink,
                                  false, 0, 0, 0, 0, false, false, 0, 0, 0, err) by {
          hide *;
          reveal C.GetFileTimesSpec();
          reveal C.TrustedFilesystemQueryContractFields();
        }
      }
      hide C.GetFileTimesSpec();
      if ok {
        result := Result.Ok(FileTimeStatus(atimeSec, atimeNsec, mtimeSec, mtimeNsec, isDir, isSymlink, device, inode, linkCount));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update a file timestamp to explicit access and modification times.
    method {:extern "NativeSetFileTimes"} {:axiom} NativeSetFileTimes(
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

    method SetFileTimes(
      path: Path,
      followSymlink: bool,
      atimeSec: int,
      atimeNsec: int,
      mtimeSec: int,
      mtimeNsec: int
    ) returns (result: IOResult<Unit>)
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
                result.Ok?,
                C.ResultErrno(result)
              )
    {
      var ok, err := NativeSetFileTimes(path, followSymlink, atimeSec, atimeNsec, mtimeSec, mtimeNsec);
      assert ok ==> err == 0;
      hide C.SetFileTimesSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update the stdout target timestamp to the current time.
    method {:extern "NativeSetStdoutTimesNow"} {:axiom} NativeSetStdoutTimesNow()
      returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutTimesNowSpec(old(now()), old(stdoutTimestamp()), old(trustedNativeFailures()), stdoutTimestamp(), ok, err)

    method SetStdoutTimesNow() returns (result: IOResult<Unit>)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutTimesNowSpec(old(now()), old(stdoutTimestamp()), old(trustedNativeFailures()), stdoutTimestamp(), result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSetStdoutTimesNow();
      assert ok ==> err == 0;
      hide C.SetStdoutTimesNowSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update only the stdout target access timestamp to the current time.
    method {:extern "NativeSetStdoutAccessTimeNow"} {:axiom} NativeSetStdoutAccessTimeNow()
      returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutAccessTimeNowSpec(old(now()), old(stdoutTimestamp()), old(trustedNativeFailures()), stdoutTimestamp(), ok, err)

    method SetStdoutAccessTimeNow() returns (result: IOResult<Unit>)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutAccessTimeNowSpec(old(now()), old(stdoutTimestamp()), old(trustedNativeFailures()), stdoutTimestamp(), result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSetStdoutAccessTimeNow();
      assert ok ==> err == 0;
      hide C.SetStdoutAccessTimeNowSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts to update only the stdout target modification timestamp to the current time.
    method {:extern "NativeSetStdoutModificationTimeNow"} {:axiom} NativeSetStdoutModificationTimeNow()
      returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutModificationTimeNowSpec(old(now()), old(stdoutTimestamp()), old(trustedNativeFailures()), stdoutTimestamp(), ok, err)

    method SetStdoutModificationTimeNow() returns (result: IOResult<Unit>)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutModificationTimeNowSpec(old(now()), old(stdoutTimestamp()), old(trustedNativeFailures()), stdoutTimestamp(), result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSetStdoutModificationTimeNow();
      assert ok ==> err == 0;
      hide C.SetStdoutModificationTimeNowSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Attempts the selected stdout timestamp updates, preserving fields requested as Keep.
    method {:extern "NativeSetStdoutTimes"} {:axiom} NativeSetStdoutTimes(
      atime: TimestampUpdate,
      mtime: TimestampUpdate
    ) returns (ok: bool, err: int)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutTimesSpec(old(now()), old(stdoutTimestamp()), old(trustedNativeFailures()), stdoutTimestamp(), atime, mtime, ok, err)

    method SetStdoutTimes(
      atime: TimestampUpdate,
      mtime: TimestampUpdate
    ) returns (result: IOResult<Unit>)
      modifies stdoutTimestampRegion
      ensures C.SetStdoutTimesSpec(old(now()), old(stdoutTimestamp()), old(trustedNativeFailures()), stdoutTimestamp(), atime, mtime, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSetStdoutTimes(atime, mtime);
      assert ok ==> err == 0;
      hide C.SetStdoutTimesSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Reads the file mode for the given path.
    method {:extern "NativeGetFileMode"} {:axiom} NativeGetFileMode(path: Path, followSymlink: bool) returns (ok: bool, mode: bv32, err: int)
      ensures C.GetFileModeSpec(old(fs()), old(trustedNativeFailures()), path, followSymlink, ok, mode, err)

    method GetFileMode(path: Path, followSymlink: bool) returns (result: IOResult<bv32>)
      ensures C.GetFileModeSpec(old(fs()), old(trustedNativeFailures()), path, followSymlink, result.Ok?, C.ResultValue(result, 0 as bv32), C.ResultErrno(result))
    {
      hide *;
      reveal C.GetFileModeSpec(), C.GetFileModeContractFields();
      reveal C.ResultValue(), C.ResultErrno(), C.IOErrorErrno();
      var ok, mode, err := NativeGetFileMode(path, followSymlink);
      if ok {
        result := Result.Ok(mode);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Reads all modeled inode metadata for the given path.
    method {:extern "NativeGetFileStatus"} {:axiom} NativeGetFileStatus(
      path: Path,
      followSymlink: bool
    ) returns (ok: bool, status: FileStatus, err: int)
      modifies statusObservationsRegion
      ensures C.GetFileStatusSpec(
                statusObservations(), old(trustedNativeFailures()), old(statusCursor()), statusCursor(),
                old(fs()), path, followSymlink, ok, status, err)

    method GetFileStatus(
      path: Path,
      followSymlink: bool
    ) returns (result: IOResult<FileStatus>)
      modifies statusObservationsRegion
      ensures C.GetFileStatusSpec(
                statusObservations(), old(trustedNativeFailures()), old(statusCursor()), statusCursor(),
                old(fs()), path, followSymlink, result.Ok?, C.ResultValue(result, DEFAULT_FILE_STATUS), C.ResultErrno(result))
    {
      var ok, status, err := NativeGetFileStatus(path, followSymlink);
      if ok {
        result := Result.Ok(status);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    method {:extern "NativeGetFileStatusAtDir"} {:axiom} NativeGetFileStatusAtDir(parent: int, path: Path, followSymlink: bool)
      returns (ok: bool, status: FileStatus, err: int)
      requires C.DirectoryParentAnchorForContextRequestFields(fs(),cwdContext(),parent,path)
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures directoryModel() == old(directoryModel())
      ensures C.CwdContextReadStepFields(old(cwdContext()),cwdContext())
      ensures C.GetFileStatusAtDirSpec(statusObservations(),old(trustedNativeFailures()),old(statusCursor()),statusCursor(),
                                       old(fs()),old(cwdContext()),parent, path,followSymlink,ok,status,err)

    method GetFileStatusAtDir(parent: int, path: Path, followSymlink: bool) returns (result: IOResult<FileStatus>)
      requires C.DirectoryParentAnchorForContextRequestFields(fs(),cwdContext(),parent,path)
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures directoryModel() == old(directoryModel())
      ensures C.CwdContextReadStepFields(old(cwdContext()),cwdContext())
      ensures C.GetFileStatusAtDirSpec(statusObservations(),old(trustedNativeFailures()),old(statusCursor()),statusCursor(),
                                       old(fs()),old(cwdContext()),parent, path,followSymlink,result.Ok?,C.ResultValue(result,DEFAULT_FILE_STATUS),C.ResultErrno(result))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      var ok,status,err := NativeGetFileStatusAtDir(parent, path,followSymlink);
      assert ok <==> err == 0;
      if ok { result := Result.Ok(status); }
      else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err,message));
      }
      assert result.Ok? <==> C.ResultErrno(result) == 0 by {
        hide *;
        reveal C.ResultErrno(), C.IOErrorErrno();
      }
    }

    method {:extern "NativeSetFileModeAtDir"} {:axiom} NativeSetFileModeAtDir(parent: int, path: Path, followSymlink: bool, mode: bv32)
      returns (ok: bool, err: int)
      requires C.DirectoryParentAnchorForContextRequestFields(fs(),cwdContext(),parent,path)
      modifies fsRegion, directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures C.SetFileModeAtDirSpec(old(fs()),old(cwdContext()),old(now()),old(trustedNativeFailures()),
                                     fs(),cwdContext(),parent, path,followSymlink,mode,ok,err)

    method SetFileModeAtDir(parent: int, path: Path, followSymlink: bool, mode: bv32) returns (result: IOResult<Unit>)
      requires C.DirectoryParentAnchorForContextRequestFields(fs(),cwdContext(),parent,path)
      modifies fsRegion, directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures C.SetFileModeAtDirSpec(old(fs()),old(cwdContext()),old(now()),old(trustedNativeFailures()),
                                     fs(),cwdContext(),parent, path,followSymlink,mode,result.Ok?,C.ResultErrno(result))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      var ok,err := NativeSetFileModeAtDir(parent, path,followSymlink,mode);
      assert ok <==> err == 0;
      hide C.SetFileModeAtDirSpec();
      if ok { result := Result.Ok(Unit); }
      else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err,message));
      }
      assert result.Ok? <==> C.ResultErrno(result) == 0 by {
        hide *;
        reveal C.ResultErrno(), C.IOErrorErrno();
      }
    }

    method {:extern "NativeOpenDirAtDir"} {:axiom} NativeOpenDirAtDir(parent: int, path: Path, includeDots: bool)
      returns (ok: bool, handle: int, err: int)
      requires C.DirectoryParentAnchorForContextRequestFields(fs(),cwdContext(),parent,path)
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures C.OpenDirAtDirSpec(old(fs()),old(cwdContext()),old(trustedNativeFailures()),
                                 cwdContext(),parent, path,includeDots,ok,handle,err)

    method OpenDirAtDir(parent: int, path: Path, includeDots: bool) returns (result: IOResult<int>)
      requires C.DirectoryParentAnchorForContextRequestFields(fs(),cwdContext(),parent,path)
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures C.OpenDirAtDirSpec(old(fs()),old(cwdContext()),old(trustedNativeFailures()),
                                 cwdContext(),parent, path,includeDots,result.Ok?,C.ResultValue(result,0),C.ResultErrno(result))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      var ok,handle,err := NativeOpenDirAtDir(parent, path,includeDots);
      assert ok <==> err == 0;
      if !ok {
        assert C.OpenDirAtDirSpec(old(fs()),old(cwdContext()),old(trustedNativeFailures()),
                                  cwdContext(),parent, path,includeDots,false,0,err) by {
          hide *;
          reveal C.OpenDirAtDirSpec(), C.OpenDirFromCwdTargetContractFields();
        }
      }
      hide C.OpenDirAtDirSpec();
      if ok { result := Result.Ok(handle); }
      else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err,message));
      }
      assert result.Ok? <==> C.ResultErrno(result) == 0 by {
        hide *;
        reveal C.ResultErrno(), C.IOErrorErrno();
      }
    }

    method {:extern "NativeGetFileStatusAtCwd"} {:axiom} NativeGetFileStatusAtCwd(path: Path, followSymlink: bool)
      returns (ok: bool, status: FileStatus, err: int)
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures directoryModel() == old(directoryModel())
      ensures C.CwdContextReadStepFields(old(cwdContext()),cwdContext())
      ensures C.GetFileStatusAtCwdSpec(statusObservations(),old(trustedNativeFailures()),old(statusCursor()),statusCursor(),
                                       old(fs()),old(cwdContext()),path,followSymlink,ok,status,err)

    method GetFileStatusAtCwd(path: Path, followSymlink: bool) returns (result: IOResult<FileStatus>)
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures directoryModel() == old(directoryModel())
      ensures C.CwdContextReadStepFields(old(cwdContext()),cwdContext())
      ensures C.GetFileStatusAtCwdSpec(statusObservations(),old(trustedNativeFailures()),old(statusCursor()),statusCursor(),
                                       old(fs()),old(cwdContext()),path,followSymlink,result.Ok?,C.ResultValue(result,DEFAULT_FILE_STATUS),C.ResultErrno(result))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      var ok,status,err := NativeGetFileStatusAtCwd(path,followSymlink);
      assert ok <==> err == 0;
      if ok { result := Result.Ok(status); }
      else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err,message));
      }
      assert result.Ok? <==> C.ResultErrno(result) == 0 by {
        hide *;
        reveal C.ResultErrno(), C.IOErrorErrno();
      }
    }

    method {:extern "NativeSetFileModeAtCwd"} {:axiom} NativeSetFileModeAtCwd(path: Path, followSymlink: bool, mode: bv32)
      returns (ok: bool, err: int)
      modifies fsRegion, directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures C.SetFileModeAtCwdSpec(old(fs()),old(cwdContext()),old(now()),old(trustedNativeFailures()),
                                     fs(),cwdContext(),path,followSymlink,mode,ok,err)

    method SetFileModeAtCwd(path: Path, followSymlink: bool, mode: bv32) returns (result: IOResult<Unit>)
      modifies fsRegion, directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures C.SetFileModeAtCwdSpec(old(fs()),old(cwdContext()),old(now()),old(trustedNativeFailures()),
                                     fs(),cwdContext(),path,followSymlink,mode,result.Ok?,C.ResultErrno(result))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      var ok,err := NativeSetFileModeAtCwd(path,followSymlink,mode);
      assert ok <==> err == 0;
      hide C.SetFileModeAtCwdSpec();
      if ok { result := Result.Ok(Unit); }
      else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err,message));
      }
      assert result.Ok? <==> C.ResultErrno(result) == 0 by {
        hide *;
        reveal C.ResultErrno(), C.IOErrorErrno();
      }
    }

    method {:extern "NativeOpenDirAtCwd"} {:axiom} NativeOpenDirAtCwd(path: Path, includeDots: bool)
      returns (ok: bool, handle: int, err: int)
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures C.OpenDirAtCwdSpec(old(fs()),old(cwdContext()),old(trustedNativeFailures()),
                                 cwdContext(),path,includeDots,ok,handle,err)

    method OpenDirAtCwd(path: Path, includeDots: bool) returns (result: IOResult<int>)
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures C.OpenDirAtCwdSpec(old(fs()),old(cwdContext()),old(trustedNativeFailures()),
                                 cwdContext(),path,includeDots,result.Ok?,C.ResultValue(result,0),C.ResultErrno(result))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      var ok,handle,err := NativeOpenDirAtCwd(path,includeDots);
      assert ok <==> err == 0;
      if !ok {
        assert C.OpenDirAtCwdSpec(old(fs()),old(cwdContext()),old(trustedNativeFailures()),
                                  cwdContext(),path,includeDots,false,0,err) by {
          hide *;
          reveal C.OpenDirAtCwdSpec(), C.OpenDirFromCwdTargetContractFields();
        }
      }
      hide C.OpenDirAtCwdSpec();
      if ok { result := Result.Ok(handle); }
      else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err,message));
      }
      assert result.Ok? <==> C.ResultErrno(result) == 0 by {
        hide *;
        reveal C.ResultErrno(), C.IOErrorErrno();
      }
    }

    method {:extern "NativeSetFileMode"} {:axiom} NativeSetFileMode(path: Path, followSymlink: bool, mode: bv32) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.SetFileModeSpec(old(fs()), old(now()), old(trustedNativeFailures()), fs(), path, followSymlink, mode, ok, err)

    method SetFileMode(path: Path, followSymlink: bool, mode: bv32) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.SetFileModeSpec(old(fs()), old(now()), old(trustedNativeFailures()), fs(), path, followSymlink, mode, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeSetFileMode(path, followSymlink, mode);
      assert ok ==> err == 0;
      hide C.SetFileModeSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Returns the current process umask value.
    method {:extern "GetUmask"} {:axiom} GetUmask() returns (mask: bv32)
      ensures C.GetUmaskSpec(old(props()), mask)

    // Opens a directory with or without dot entries and returns an iteration handle.
    method {:extern "NativeOpenDir"} {:axiom} NativeOpenDir(path: Path, includeDots: bool)
      returns (ok: bool, handle: int, err: int)
      modifies dirHandlesRegion
      ensures directoryState() == old(directoryState())
      ensures directoryOrigins() == (if ok then old(directoryOrigins())[handle := old(fs())] else old(directoryOrigins()))
      ensures C.OpenDirSpec(old(fs()), old(dirHandles()), old(trustedNativeFailures()), dirHandles(), path, includeDots, ok, handle, err)

    method OpenDir(path: Path, includeDots: bool) returns (result: IOResult<int>)
      modifies dirHandlesRegion
      ensures directoryState() == old(directoryState())
      ensures directoryOrigins() == (if result.Ok? then old(directoryOrigins())[result.v := old(fs())] else old(directoryOrigins()))
      ensures C.OpenDirSpec(old(fs()), old(dirHandles()), old(trustedNativeFailures()), dirHandles(), path, includeDots, result.Ok?, C.ResultValue(result, 0), C.ResultErrno(result))
    {
      var ok, handle, err := NativeOpenDir(path, includeDots);
      assert ok ==> err == 0;
      if !ok {
        assert C.OpenDirSpec(fs(), old(dirHandles()), trustedNativeFailures(), dirHandles(),
                             path, includeDots, false, 0, err) by {
          hide *;
          reveal C.OpenDirSpec(), C.OpenDirContractFields();
        }
      }
      hide C.OpenDirSpec();
      if ok {
        result := Result.Ok(handle);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Reads metadata from an already opened directory descriptor.
    method {:extern "NativeGetOpenDirectoryStatus"} {:axiom} NativeGetOpenDirectoryStatus(handle: int)
      returns (ok: bool, status: FileStatus, err: int)
      modifies statusObservationsRegion
      ensures C.GetOpenDirectoryStatusSpec(
                statusObservations(), old(trustedNativeFailures()), old(statusCursor()), statusCursor(),
                old(fs()), old(dirHandles()), handle, ok, status, err)

    method GetOpenDirectoryStatus(handle: int) returns (result: IOResult<FileStatus>)
      modifies statusObservationsRegion
      ensures C.GetOpenDirectoryStatusSpec(
                statusObservations(), old(trustedNativeFailures()), old(statusCursor()), statusCursor(),
                old(fs()), old(dirHandles()), handle, result.Ok?, C.ResultValue(result, DEFAULT_FILE_STATUS), C.ResultErrno(result))
    {
      var ok, status, err := NativeGetOpenDirectoryStatus(handle);
      if ok {
        result := Result.Ok(status);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    method {:extern "NativeGetOpenDirectoryCapabilityStatus"} {:axiom} NativeGetOpenDirectoryCapabilityStatus(handle: int)
      returns (ok: bool, status: FileStatus, err: int)
      requires handle in directoryCapabilities() ==>
                 C.DirectoryCapabilityAnchorCurrentFields(directoryTopology(),directoryCapabilities()[handle])
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures directoryModel() == old(directoryModel())
      ensures C.CwdContextReadStepFields(old(cwdContext()),cwdContext())
      ensures C.GetOpenDirectoryCapabilityStatusSpec(statusObservations(),old(trustedNativeFailures()),
                                                     old(statusCursor()),statusCursor(),old(fs()),old(cwdContext()),handle,ok,status,err)

    method GetOpenDirectoryCapabilityStatus(handle: int) returns (result: IOResult<FileStatus>)
      requires handle in directoryCapabilities() ==>
                 C.DirectoryCapabilityAnchorCurrentFields(directoryTopology(),directoryCapabilities()[handle])
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryObservations() == old(directoryObservations())
      ensures directoryModel() == old(directoryModel())
      ensures C.CwdContextReadStepFields(old(cwdContext()),cwdContext())
      ensures C.GetOpenDirectoryCapabilityStatusSpec(statusObservations(),old(trustedNativeFailures()),
                                                     old(statusCursor()),statusCursor(),old(fs()),old(cwdContext()),handle,result.Ok?,C.ResultValue(result,DEFAULT_FILE_STATUS),C.ResultErrno(result))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      var ok,status,err := NativeGetOpenDirectoryCapabilityStatus(handle);
      assert ok <==> err == 0;
      if ok { result := Result.Ok(status); }
      else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err,message));
      }
      assert result.Ok? <==> C.ResultErrno(result) == 0 by {
        hide *;
        reveal C.ResultErrno(), C.IOErrorErrno();
      }
    }

    // Resolves a path identity without opening or mutating the target.
    method {:extern "NativeResolvePathIdentity"} {:axiom} NativeResolvePathIdentity(path: Path)
      returns (ok: bool, resolvedPath: Path, err: int)
      ensures C.ResolvePathIdentitySpec(old(fs()), old(cwd()), old(trustedNativeFailures()), path, ok, resolvedPath, err)

    method ResolvePathIdentity(path: Path) returns (result: IOResult<Path>)
      ensures C.ResolvePathIdentitySpec(old(fs()), old(cwd()), old(trustedNativeFailures()), path, result.Ok?, C.ResultValue(result, ""), C.ResultErrno(result))
    {
      var ok, resolvedPath, err := NativeResolvePathIdentity(path);
      if ok {
        result := Result.Ok(resolvedPath);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Reads the next native entry according to the handle's dot-entry mode.
    method {:extern "NativeReadDir"} {:axiom} NativeReadDir(handle: int)
      returns (hasMore: bool, name: string, kind: DirectoryEntryKind, inode: int, err: int)
      modifies dirHandlesRegion
      ensures directoryState() == old(directoryState())
      ensures directoryOrigins() == old(directoryOrigins())
      ensures C.ReadDirSpec(
                old(fs()), old(dirHandles()), old(trustedNativeFailures()), dirHandles(), handle,
                hasMore, name, kind, err)
      ensures C.ReadDirInodeFields(old(fs()),old(dirHandles()),handle,name,hasMore,inode)

    method ReadDir(handle: int) returns (result: IOResult<DirectoryRead>)
      modifies dirHandlesRegion
      ensures directoryState() == old(directoryState())
      ensures directoryOrigins() == old(directoryOrigins())
      ensures C.ReadDirSpec(
                old(fs()), old(dirHandles()), old(trustedNativeFailures()), dirHandles(), handle,
                (result.Ok? && result.v.DirectoryItem?), (if result.Ok? && result.v.DirectoryItem? then result.v.name else ""), (if result.Ok? && result.v.DirectoryItem? then result.v.kind else UnknownDirentKind), C.ResultErrno(result))
      ensures C.ReadDirInodeFields(old(fs()),old(dirHandles()),handle,
                                   if result.Ok? && result.v.DirectoryItem? then result.v.name else "",
                                   result.Ok? && result.v.DirectoryItem?,
                                   if result.Ok? && result.v.DirectoryItem? then result.v.inode else 0)
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      var hasMore, name, kind, inode, err := NativeReadDir(handle);
      if err == 0 {
        result := Result.Ok((if hasMore then DirectoryItem(name, kind, inode) else DirectoryEnd));
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // closedir consumes an owned handle even when closing its descriptor fails.
    method {:extern "NativeCloseDir"} {:axiom} NativeCloseDir(handle: int)
      returns (ok: bool, err: int)
      modifies dirHandlesRegion
      ensures directoryState() == old(directoryState())
      ensures directoryOrigins() == old(directoryOrigins()) - {handle}
      ensures C.CloseDirSpec(old(dirHandles()), old(trustedNativeFailures()), dirHandles(), handle, ok, err)

    method CloseDir(handle: int) returns (result: IOResult<Unit>)
      modifies dirHandlesRegion
      ensures directoryState() == old(directoryState())
      ensures directoryOrigins() == old(directoryOrigins()) - {handle}
      ensures C.CloseDirSpec(old(dirHandles()), old(trustedNativeFailures()), dirHandles(), handle, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeCloseDir(handle);
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Checks whether a path refers to a directory, preserving native failures.
    method {:extern "NativeIsDirectory"} {:axiom} NativeIsDirectory(path: Path, followSymlink: bool) returns (ok: bool, isDir: bool, err: int)
      ensures C.IsDirectorySpec(old(fs()), old(trustedNativeFailures()), path, followSymlink, ok, isDir, err)

    method IsDirectory(path: Path, followSymlink: bool) returns (result: IOResult<bool>)
      ensures C.IsDirectorySpec(old(fs()), old(trustedNativeFailures()), path, followSymlink, result.Ok?, C.ResultValue(result, false), C.ResultErrno(result))
    {
      hide *;
      reveal C.IsDirectorySpec(), C.IsDirectoryStrictContractFields(), C.IsDirectoryContractFields();
      reveal C.ResultValue(), C.ResultErrno(), C.IOErrorErrno();
      var ok, isDir, err := NativeIsDirectory(path, followSymlink);
      if ok {
        result := Result.Ok(isDir);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Checks whether a path refers to a symlink.
    method {:extern "NativeIsSymlink"} {:axiom} NativeIsSymlink(path: Path) returns (ok: bool, isSymlink: bool, err: int)
      ensures C.IsSymlinkSpec(old(fs()), old(trustedNativeFailures()), path, ok, isSymlink, err)

    method IsSymlink(path: Path) returns (result: IOResult<bool>)
      ensures C.IsSymlinkSpec(old(fs()), old(trustedNativeFailures()), path, result.Ok?, C.ResultValue(result, false), C.ResultErrno(result))
    {
      hide *;
      reveal C.IsSymlinkSpec(), C.IsSymlinkContractFields();
      reveal C.ResultValue(), C.ResultErrno(), C.IOErrorErrno();
      var ok, isSymlink, err := NativeIsSymlink(path);
      if ok {
        result := Result.Ok(isSymlink);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    // Renames a filesystem entry, moving directory subtrees as a unit.
    method {:extern "NativeRenamePath"} {:axiom} NativeRenamePath(source: Path, target: Path) returns (ok: bool, err: int)
      modifies fsRegion
      ensures C.RenamePathSpec(old(fs()), old(now()), old(trustedNativeFailures()), fs(), source, target, ok, err)

    method RenamePath(source: Path, target: Path) returns (result: IOResult<Unit>)
      modifies fsRegion
      ensures C.RenamePathSpec(old(fs()), old(now()), old(trustedNativeFailures()), fs(), source, target, result.Ok?, C.ResultErrno(result))
    {
      var ok, err := NativeRenamePath(source, target);
      assert ok ==> err == 0;
      hide C.RenamePathSpec();
      if ok {
        result := Result.Ok(Unit);
      } else {
        var message := GetCLocaleErrnoText(err);
        result := Result.Err(NativeFailure(err, message));
      }
    }

    method {:extern "NativeGetCwd"} {:axiom} NativeGetCwd() returns (response: DirectoryResponse)
      requires C.DirectoryRequestFields(DirectoryRequest(DirectoryGetCwd,directoryOrdinal(),fs(),directoryTopology(),directoryPosition(),directoryCapabilities(),0,0,"",statusCursor(),cwd(),dirHandles().Keys))
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryGetCwd,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), response, directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())

    method GetCwd() returns (result: IOResult<Path>)
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryGetCwd,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), old(directoryObservations())(DirectoryRequest(DirectoryGetCwd,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)), directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())
      ensures result == C.DirectoryPathResultFields(old(directoryObservations())(DirectoryRequest(DirectoryGetCwd,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      C.DirectoryStateAdmitsRequest(directoryStateRegion.resources.live,fs(),DirectoryGetCwd,0,0,"",statusCursor(),cwd(),dirHandles().Keys);
      var response := NativeGetCwd();
      if response.err == 0 {
        result := Result.Ok(response.path);
      } else {
        var reason := GetCLocaleErrnoText(response.err);
        result := Result.Err(NativeFailure(response.err,reason));
      }
    }

    method {:extern "NativeGetCwdDirectoryIdentity"} {:axiom} NativeGetCwdDirectoryIdentity() returns (response: DirectoryResponse)
      requires C.DirectoryRequestFields(DirectoryRequest(DirectoryCurrentStatus,directoryOrdinal(),fs(),directoryTopology(),directoryPosition(),directoryCapabilities(),0,0,"",statusCursor(),cwd(),dirHandles().Keys))
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryCurrentStatus,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), response, directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())

    method GetCwdDirectoryIdentity() returns (result: IOResult<FileStatus>)
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryCurrentStatus,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), old(directoryObservations())(DirectoryRequest(DirectoryCurrentStatus,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)), directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())
      ensures result == C.DirectoryStatusResultFields(old(directoryObservations())(DirectoryRequest(DirectoryCurrentStatus,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      C.DirectoryStateAdmitsRequest(directoryStateRegion.resources.live,fs(),DirectoryCurrentStatus,0,0,"",statusCursor(),cwd(),dirHandles().Keys);
      var response := NativeGetCwdDirectoryIdentity();
      if response.err == 0 {
        result := Result.Ok(response.status);
      } else {
        var reason := GetCLocaleErrnoText(response.err);
        result := Result.Err(NativeFailure(response.err,reason));
      }
    }

    method {:extern "NativeOpenParentDirectory"} {:axiom} NativeOpenParentDirectory() returns (response: DirectoryResponse)
      requires C.DirectoryRequestFields(DirectoryRequest(DirectoryOpenParent,directoryOrdinal(),fs(),directoryTopology(),directoryPosition(),directoryCapabilities(),0,0,"",statusCursor(),cwd(),dirHandles().Keys))
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryOpenParent,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), response, directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())

    method OpenParentDirectory() returns (result: IOResult<int>)
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryOpenParent,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), old(directoryObservations())(DirectoryRequest(DirectoryOpenParent,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)), directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())
      ensures result == C.DirectoryHandleResultFields(old(directoryObservations())(DirectoryRequest(DirectoryOpenParent,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      C.DirectoryStateAdmitsRequest(directoryStateRegion.resources.live,fs(),DirectoryOpenParent,0,0,"",statusCursor(),cwd(),dirHandles().Keys);
      var response := NativeOpenParentDirectory();
      if response.err == 0 {
        result := Result.Ok(response.handle);
      } else {
        var reason := GetCLocaleErrnoText(response.err);
        result := Result.Err(NativeFailure(response.err,reason));
      }
    }

    method {:extern "NativeGetDirectoryDescriptor"} {:axiom} NativeGetDirectoryDescriptor(handle: int) returns (response: DirectoryResponse)
      requires C.DirectoryRequestFields(DirectoryRequest(DirectoryGetDescriptor,directoryOrdinal(),fs(),directoryTopology(),directoryPosition(),directoryCapabilities(),handle,0,"",statusCursor(),cwd(),dirHandles().Keys))
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryGetDescriptor,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), response, directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())

    method GetDirectoryDescriptor(handle: int) returns (result: IOResult<int>)
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryGetDescriptor,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), old(directoryObservations())(DirectoryRequest(DirectoryGetDescriptor,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)), directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())
      ensures result == C.DirectoryDescriptorResultFields(old(directoryObservations())(DirectoryRequest(DirectoryGetDescriptor,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      C.DirectoryStateAdmitsRequest(directoryStateRegion.resources.live,fs(),DirectoryGetDescriptor,handle,0,"",statusCursor(),cwd(),dirHandles().Keys);
      var response := NativeGetDirectoryDescriptor(handle);
      if response.err == 0 {
        result := Result.Ok(response.fd);
      } else {
        var reason := GetCLocaleErrnoText(response.err);
        result := Result.Err(NativeFailure(response.err,reason));
      }
    }

    method {:extern "NativeFchdirDirectory"} {:axiom} NativeFchdirDirectory(fd: int) returns (response: DirectoryResponse)
      requires C.DirectoryOperationCapabilitiesCurrentFields(directoryTopology(),
                                                             directoryCapabilities(),DirectoryFchdir,0,fd)
      requires exists handle | handle in directoryCapabilities() :: directoryCapabilities()[handle].descriptor == [fd]
      requires C.DirectoryRequestFields(DirectoryRequest(DirectoryFchdir,directoryOrdinal(),fs(),directoryTopology(),directoryPosition(),directoryCapabilities(),0,fd,"",statusCursor(),cwd(),dirHandles().Keys))
      modifies directoryStateRegion, cwdRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryFchdir,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,fd,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), response, directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())

    method FchdirDirectory(fd: int) returns (result: IOResult<Unit>)
      requires C.DirectoryOperationCapabilitiesCurrentFields(directoryTopology(),
                                                             directoryCapabilities(),DirectoryFchdir,0,fd)
      requires exists handle | handle in directoryCapabilities() :: directoryCapabilities()[handle].descriptor == [fd]
      modifies directoryStateRegion, cwdRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryFchdir,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,fd,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), old(directoryObservations())(DirectoryRequest(DirectoryFchdir,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,fd,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)), directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())
      ensures result == C.DirectoryUnitResultFields(old(directoryObservations())(DirectoryRequest(DirectoryFchdir,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,fd,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      C.DirectoryStateAdmitsRequest(directoryStateRegion.resources.live,fs(),DirectoryFchdir,0,fd,"",statusCursor(),cwd(),dirHandles().Keys);
      var response := NativeFchdirDirectory(fd);
      if response.err == 0 {
        result := Result.Ok(Unit);
      } else {
        var reason := GetCLocaleErrnoText(response.err);
        result := Result.Err(NativeFailure(response.err,reason));
      }
      assert result.Ok? <==> C.ResultErrno(result) == 0 by {
        hide *;
        reveal C.ResultErrno(), C.IOErrorErrno();
      }
    }

    method {:extern "NativeChdirParent"} {:axiom} NativeChdirParent() returns (response: DirectoryResponse)
      requires C.DirectoryRequestFields(DirectoryRequest(DirectoryChdirParent,directoryOrdinal(),fs(),directoryTopology(),directoryPosition(),directoryCapabilities(),0,0,"",statusCursor(),cwd(),dirHandles().Keys))
      modifies directoryStateRegion, cwdRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryChdirParent,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), response, directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())

    method ChdirParent() returns (result: IOResult<Unit>)
      modifies directoryStateRegion, cwdRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryChdirParent,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), old(directoryObservations())(DirectoryRequest(DirectoryChdirParent,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)), directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())
      ensures result == C.DirectoryUnitResultFields(old(directoryObservations())(DirectoryRequest(DirectoryChdirParent,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      C.DirectoryStateAdmitsRequest(directoryStateRegion.resources.live,fs(),DirectoryChdirParent,0,0,"",statusCursor(),cwd(),dirHandles().Keys);
      var response := NativeChdirParent();
      if response.err == 0 {
        result := Result.Ok(Unit);
      } else {
        var reason := GetCLocaleErrnoText(response.err);
        result := Result.Err(NativeFailure(response.err,reason));
      }
    }

    method {:extern "NativeFstatDirectory"} {:axiom} NativeFstatDirectory(fd: int) returns (response: DirectoryResponse)
      requires C.DirectoryOperationCapabilitiesCurrentFields(directoryTopology(),
                                                             directoryCapabilities(),DirectoryFstat,0,fd)
      requires exists handle | handle in directoryCapabilities() :: directoryCapabilities()[handle].descriptor == [fd]
      requires C.DirectoryRequestFields(DirectoryRequest(DirectoryFstat,directoryOrdinal(),fs(),directoryTopology(),directoryPosition(),directoryCapabilities(),0,fd,"",statusCursor(),cwd(),dirHandles().Keys))
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryFstat,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,fd,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), response, directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())

    method FstatDirectory(fd: int) returns (result: IOResult<FileStatus>)
      requires C.DirectoryOperationCapabilitiesCurrentFields(directoryTopology(),
                                                             directoryCapabilities(),DirectoryFstat,0,fd)
      requires exists handle | handle in directoryCapabilities() :: directoryCapabilities()[handle].descriptor == [fd]
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryFstat,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,fd,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), old(directoryObservations())(DirectoryRequest(DirectoryFstat,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,fd,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)), directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())
      ensures result == C.DirectoryStatusResultFields(old(directoryObservations())(DirectoryRequest(DirectoryFstat,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,fd,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      C.DirectoryStateAdmitsRequest(directoryStateRegion.resources.live,fs(),DirectoryFstat,0,fd,"",statusCursor(),cwd(),dirHandles().Keys);
      var response := NativeFstatDirectory(fd);
      if response.err == 0 {
        result := Result.Ok(response.status);
      } else {
        var reason := GetCLocaleErrnoText(response.err);
        result := Result.Err(NativeFailure(response.err,reason));
      }
      assert result.Ok? <==> C.ResultErrno(result) == 0 by {
        hide *;
        reveal C.ResultErrno(), C.IOErrorErrno();
      }
    }

    method {:extern "NativeReadDirectoryCapability"} {:axiom} NativeReadDirectoryCapability(handle: int) returns (response: DirectoryResponse)
      requires C.DirectoryOperationCapabilitiesCurrentFields(directoryTopology(),
                                                             directoryCapabilities(),DirectoryReadNext,handle,0)
      requires C.DirectoryRequestFields(DirectoryRequest(DirectoryReadNext,directoryOrdinal(),fs(),directoryTopology(),directoryPosition(),directoryCapabilities(),handle,0,"",statusCursor(),cwd(),dirHandles().Keys))
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryReadNext,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), response, directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())

    method ReadDirectoryCapability(handle: int) returns (result: IOResult<DirectoryRead>)
      requires C.DirectoryOperationCapabilitiesCurrentFields(directoryTopology(),
                                                             directoryCapabilities(),DirectoryReadNext,handle,0)
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryReadNext,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), old(directoryObservations())(DirectoryRequest(DirectoryReadNext,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)), directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())
      ensures result == C.DirectoryReadResultFields(old(directoryObservations())(DirectoryRequest(DirectoryReadNext,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
      ensures C.ContextOperationSpec(old(fs()),old(cwdContext()),old(directoryObservations()),
                                     DirectoryReadNext,handle,0,"",old(statusCursor()),statusCursor(),
                                     old(directoryObservations())(C.DirectoryRequestForContextFields(old(fs()),old(cwdContext()),
                                                                                                     DirectoryReadNext,handle,0,"",old(statusCursor()))),cwdContext())
    {
      C.DirectoryStateAdmitsRequest(directoryStateRegion.resources.live,fs(),DirectoryReadNext,handle,0,"",statusCursor(),cwd(),dirHandles().Keys);
      var response := NativeReadDirectoryCapability(handle);
      if response.err == 0 {
        result := Result.Ok(response.read);
      } else {
        var reason := GetCLocaleErrnoText(response.err);
        result := Result.Err(NativeFailure(response.err,reason));
      }
      assert result.Ok? <==> C.ResultErrno(result) == 0 by {
        hide *;
        reveal C.ResultErrno(), C.IOErrorErrno();
      }
    }

    method {:extern "NativeLstatCwdEntry"} {:axiom} NativeLstatCwdEntry(name: string) returns (response: DirectoryResponse)
      requires InodeChildNameValid(name)
      requires C.DirectoryRequestFields(DirectoryRequest(DirectoryEntryLstat,directoryOrdinal(),fs(),directoryTopology(),directoryPosition(),directoryCapabilities(),0,0,name,statusCursor(),cwd(),dirHandles().Keys))
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryEntryLstat,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,name,old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), response, directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())

    method LstatCwdEntry(name: string) returns (result: IOResult<FileStatus>)
      requires InodeChildNameValid(name)
      modifies directoryStateRegion, statusObservationsRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryEntryLstat,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,name,old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), old(directoryObservations())(DirectoryRequest(DirectoryEntryLstat,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,name,old(statusCursor()),old(cwd()),old(dirHandles()).Keys)), directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())
      ensures result == C.DirectoryStatusResultFields(old(directoryObservations())(DirectoryRequest(DirectoryEntryLstat,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),0,0,name,old(statusCursor()),old(cwd()),old(dirHandles()).Keys)))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
    {
      C.DirectoryStateAdmitsRequest(directoryStateRegion.resources.live,fs(),DirectoryEntryLstat,0,0,name,statusCursor(),cwd(),dirHandles().Keys);
      var response := NativeLstatCwdEntry(name);
      if response.err == 0 {
        result := Result.Ok(response.status);
      } else {
        var reason := GetCLocaleErrnoText(response.err);
        result := Result.Err(NativeFailure(response.err,reason));
      }
    }

    method {:extern "NativeCloseDirectoryCapability"} {:axiom} NativeCloseDirectoryCapability(handle: int) returns (response: DirectoryResponse)
      requires C.DirectoryRequestFields(DirectoryRequest(DirectoryClose,directoryOrdinal(),fs(),directoryTopology(),directoryPosition(),directoryCapabilities(),handle,0,"",statusCursor(),cwd(),dirHandles().Keys))
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryClose,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), response, directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())

    method CloseDirectoryCapability(handle: int) returns (result: IOResult<Unit>)
      modifies directoryStateRegion
      ensures dirHandles() == old(dirHandles()) && directoryOrigins() == old(directoryOrigins())
      ensures directoryModel() == old(directoryModel())
      ensures C.DirectoryOperationSpec(DirectoryRequest(DirectoryClose,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys), old(directoryObservations()), old(directoryObservations())(DirectoryRequest(DirectoryClose,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)), directoryPosition(),directoryCapabilities(),directoryOrdinal(),statusCursor(),cwd())
      ensures result == C.DirectoryUnitResultFields(old(directoryObservations())(DirectoryRequest(DirectoryClose,old(directoryOrdinal()),old(fs()),old(directoryTopology()),old(directoryPosition()),old(directoryCapabilities()),handle,0,"",old(statusCursor()),old(cwd()),old(dirHandles()).Keys)))
      ensures result.Ok? <==> C.ResultErrno(result) == 0
      ensures C.ContextOperationSpec(old(fs()),old(cwdContext()),old(directoryObservations()),
                                     DirectoryClose,handle,0,"",old(statusCursor()),statusCursor(),
                                     old(directoryObservations())(C.DirectoryRequestForContextFields(old(fs()),old(cwdContext()),
                                                                                                     DirectoryClose,handle,0,"",old(statusCursor()))),cwdContext())
    {
      C.DirectoryStateAdmitsRequest(directoryStateRegion.resources.live,fs(),DirectoryClose,handle,0,"",statusCursor(),cwd(),dirHandles().Keys);
      var response := NativeCloseDirectoryCapability(handle);
      if response.err == 0 {
        result := Result.Ok(Unit);
      } else {
        var reason := GetCLocaleErrnoText(response.err);
        result := Result.Err(NativeFailure(response.err,reason));
      }
    }

  }
}
