using System;
using System.ComponentModel;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Globalization;
using System.Numerics;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;
using Dafny;

public static partial class IOExtern {
  private enum NativeStartupFailure {
    None,
    LateCapabilityUse,
    RepeatedAdoption,
    NativeTakeStatus,
    InvalidTransfer,
    InteropUnavailable,
    EntryBeforeAdoption,
    NativeEntryStatus
  }

  private readonly struct NativeStartupResult {
    public readonly NativeStartupFailure Failure;
    public readonly int ApiStatus;
    public readonly int Role;
    public readonly uint AvailabilityErrno;
    public readonly uint FailureKind;
    public readonly uint FailureCode;

    public bool IsSuccess => Failure == NativeStartupFailure.None;

    public NativeStartupResult(
        NativeStartupFailure failure, int apiStatus = 0, int role = -1,
        uint availabilityErrno = 0, uint failureKind = 0, uint failureCode = 0) {
      Failure = failure;
      ApiStatus = apiStatus;
      Role = role;
      AvailabilityErrno = availabilityErrno;
      FailureKind = failureKind;
      FailureCode = failureCode;
    }
  }

  private enum CapabilityLifecycle {
    LegacyUnused,
    LegacyUsed,
    NativeOwned,
    NativeEntered,
    NativeFailed
  }

  private sealed class DescriptorCapability {
    public readonly int NativeFd;
    public readonly object Gate = new object();
    public bool Closed;

    public DescriptorCapability(int nativeFd) { NativeFd = nativeFd; }
  }

  // Logical capabilities never reuse an id, even when libc reuses an fd.
  // Only the three inherited streams and this API's Open create capabilities.
  private static readonly object capabilityGate = new object();
  private static CapabilityLifecycle capabilityLifecycle = CapabilityLifecycle.LegacyUnused;
  private static readonly Dictionary<BigInteger, DescriptorCapability> capabilities =
    new Dictionary<BigInteger, DescriptorCapability> {
      [BigInteger.Zero] = new DescriptorCapability(0),
      [BigInteger.One] = new DescriptorCapability(1),
      [new BigInteger(2)] = new DescriptorCapability(2)
    };
  private static BigInteger nextCapability = new BigInteger(3);

  private const string StartupLibrary = "libdafnyutils_startup.so";
  private const int StartupOk = 0;
  private const int BadFileDescriptor = 9;

  [DllImport(StartupLibrary)]
  private static extern int dfy_startup_take_standard(
    uint role, out int nativeFd, out uint availabilityErrno);

  [DllImport(StartupLibrary)]
  private static extern int dfy_startup_enter_utility(
    out uint failureKind, out uint failureCode);

  // Maintainer-owned lifecycle entry. No Dafny extern exposes this operation.
  private static NativeStartupResult AdoptNativeStartupCapabilities() {
    lock (capabilityGate) {
      if (capabilityLifecycle == CapabilityLifecycle.LegacyUsed) {
        return new NativeStartupResult(NativeStartupFailure.LateCapabilityUse);
      }
      if (capabilityLifecycle != CapabilityLifecycle.LegacyUnused) {
        return new NativeStartupResult(NativeStartupFailure.RepeatedAdoption);
      }

      var transferred = new Dictionary<BigInteger, DescriptorCapability>();
      var ownedFds = new HashSet<int>();
      for (uint role = 0; role < 3; ++role) {
        int status;
        int nativeFd;
        uint availabilityErrno;
        try {
          status = dfy_startup_take_standard(role, out nativeFd, out availabilityErrno);
        } catch (DllNotFoundException) {
          CloseTransferredDescriptors(ownedFds);
          capabilityLifecycle = CapabilityLifecycle.NativeFailed;
          return new NativeStartupResult(NativeStartupFailure.InteropUnavailable, role: (int)role);
        } catch (EntryPointNotFoundException) {
          CloseTransferredDescriptors(ownedFds);
          capabilityLifecycle = CapabilityLifecycle.NativeFailed;
          return new NativeStartupResult(NativeStartupFailure.InteropUnavailable, role: (int)role);
        } catch (BadImageFormatException) {
          CloseTransferredDescriptors(ownedFds);
          capabilityLifecycle = CapabilityLifecycle.NativeFailed;
          return new NativeStartupResult(NativeStartupFailure.InteropUnavailable, role: (int)role);
        }
        if (status != StartupOk) {
          if (nativeFd >= 0) ownedFds.Add(nativeFd);
          CloseTransferredDescriptors(ownedFds);
          capabilityLifecycle = CapabilityLifecycle.NativeFailed;
          return new NativeStartupResult(
            NativeStartupFailure.NativeTakeStatus, status, (int)role, availabilityErrno);
        }
        if (availabilityErrno == 0 && nativeFd >= 3 && ownedFds.Add(nativeFd)) {
          transferred.Add(new BigInteger(role), new DescriptorCapability(nativeFd));
          continue;
        }
        if (availabilityErrno == BadFileDescriptor && nativeFd == -1) continue;
        if (nativeFd >= 0) ownedFds.Add(nativeFd);
        CloseTransferredDescriptors(ownedFds);
        capabilityLifecycle = CapabilityLifecycle.NativeFailed;
        return new NativeStartupResult(
          NativeStartupFailure.InvalidTransfer, role: (int)role,
          availabilityErrno: availabilityErrno);
      }

      capabilities.Remove(BigInteger.Zero);
      capabilities.Remove(BigInteger.One);
      capabilities.Remove(new BigInteger(2));
      foreach (var item in transferred) capabilities.Add(item.Key, item.Value);
      capabilityLifecycle = CapabilityLifecycle.NativeOwned;
      return new NativeStartupResult(NativeStartupFailure.None);
    }
  }

  private static void CloseTransferredDescriptors(HashSet<int> ownedFds) {
    foreach (var nativeFd in ownedFds) CloseDescriptor(nativeFd, out _);
  }

  // Maintainer-owned lifecycle entry. Native status/kind/code remain separate from errno.
  private static NativeStartupResult EnterNativeUtility() {
    lock (capabilityGate) {
      if (capabilityLifecycle != CapabilityLifecycle.NativeOwned &&
          capabilityLifecycle != CapabilityLifecycle.NativeEntered) {
        return new NativeStartupResult(NativeStartupFailure.EntryBeforeAdoption);
      }
    }
    int status;
    uint failureKind;
    uint failureCode;
    try {
      status = dfy_startup_enter_utility(out failureKind, out failureCode);
    } catch (DllNotFoundException) {
      return new NativeStartupResult(NativeStartupFailure.InteropUnavailable);
    } catch (EntryPointNotFoundException) {
      return new NativeStartupResult(NativeStartupFailure.InteropUnavailable);
    } catch (BadImageFormatException) {
      return new NativeStartupResult(NativeStartupFailure.InteropUnavailable);
    }
    if (status != StartupOk) {
      return new NativeStartupResult(
        NativeStartupFailure.NativeEntryStatus, status, failureKind: failureKind,
        failureCode: failureCode);
    }
    lock (capabilityGate) {
      if (capabilityLifecycle != CapabilityLifecycle.NativeOwned) {
        return new NativeStartupResult(NativeStartupFailure.EntryBeforeAdoption);
      }
      capabilityLifecycle = CapabilityLifecycle.NativeEntered;
    }
    return new NativeStartupResult(NativeStartupFailure.None);
  }

  private static void BeginCapabilityUseUnderGate() {
    if (capabilityLifecycle == CapabilityLifecycle.LegacyUnused) {
      capabilityLifecycle = CapabilityLifecycle.LegacyUsed;
    } else if (capabilityLifecycle != CapabilityLifecycle.LegacyUsed &&
               capabilityLifecycle != CapabilityLifecycle.NativeEntered) {
      throw new InvalidOperationException(
        "descriptor primitive used outside an entered capability lifecycle");
    }
  }

  internal static void BeginCapabilityUse() {
    lock (capabilityGate) { BeginCapabilityUseUnderGate(); }
  }

  private static bool FindCapability(BigInteger handle, out DescriptorCapability capability) {
    lock (capabilityGate) {
      BeginCapabilityUseUnderGate();
      return capabilities.TryGetValue(handle, out capability);
    }
  }

  private sealed class DirEntry {
    public IntPtr DirPtr { get; }
    public string Path { get; }

    public DirEntry(IntPtr dirPtr, string path) {
      DirPtr = dirPtr;
      Path = path;
    }
  }

  private static readonly Dictionary<int, DirEntry> Dirs = new Dictionary<int, DirEntry>();
  private static readonly Stream StdInStream = Console.OpenStandardInput();
  private static readonly Stream StdOutStream = Console.OpenStandardOutput();
  private static readonly Stream StdErrStream = Console.OpenStandardError();
  private static int nextDirHandle = 1;
  private static readonly object dirLock = new object();
  private const int MaxLinkPath = 4096;

  [DllImport("libc", SetLastError = true)]
  private static extern long readlink(string path, byte[] buf, long bufsiz);

  [DllImport("libc", SetLastError = true)]
  private static extern int fcntl(int fd, int cmd);

  [DllImport("libc", SetLastError = true)]
  private static extern long lseek(int fd, long offset, int whence);

  [DllImport("libc", SetLastError = true)]
  private static extern int open(string path, int flags, uint mode);

  [DllImport("libc", SetLastError = true)]
  private static extern long write(int fd, byte[] buf, UIntPtr count);

  [DllImport("libc", SetLastError = true)]
  private static extern long read(int fd, byte[] buf, UIntPtr count);

  [DllImport("libc", SetLastError = true)]
  private static extern int close(int fd);

  [DllImport("libc", SetLastError = true)]
  private static extern long syscall(long number, int clockId, out Timespec value);

  [DllImport("libc", SetLastError = true)]
  private static extern int symlink(string target, string linkpath);

  [DllImport("libc", SetLastError = true)]
  private static extern int rename(string oldpath, string newpath);

  [DllImport("libc", SetLastError = true)]
  private static extern int unlink(string pathname);

  [DllImport("libc", SetLastError = true)]
  private static extern int mkdir(string path, uint mode);

  [DllImport("libc", SetLastError = true)]
  private static extern int rmdir(string path);

  [DllImport("libc", SetLastError = true, EntryPoint = "link")]
  private static extern int linkPath(string oldpath, string newpath);

  [DllImport("libc", SetLastError = true, EntryPoint = "truncate")]
  private static extern int truncatePath(string path, long length);

  [DllImport("libc", SetLastError = true, EntryPoint = "mkfifo")]
  private static extern int makeFifo(string path, uint mode);

  [DllImport("libc", SetLastError = true, EntryPoint = "mknod")]
  private static extern int makeNode(string path, uint mode, ulong device);

  [DllImport("libc", EntryPoint = "gnu_dev_makedev")]
  private static extern ulong makeDevice(uint major, uint minor);

  [DllImport("libc", EntryPoint = "sync")]
  private static extern void syncAll();

  [DllImport("libc", SetLastError = true)]
  private static extern int fsync(int fd);

  [DllImport("libc", SetLastError = true)]
  private static extern int fdatasync(int fd);

  [DllImport("libc", SetLastError = true)]
  private static extern int syncfs(int fd);

  [DllImport("libc", SetLastError = true, EntryPoint = "utimensat")]
  private static extern int utimensatPath(int dirfd, string path, Timespec[] times, int flags);

  [DllImport("libc", SetLastError = true, EntryPoint = "utimensat")]
  private static extern int utimensatFd(int dirfd, IntPtr path, Timespec[] times, int flags);

  [DllImport("libc", SetLastError = true)]
  private static extern int futimens(int fd, Timespec[] times);

  [DllImport("libc", SetLastError = true)]
  private static extern int stat(string path, out Stat buf);

  [DllImport("libc", SetLastError = true)]
  private static extern int fstat(int fd, out Stat buf);

  [DllImport("libc", SetLastError = true)]
  private static extern int ioctl(int fd, ulong request, ref LinuxKernelTermios attributes);

  [DllImport("libc", SetLastError = true)]
  private static extern int lstat(string path, out Stat buf);

  [DllImport("libc", SetLastError = true)]
  private static extern int chmod(string path, uint mode);

  [DllImport("libc", SetLastError = true)]
  private static extern int fchmodat(int dirfd, string path, uint mode, int flags);

  [DllImport("libc", SetLastError = true)]
  private static extern uint umask(uint mask);

  [DllImport("libc", SetLastError = true)]
  private static extern IntPtr getlogin();

  [DllImport("libc", SetLastError = true)]
  private static extern IntPtr opendir(string path);

  [DllImport("libc", SetLastError = true)]
  private static extern IntPtr readdir(IntPtr dirp);

  [DllImport("libc", SetLastError = true)]
  private static extern int closedir(IntPtr dirp);

  [DllImport("libc", SetLastError = true)]
  private static extern IntPtr realpath(string path, IntPtr resolvedPath);

  [DllImport("libc")]
  private static extern void free(IntPtr pointer);

  [DllImport("libc")]
  private static extern IntPtr strerror(int errnum);

  private const int F_GETFL = 3;
  private const int O_APPEND = 0x400;
  private const int SEEK_SET = 0;
  private const int SEEK_CUR = 1;
  private const int SEEK_END = 2;
  private const int O_WRONLY = 0x1;
  private const int O_RDONLY = 0x0;
  private const int O_CREAT = 0x40;
  private const int O_TRUNC = 0x200;
  private const int O_NONBLOCK = 0x800;
  private const int O_NOCTTY = 0x100;
  private const int AT_FDCWD = -100;
  private const int AT_SYMLINK_NOFOLLOW = 0x100;
  private const int S_IFMT = 0xF000;
  private const int S_IFIFO = 0x1000;
  private const int S_IFCHR = 0x2000;
  private const int S_IFDIR = 0x4000;
  private const int S_IFBLK = 0x6000;
  private const int S_IFLNK = 0xA000;
  private const int S_IFSOCK = 0xC000;
  private const uint PermissionModeMask = 0x0FFF;
  private const int ENOENT = 2;
  private const int EINTR = 4;
  private const int EIO = 5;
  private const int EBADF = 9;
  private const int EINVAL = 22;
  private const int ENAMETOOLONG = 36;
  private const int ENOTSUP = 95;
  private const int EOPNOTSUPP = 95;
  private const long SYS_CLOCK_GETTIME_LINUX_X86_64 = 228;
  private const ulong TCGETS_LINUX = 0x5401;
  private const int LINUX_KERNEL_TERMIOS_SIZE = 36;
  private const int LINUX_KERNEL_TERMIOS_CONTROL_COUNT = 19;

  // Permission bit masks
  private const uint S_IRWXU = 0x1C0;  // 0700
  private const uint S_IRUSR = 0x100;  // 0400
  private const uint S_IWUSR = 0x080;  // 0200
  private const uint S_IXUSR = 0x040;  // 0100
  private const uint S_IRWXG = 0x038;  // 0070
  private const uint S_IRGRP = 0x020;  // 0040
  private const uint S_IWGRP = 0x010;  // 0020
  private const uint S_IXGRP = 0x008;  // 0010
  private const uint S_IRWXO = 0x007;  // 0007
  private const uint S_IROTH = 0x004;  // 0004
  private const uint S_IWOTH = 0x002;  // 0002
  private const uint S_IXOTH = 0x001;  // 0001
  private const uint S_ISUID = 0x800;  // 04000
  private const uint S_ISGID = 0x400;  // 02000
  private const uint S_ISVTX = 0x200;  // 01000

  // Directory entry types
  private const byte DT_UNKNOWN = 0;
  private const byte DT_DIR = 4;
  private const byte DT_LNK = 10;

  private const long UTIME_NOW = (1L << 30) - 1;
  private const long UTIME_OMIT = (1L << 30) - 2;

  private const uint DefaultCreateMode = 0x1B6;

  [StructLayout(LayoutKind.Sequential)]
  private struct Timespec {
    public long tv_sec;
    public long tv_nsec;
  }

  [StructLayout(LayoutKind.Sequential)]
  private struct Stat {
    public ulong st_dev;
    public ulong st_ino;
    public ulong st_nlink;
    public uint st_mode;
    public uint st_uid;
    public uint st_gid;
    public uint __pad0;
    public ulong st_rdev;
    public long st_size;
    public long st_blksize;
    public long st_blocks;
    public Timespec st_atim;
    public Timespec st_mtim;
    public Timespec st_ctim;
    public long __glibc_reserved0;
    public long __glibc_reserved1;
    public long __glibc_reserved2;
  }

  [StructLayout(LayoutKind.Sequential)]
  private struct LinuxKernelTermios {
    public uint inputFlags;
    public uint outputFlags;
    public uint controlFlags;
    public uint localFlags;
    public byte lineDiscipline;
    [MarshalAs(UnmanagedType.ByValArray, SizeConst = LINUX_KERNEL_TERMIOS_CONTROL_COUNT)]
    public byte[] controlCharacters;
  }

  [StructLayout(LayoutKind.Sequential)]
  private struct Dirent {
    public ulong d_ino;
    public long d_off;
    public ushort d_reclen;
    public byte d_type;
    [MarshalAs(UnmanagedType.ByValArray, SizeConst = 256)]
    public byte[] d_name;
  }

  private static bool TryToLong(BigInteger value, out long result) {
    try {
      result = (long)value;
      return true;
    } catch {
      result = 0;
      return false;
    }
  }

  private static Timespec BuildExactTimespec(long sec, long nsec) {
    return new Timespec { tv_sec = sec, tv_nsec = nsec };
  }

  private static Timespec BuildCurrentTimespec() {
    return new Timespec { tv_sec = 0, tv_nsec = UTIME_NOW };
  }

  private static Timespec BuildKeepTimespec() {
    return new Timespec { tv_sec = 0, tv_nsec = UTIME_OMIT };
  }

  private static void SplitUnixTime(DateTime utcTime, out long sec, out long nsec) {
    var timestamp = new DateTimeOffset(utcTime, TimeSpan.Zero);
    sec = timestamp.ToUnixTimeSeconds();
    var ticksRemainder = utcTime.Ticks % TimeSpan.TicksPerSecond;
    nsec = ticksRemainder * 100;
  }

  private readonly struct TrustedTimeParserResult {
    public readonly bool Ok;
    public readonly BigInteger Seconds;
    public readonly BigInteger Nanoseconds;

    public TrustedTimeParserResult(bool ok, BigInteger seconds, BigInteger nanoseconds) {
      Ok = ok;
      Seconds = seconds;
      Nanoseconds = nanoseconds;
    }
  }

  private const string TrustedTimeParserProtocol = "dafnyutils-touch-time-parser-v1";
  private const string TrustedTimeParserEnvironment = "DAFNYUTILS_TOUCH_TIME_PARSER";
  private const string TrustedTimeParserExecutable = "touch_time_parser";
  private const int TrustedTimeParserTimeoutMilliseconds = 5000;
  private const int TrustedTimeParserMaxInputBytes = 128 * 1024;
  private const int TrustedTimeParserMaxOutputBytes = 512;

  private static readonly UTF8Encoding StrictUtf8 = new UTF8Encoding(false, true);

  private static string TrustedTimeParserPath() {
    var configured = Environment.GetEnvironmentVariable(TrustedTimeParserEnvironment);
    if (!string.IsNullOrEmpty(configured)) {
      return configured;
    }
    var adjacent = Path.Combine(AppContext.BaseDirectory, TrustedTimeParserExecutable);
    if (File.Exists(adjacent)) {
      return adjacent;
    }
    var evaluatorRoot = Environment.GetEnvironmentVariable("EVAL_REPO_ROOT");
    if (!string.IsNullOrEmpty(evaluatorRoot)) {
      var evaluatorOwned = Path.Combine(
        evaluatorRoot, "_build", "bench", TrustedTimeParserExecutable);
      if (File.Exists(evaluatorOwned)) {
        return evaluatorOwned;
      }
    }
    return adjacent;
  }

  private static async Task<byte[]> ReadBoundedProcessOutput(Stream stream, int limit) {
    using var output = new MemoryStream();
    var buffer = new byte[256];
    while (true) {
      var count = await stream.ReadAsync(buffer, 0, buffer.Length).ConfigureAwait(false);
      if (count == 0) {
        return output.ToArray();
      }
      if (output.Length + count > limit) {
        throw new InvalidDataException("trusted time parser output exceeded its protocol limit");
      }
      output.Write(buffer, 0, count);
    }
  }

  private static byte[] TrustedTimeParserRequest(
      string operation, BigInteger referenceSeconds, BigInteger referenceNanoseconds,
      byte[] payload) {
    var header = string.Join("\n", new[] {
      TrustedTimeParserProtocol,
      operation,
      referenceSeconds.ToString(CultureInfo.InvariantCulture),
      referenceNanoseconds.ToString(CultureInfo.InvariantCulture),
      payload.Length.ToString(CultureInfo.InvariantCulture),
      string.Empty,
    });
    var headerBytes = Encoding.ASCII.GetBytes(header);
    var request = new byte[headerBytes.Length + payload.Length];
    Buffer.BlockCopy(headerBytes, 0, request, 0, headerBytes.Length);
    Buffer.BlockCopy(payload, 0, request, headerBytes.Length, payload.Length);
    return request;
  }

  private static TrustedTimeParserResult DecodeTrustedTimeParserResponse(byte[] response) {
    string text;
    try {
      text = StrictUtf8.GetString(response);
    } catch (DecoderFallbackException error) {
      throw new InvalidOperationException(
        "trusted time parser infrastructure failure: malformed UTF-8 response", error);
    }
    if (text == TrustedTimeParserProtocol + "\ninvalid\n") {
      return new TrustedTimeParserResult(false, BigInteger.Zero, BigInteger.Zero);
    }
    var lines = text.Split('\n');
    if (lines.Length != 5 || lines[0] != TrustedTimeParserProtocol || lines[1] != "ok"
        || lines[4] != string.Empty
        || !BigInteger.TryParse(
          lines[2], NumberStyles.AllowLeadingSign, CultureInfo.InvariantCulture,
          out var seconds)
        || !BigInteger.TryParse(
          lines[3], NumberStyles.None, CultureInfo.InvariantCulture,
          out var nanoseconds)
        || nanoseconds < BigInteger.Zero || nanoseconds >= new BigInteger(1000000000)) {
      throw new InvalidOperationException(
        "trusted time parser infrastructure failure: malformed protocol response");
    }
    return new TrustedTimeParserResult(true, seconds, nanoseconds);
  }

  private static TrustedTimeParserResult RunTrustedTimeParser(
      string operation, string text, BigInteger referenceSeconds,
      BigInteger referenceNanoseconds) {
    byte[] payload;
    try {
      payload = StrictUtf8.GetBytes(text);
    } catch (EncoderFallbackException) {
      return new TrustedTimeParserResult(false, BigInteger.Zero, BigInteger.Zero);
    }
    if (payload.Length > TrustedTimeParserMaxInputBytes) {
      return new TrustedTimeParserResult(false, BigInteger.Zero, BigInteger.Zero);
    }

    var startInfo = new ProcessStartInfo {
      FileName = TrustedTimeParserPath(),
      UseShellExecute = false,
      RedirectStandardInput = true,
      RedirectStandardOutput = true,
      RedirectStandardError = true,
      CreateNoWindow = true,
    };
    using var process = new Process { StartInfo = startInfo };
    try {
      if (!process.Start()) {
        throw new InvalidOperationException(
          "trusted time parser infrastructure failure: helper did not start");
      }
    } catch (Win32Exception error) {
      throw new InvalidOperationException(
        "trusted time parser infrastructure failure: unable to start helper", error);
    }

    var stdoutTask = ReadBoundedProcessOutput(
      process.StandardOutput.BaseStream, TrustedTimeParserMaxOutputBytes);
    var stderrTask = ReadBoundedProcessOutput(
      process.StandardError.BaseStream, TrustedTimeParserMaxOutputBytes);
    var request = TrustedTimeParserRequest(
      operation, referenceSeconds, referenceNanoseconds, payload);
    try {
      process.StandardInput.BaseStream.Write(request, 0, request.Length);
      process.StandardInput.Close();
    } catch (IOException error) {
      try {
        process.Kill(entireProcessTree: true);
      } catch (InvalidOperationException) {
      }
      throw new InvalidOperationException(
        "trusted time parser infrastructure failure: request write failed", error);
    }

    if (!process.WaitForExit(TrustedTimeParserTimeoutMilliseconds)) {
      try {
        process.Kill(entireProcessTree: true);
      } catch (InvalidOperationException) {
      }
      process.WaitForExit();
      throw new InvalidOperationException(
        "trusted time parser infrastructure failure: helper timed out");
    }

    byte[] stdout;
    byte[] stderr;
    try {
      stdout = stdoutTask.GetAwaiter().GetResult();
      stderr = stderrTask.GetAwaiter().GetResult();
    } catch (InvalidDataException error) {
      throw new InvalidOperationException(
        "trusted time parser infrastructure failure: oversized helper output", error);
    }
    if (process.ExitCode != 0) {
      throw new InvalidOperationException(
        "trusted time parser infrastructure failure: helper exited with status "
        + process.ExitCode.ToString(CultureInfo.InvariantCulture));
    }
    if (stderr.Length != 0) {
      throw new InvalidOperationException(
        "trusted time parser infrastructure failure: helper wrote to stderr");
    }
    return DecodeTrustedTimeParserResponse(stdout);
  }

  private static bool TryStatPath(string path, bool followSymlink, out Stat statResult, out int err) {
    statResult = default;
    err = 0;
    int rc;
    if (followSymlink) {
      rc = stat(path, out statResult);
    } else {
      rc = lstat(path, out statResult);
    }
    if (rc == 0) {
      return true;
    }
    err = Marshal.GetLastWin32Error();
    return false;
  }

  public static void StatPath(
      string path, bool followSymlink, out BenchWorld._IFileStatus status,
      out int err, out bool invoked) {
    status = BenchWorld.FileStatus.Default();
    invoked = false;
    if (!IsAbiPath(path)) {
      err = EINVAL;
      return;
    }
    invoked = true;
    if (!TryStatPath(path, followSymlink, out var nativeStatus, out err)) return;
    status = FileStatusFromStat(nativeStatus);
  }

  private static void WriteAllToFdWithOutcome(
      int fd, byte[] bytes, out int committed, out int err) {
    err = 0;
    committed = 0;
    while (committed < bytes.Length) {
      var chunkLength = Math.Min(bytes.Length - committed, 1024 * 1024);
      var chunk = new byte[chunkLength];
      Buffer.BlockCopy(bytes, committed, chunk, 0, chunkLength);
      var written = write(fd, chunk, (UIntPtr)chunk.Length);
      if (written < 0) {
        var writeErr = Marshal.GetLastPInvokeError();
        if (writeErr == EINTR) continue;
        err = writeErr == 0 ? EIO : writeErr;
        return;
      }
      if (written == 0) {
        err = EIO;
        return;
      }
      committed += checked((int)written);
    }
  }

  private static bool TryWriteAllToFd(int fd, byte[] bytes, out int err) {
    WriteAllToFdWithOutcome(fd, bytes, out var committed, out err);
    return committed == bytes.Length && err == 0;
  }

  private static void ReadAllFromFdWithOutcome(int fd, out byte[] data, out int err) {
    err = 0;
    using var output = new MemoryStream();
    var buffer = new byte[64 * 1024];
    while (true) {
      var count = read(fd, buffer, (UIntPtr)buffer.Length);
      if (count < 0) {
        var readErr = Marshal.GetLastPInvokeError();
        if (readErr == EINTR) continue;
        err = readErr == 0 ? EIO : readErr;
        break;
      }
      if (count == 0) break;
      output.Write(buffer, 0, checked((int)count));
    }
    data = output.ToArray();
  }

  // Each descriptor operation below performs exactly one libc operation.
  // Counts and errno are preserved; callers own retries and whole-file processing.
  public static void OpenDescriptor(string path, int flags, uint mode, out int fd, out int err) {
    fd = open(path, flags, mode);
    err = fd < 0 ? Marshal.GetLastPInvokeError() : 0;
  }

  public static void CreateDirectory(string path, uint mode, out int err) {
    var result = mkdir(path, mode);
    err = result < 0 ? Marshal.GetLastPInvokeError() : 0;
  }

  public static void RemoveDirectory(string path, out int err) {
    var result = rmdir(path);
    err = result < 0 ? Marshal.GetLastPInvokeError() : 0;
  }

  public static void ReadDescriptor(int fd, int capacity, out byte[] data, out int err) {
    var buffer = new byte[capacity];
    var count = read(fd, buffer, (UIntPtr)capacity);
    err = count < 0 ? Marshal.GetLastPInvokeError() : 0;
    if (count < 0) {
      data = Array.Empty<byte>();
      return;
    }
    Array.Resize(ref buffer, checked((int)count));
    data = buffer;
  }

  public static void WriteDescriptor(int fd, byte[] data, out int count, out int err) {
    var written = write(fd, data, (UIntPtr)data.Length);
    err = written < 0 ? Marshal.GetLastPInvokeError() : 0;
    count = checked((int)written);
  }

  public static void CloseDescriptor(int fd, out int err) {
    var result = close(fd);
    err = result < 0 ? Marshal.GetLastPInvokeError() : 0;
  }

  public static void SeekDescriptor(int fd, long offset, int whence, out long position, out int err) {
    position = lseek(fd, offset, whence);
    err = position < 0 ? Marshal.GetLastPInvokeError() : 0;
  }

  public static void GetDescriptorFlags(int fd, out int flags, out int err) {
    flags = fcntl(fd, F_GETFL);
    err = flags < 0 ? Marshal.GetLastPInvokeError() : 0;
  }

  public static void OpenCapability(
      string path, int flags, uint mode, out BigInteger handle, out int err) {
    OpenCapability(path, flags, mode, out handle, out err, out _);
  }

  public static bool IsAbiPath(string path) => path.IndexOf('\0') < 0;

  public static void OpenCapability(
      string path, int flags, uint mode, out BigInteger handle, out int err, out bool invoked) {
    handle = BigInteger.Zero;
    invoked = false;
    lock (capabilityGate) { BeginCapabilityUseUnderGate(); }
    if (!IsAbiPath(path)) {
      err = EINVAL;
      return;
    }
    invoked = true;
    OpenDescriptor(path, flags, mode, out var fd, out err);
    if (err != 0) return;
    lock (capabilityGate) {
      handle = nextCapability++;
      capabilities.Add(handle, new DescriptorCapability(fd));
    }
  }

  public static void ReadCapability(
      BigInteger handle, int capacity, out byte[] data, out int err, out bool invoked) {
    data = Array.Empty<byte>();
    err = 9;
    invoked = false;
    if (!FindCapability(handle, out var capability)) return;
    lock (capability.Gate) {
      if (capability.Closed) return;
      invoked = true;
      ReadDescriptor(capability.NativeFd, capacity, out data, out err);
    }
  }

  public static void WriteCapability(
      BigInteger handle, byte[] data, out int count, out int err, out bool invoked) {
    count = -1;
    err = 9;
    invoked = false;
    if (!FindCapability(handle, out var capability)) return;
    lock (capability.Gate) {
      if (capability.Closed) return;
      invoked = true;
      WriteDescriptor(capability.NativeFd, data, out count, out err);
    }
  }

  public static void CloseCapability(BigInteger handle, out int err, out bool invoked) {
    err = 9;
    invoked = false;
    if (!FindCapability(handle, out var capability)) return;
    lock (capability.Gate) {
      if (capability.Closed) return;
      capability.Closed = true;
      lock (capabilityGate) { capabilities.Remove(handle); }
      invoked = true;
      // Linux releases an fd even if close later reports an error. Never retry.
      CloseDescriptor(capability.NativeFd, out err);
    }
  }

  public static void SeekCapability(
      BigInteger handle, long offset, int whence,
      out long position, out int err, out bool invoked) {
    position = -1;
    err = 9;
    invoked = false;
    if (!FindCapability(handle, out var capability)) return;
    lock (capability.Gate) {
      if (capability.Closed) return;
      invoked = true;
      SeekDescriptor(capability.NativeFd, offset, whence, out position, out err);
    }
  }

  public static void GetCapabilityFlags(
      BigInteger handle, out int flags, out int err, out bool invoked) {
    flags = -1;
    err = 9;
    invoked = false;
    if (!FindCapability(handle, out var capability)) return;
    lock (capability.Gate) {
      if (capability.Closed) return;
      invoked = true;
      GetDescriptorFlags(capability.NativeFd, out flags, out err);
    }
  }

  public static void FstatCapability(
      BigInteger handle, out BenchWorld._IFileStatus status, out int err, out bool invoked) {
    status = BenchWorld.FileStatus.Default();
    err = 9;
    invoked = false;
    if (!FindCapability(handle, out var capability)) return;
    lock (capability.Gate) {
      if (capability.Closed) return;
      invoked = true;
      var result = fstat(capability.NativeFd, out var nativeStatus);
      err = result < 0 ? Marshal.GetLastPInvokeError() : 0;
      if (err == 0) status = FileStatusFromStat(nativeStatus);
    }
  }

  private static bool StatIsDirectory(Stat statResult) {
    return (statResult.st_mode & S_IFMT) == S_IFDIR;
  }

  public static void ReadFileContents(ISequence<Dafny.Rune> path, out bool ok, out ISequence<Dafny.Rune> content) {
    ok = false;
    content = Sequence<Dafny.Rune>.Empty;
    try {
      var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
      var bytes = File.ReadAllBytes(pathStr);
      var text = Encoding.Latin1.GetString(bytes);
      content = Sequence<Dafny.Rune>.UnicodeFromString(text);
      ok = true;
    } catch {
      ok = false;
      content = Sequence<Dafny.Rune>.Empty;
    }
  }

  public static void ReadFileWithOutcome(
      ISequence<Dafny.Rune> path,
      out ISequence<Dafny.Rune> content,
      out BigInteger err) {
    content = Sequence<Dafny.Rune>.Empty;
    err = BigInteger.Zero;
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr) || !IsAbiPath(pathStr)) {
      err = new BigInteger(string.IsNullOrEmpty(pathStr) ? ENOENT : EINVAL);
      return;
    }
    var fd = open(pathStr, O_RDONLY | O_NOCTTY, 0);
    if (fd < 0) {
      var openErr = Marshal.GetLastPInvokeError();
      err = new BigInteger(openErr == 0 ? EIO : openErr);
      return;
    }
    ReadAllFromFdWithOutcome(fd, out var bytes, out var readErr);
    var closeResult = close(fd);
    var closeErr = closeResult < 0 ? Marshal.GetLastPInvokeError() : 0;
    content = Sequence<Dafny.Rune>.UnicodeFromString(Encoding.Latin1.GetString(bytes));
    var finalErr = readErr != 0 ? readErr : closeErr;
    err = new BigInteger(finalErr == 0 ? 0 : finalErr);
  }

  public static ISequence<Dafny.Rune> ReadStdin() {
    using var buffer = new MemoryStream();
    StdInStream.CopyTo(buffer);
    var text = Encoding.Latin1.GetString(buffer.ToArray());
    return Sequence<Dafny.Rune>.UnicodeFromString(text);
  }

  public static void ReadStdinWithOutcome(
      out ISequence<Dafny.Rune> content,
      out BigInteger err) {
    content = Sequence<Dafny.Rune>.Empty;
    err = BigInteger.Zero;
    if (!FindCapability(BigInteger.Zero, out var capability)) {
      err = new BigInteger(EBADF);
      return;
    }
    byte[] bytes;
    int readErr;
    lock (capability.Gate) {
      if (capability.Closed) {
        err = new BigInteger(EBADF);
        return;
      }
      ReadAllFromFdWithOutcome(capability.NativeFd, out bytes, out readErr);
    }
    content = Sequence<Dafny.Rune>.UnicodeFromString(Encoding.Latin1.GetString(bytes));
    err = new BigInteger(readErr);
  }

  private static void WriteStandardWithOutcome(
      BigInteger handle,
      ISequence<Dafny.Rune> content,
      out BigInteger committed,
      out BigInteger err) {
    committed = BigInteger.Zero;
    err = BigInteger.Zero;
    if (!FindCapability(handle, out var capability)) {
      err = new BigInteger(EBADF);
      return;
    }
    var text = content?.ToVerbatimString(false) ?? string.Empty;
    var bytes = Encoding.Latin1.GetBytes(text);
    int written;
    int writeErr;
    lock (capability.Gate) {
      if (capability.Closed) {
        err = new BigInteger(EBADF);
        return;
      }
      WriteAllToFdWithOutcome(capability.NativeFd, bytes, out written, out writeErr);
    }
    committed = new BigInteger(written);
    err = new BigInteger(writeErr);
  }

  public static void WriteStdoutWithOutcome(
      ISequence<Dafny.Rune> content,
      out BigInteger committed,
      out BigInteger err) {
    WriteStandardWithOutcome(BigInteger.One, content, out committed, out err);
  }

  public static void WriteStderrWithOutcome(
      ISequence<Dafny.Rune> content,
      out BigInteger committed,
      out BigInteger err) {
    WriteStandardWithOutcome(new BigInteger(2), content, out committed, out err);
  }

  public static void WriteStdout(ISequence<Dafny.Rune> content) {
    var text = content?.ToVerbatimString(false) ?? string.Empty;
    var bytes = Encoding.Latin1.GetBytes(text);
    StdOutStream.Write(bytes, 0, bytes.Length);
    StdOutStream.Flush();
  }

  public static void WriteStderr(ISequence<Dafny.Rune> content) {
    var text = content?.ToVerbatimString(false) ?? string.Empty;
    var bytes = Encoding.Latin1.GetBytes(text);
    StdErrStream.Write(bytes, 0, bytes.Length);
  }

  public static void GetEnv(ISequence<Dafny.Rune> name, out bool ok, out ISequence<Dafny.Rune> value) {
    ok = false;
    value = Sequence<Dafny.Rune>.Empty;
    var nameStr = name?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(nameStr)) {
      return;
    }
    var env = Environment.GetEnvironmentVariable(nameStr);
    if (env == null) {
      return;
    }
    ok = true;
    value = Sequence<Dafny.Rune>.UnicodeFromString(env);
  }

  public static ISequence<ISequence<Dafny.Rune>> GetEnvironment() {
    var entries = new List<ISequence<Dafny.Rune>>();
    foreach (System.Collections.DictionaryEntry entry in Environment.GetEnvironmentVariables()) {
      var key = entry.Key?.ToString() ?? string.Empty;
      if (string.IsNullOrEmpty(key)) {
        continue;
      }
      var value = entry.Value?.ToString() ?? string.Empty;
      entries.Add(Sequence<Dafny.Rune>.UnicodeFromString(key + "=" + value));
    }
    return Sequence<ISequence<Dafny.Rune>>.FromArray(entries.ToArray());
  }

  public static void GetLoginName(out bool ok, out ISequence<Dafny.Rune> value) {
    ok = false;
    value = Sequence<Dafny.Rune>.Empty;
    try {
      var ptr = getlogin();
      if (ptr == IntPtr.Zero) {
        return;
      }
      var login = Marshal.PtrToStringAnsi(ptr);
      if (string.IsNullOrEmpty(login)) {
        return;
      }
      ok = true;
      value = Sequence<Dafny.Rune>.UnicodeFromString(login);
    } catch {
    }
  }

  public static void GetCurrentDirectory(out bool ok, out ISequence<Dafny.Rune> value) {
    ok = false;
    value = Sequence<Dafny.Rune>.Empty;
    try {
      var cwd = Directory.GetCurrentDirectory();
      if (string.IsNullOrEmpty(cwd)) {
        return;
      }
      ok = true;
      value = Sequence<Dafny.Rune>.UnicodeFromString(cwd);
    } catch {
    }
  }

  [DllImport("libc", SetLastError = true)]
  private static extern ulong getauxval(ulong tag);

  public static void GetAuxiliaryValue(BigInteger tag, out BigInteger value, out int err) {
    value = BigInteger.Zero;
    if (tag < BigInteger.Zero || tag > ulong.MaxValue) {
      err = 75; // EOVERFLOW: the request does not fit unsigned long on LP64.
      return;
    }
    if (!RuntimeInformation.IsOSPlatform(OSPlatform.Linux)
        || RuntimeInformation.ProcessArchitecture != Architecture.X64) {
      err = ENOTSUP;
      return;
    }
    // .NET SetLastError clears errno before this call, preserving successful 0.
    var observed = getauxval((ulong)tag);
    err = Marshal.GetLastPInvokeError();
    if (err == 0) {
      value = new BigInteger(observed);
    }
  }

  public static void ClockRealtime(out BigInteger sec, out BigInteger nsec, out int err) {
    sec = BigInteger.Zero;
    nsec = BigInteger.Zero;
    if (!RuntimeInformation.IsOSPlatform(OSPlatform.Linux)
        || RuntimeInformation.ProcessArchitecture != Architecture.X64) {
      err = ENOTSUP;
      return;
    }
    var result = syscall(SYS_CLOCK_GETTIME_LINUX_X86_64, 0, out var value); // CLOCK_REALTIME
    err = result == 0 ? 0 : Marshal.GetLastPInvokeError();
    sec = result == 0 ? new BigInteger(value.tv_sec) : BigInteger.Zero;
    nsec = result == 0 ? new BigInteger(value.tv_nsec) : BigInteger.Zero;
  }

  public static void GetCurrentTime(out BigInteger sec, out BigInteger nsec) {
    SplitUnixTime(DateTime.UtcNow, out var seconds, out var nanoseconds);
    sec = new BigInteger(seconds);
    nsec = new BigInteger(nanoseconds);
  }

  public static void ParseDate(ISequence<Dafny.Rune> date, BigInteger refSec, BigInteger refNsec, out bool ok, out BigInteger sec, out BigInteger nsec) {
    var text = date?.ToVerbatimString(false) ?? string.Empty;
    var result = RunTrustedTimeParser("date", text, refSec, refNsec);
    ok = result.Ok;
    sec = result.Seconds;
    nsec = result.Nanoseconds;
  }

  public static void ParseTimestamp(ISequence<Dafny.Rune> timestamp, BigInteger nowSec, BigInteger nowNsec, out bool ok, out BigInteger sec, out BigInteger nsec) {
    var text = timestamp?.ToVerbatimString(false) ?? string.Empty;
    var result = RunTrustedTimeParser("timestamp", text, nowSec, nowNsec);
    ok = result.Ok;
    sec = result.Seconds;
    nsec = result.Nanoseconds;
  }

  public static ISequence<Dafny.Rune> ErrnoMessage(BigInteger err) {
    int errValue;
    try {
      errValue = (int)err;
    } catch {
      errValue = 0;
    }
    var pointer = strerror(errValue);
    if (pointer == IntPtr.Zero) {
      return Sequence<Dafny.Rune>.Empty;
    }
    var message = Marshal.PtrToStringAnsi(pointer) ?? string.Empty;
    return Sequence<Dafny.Rune>.UnicodeFromString(message);
  }

  public static ISequence<Dafny.Rune> GetCLocaleErrnoText(BigInteger err) {
    return ErrnoMessage(err);
  }

  private static bool IsQuoteafDoubleQuoteCompatible(byte value) {
    return value == (byte)' '
      || value == (byte)'\''
      || value == (byte)'%'
      || value == (byte)'+'
      || value == (byte)','
      || value == (byte)'-'
      || value == (byte)'.'
      || value == (byte)'/'
      || (value >= (byte)'0' && value <= (byte)':')
      || (value >= (byte)'A' && value <= (byte)'Z')
      || value == (byte)']'
      || value == (byte)'_'
      || (value >= (byte)'a' && value <= (byte)'z');
  }

  private static char QuoteafEscape(byte value) {
    switch (value) {
      case 0x00: return '0';
      case 0x07: return 'a';
      case 0x08: return 'b';
      case 0x0c: return 'f';
      case 0x0a: return 'n';
      case 0x0d: return 'r';
      case 0x09: return 't';
      case 0x0b: return 'v';
      default: return '\0';
    }
  }

  // This is the C-locale shell-escape-always subset used by gnulib quoteaf.
  // Public paths are Unicode scalar strings, so formatting their UTF-8 bytes
  // covers the benchmark domain without exposing gnulib's byte loop to Dafny.
  public static ISequence<Dafny.Rune> QuoteafPath(ISequence<Dafny.Rune> path) {
    var pathText = path?.ToVerbatimString(false) ?? string.Empty;
    var pathBytes = Encoding.UTF8.GetBytes(pathText);
    var encounteredSingleQuote = false;
    var allDoubleQuoteCompatible = true;
    foreach (var value in pathBytes) {
      encounteredSingleQuote |= value == (byte)'\'';
      allDoubleQuoteCompatible &= IsQuoteafDoubleQuoteCompatible(value);
    }

    if (encounteredSingleQuote && allDoubleQuoteCompatible) {
      return Sequence<Dafny.Rune>.UnicodeFromString(
        "\"" + Encoding.ASCII.GetString(pathBytes) + "\"");
    }

    var quoted = new StringBuilder("'");
    var inShellEscape = false;
    foreach (var value in pathBytes) {
      var escape = QuoteafEscape(value);
      if (escape != '\0') {
        if (!inShellEscape) {
          quoted.Append("'$'");
          inShellEscape = true;
        }
        quoted.Append('\\');
        quoted.Append(escape);
      } else if (value < 0x20 || value >= 0x7f) {
        if (!inShellEscape) {
          quoted.Append("'$'");
          inShellEscape = true;
        }
        quoted.Append('\\');
        quoted.Append((char)('0' + (value >> 6)));
        quoted.Append((char)('0' + ((value >> 3) & 7)));
        quoted.Append((char)('0' + (value & 7)));
      } else if (value == (byte)'\'') {
        quoted.Append("'\\''");
        inShellEscape = false;
      } else {
        if (inShellEscape) {
          quoted.Append("''");
          inShellEscape = false;
        }
        quoted.Append((char)value);
      }
    }
    quoted.Append('\'');
    return Sequence<Dafny.Rune>.UnicodeFromString(quoted.ToString());
  }

  // C-locale gnulib quote_mem: single quotes, C escapes and octal byte escapes.
  // Bytes are already encoded; unlike QuoteafPath, no UTF-8 conversion is needed.
  public static ISequence<Dafny.Rune> QuoteArgument(ISequence<Dafny.Rune> value) {
    var bytes = Encoding.Latin1.GetBytes(value.ToVerbatimString(false));
    var quoted = new StringBuilder("'");
    for (var i = 0; i < bytes.Length; i++) {
      var current = bytes[i];
      var escape = QuoteafEscape(current);
      if (escape != '\0') {
        quoted.Append('\\');
        if (current == 0 && i + 1 < bytes.Length
            && bytes[i + 1] >= (byte)'0' && bytes[i + 1] <= (byte)'9') {
          quoted.Append("00");
        }
        quoted.Append(escape);
      } else if (current < 0x20 || current >= 0x7f) {
        quoted.Append('\\');
        quoted.Append((char)('0' + (current >> 6)));
        quoted.Append((char)('0' + ((current >> 3) & 7)));
        quoted.Append((char)('0' + (current & 7)));
      } else {
        if (current == (byte)'\'' || current == (byte)'\\') {
          quoted.Append('\\');
        }
        quoted.Append((char)current);
      }
    }
    quoted.Append('\'');
    return Sequence<Dafny.Rune>.UnicodeFromString(quoted.ToString());
  }

  public static void ReadLinkTarget(ISequence<Dafny.Rune> path, out bool ok, out ISequence<Dafny.Rune> target, out BigInteger err) {
    ok = false;
    target = Sequence<Dafny.Rune>.Empty;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    var buffer = new byte[MaxLinkPath];
    long length;
    try {
      length = readlink(pathStr, buffer, buffer.Length);
    } catch {
      length = -1;
    }
    if (length < 0) {
      err = new BigInteger(Marshal.GetLastWin32Error());
      return;
    }
    ok = true;
    target = Sequence<Dafny.Rune>.UnicodeFromString(Encoding.UTF8.GetString(buffer, 0, (int)length));
  }

  public static void PathExists(ISequence<Dafny.Rune> path, bool followSymlink, out bool exists, out BigInteger err) {
    exists = false;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    if (TryStatPath(pathStr, followSymlink, out _, out var statErr)) {
      exists = true;
      return;
    }
    err = new BigInteger(statErr);
  }


  public static void GetFileTimes(ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BigInteger atimeSec, out BigInteger atimeNsec, out BigInteger mtimeSec, out BigInteger mtimeNsec, out bool isDir, out bool isSymlink, out BigInteger device, out BigInteger inode, out BigInteger linkCount, out BigInteger err) {
    ok = false;
    isDir = false;
    isSymlink = false;
    err = new BigInteger(0);
    atimeSec = new BigInteger(0);
    atimeNsec = new BigInteger(0);
    mtimeSec = new BigInteger(0);
    mtimeNsec = new BigInteger(0);
    device = new BigInteger(0);
    inode = new BigInteger(0);
    linkCount = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    if (!TryStatPath(pathStr, followSymlink, out var statResult, out var statErr)) {
      // The symbolic path model has no component-length failure constructor;
      // an overlong component is therefore observed as an unresolved path.
      err = new BigInteger(statErr == ENAMETOOLONG ? ENOENT : statErr);
      return;
    }
    ok = true;
    isDir = StatIsDirectory(statResult);
    isSymlink = (statResult.st_mode & S_IFMT) == S_IFLNK;
    device = new BigInteger(statResult.st_dev);
    inode = new BigInteger(statResult.st_ino);
    linkCount = new BigInteger(statResult.st_nlink);
    atimeSec = new BigInteger(statResult.st_atim.tv_sec);
    atimeNsec = new BigInteger(statResult.st_atim.tv_nsec);
    mtimeSec = new BigInteger(statResult.st_mtim.tv_sec);
    mtimeNsec = new BigInteger(statResult.st_mtim.tv_nsec);
  }


  private static void SetPathTimes(
    ISequence<Dafny.Rune> path,
    bool followSymlink,
    Timespec[] times,
    out bool ok,
    out BigInteger err
  ) {
    ok = false;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    int flags = followSymlink ? 0 : AT_SYMLINK_NOFOLLOW;
    int rc;
    try {
      rc = utimensatPath(AT_FDCWD, pathStr, times, flags);
    } catch {
      rc = -1;
    }
    if (rc == 0) {
      ok = true;
      return;
    }
    err = new BigInteger(Marshal.GetLastWin32Error());
  }

  public static void SetFileTimes(
    ISequence<Dafny.Rune> path,
    bool followSymlink,
    BigInteger atimeSec,
    BigInteger atimeNsec,
    BigInteger mtimeSec,
    BigInteger mtimeNsec,
    out bool ok,
    out BigInteger err
  ) {
    if (!TryToLong(atimeSec, out var atimeSecValue)
        || !TryToLong(atimeNsec, out var atimeNsecValue)
        || !TryToLong(mtimeSec, out var mtimeSecValue)
        || !TryToLong(mtimeNsec, out var mtimeNsecValue)) {
      ok = false;
      err = new BigInteger(EINVAL);
      return;
    }
    SetPathTimes(
      path, followSymlink,
      new[] {
        BuildExactTimespec(atimeSecValue, atimeNsecValue),
        BuildExactTimespec(mtimeSecValue, mtimeNsecValue)
      },
      out ok, out err
    );
  }

  public static void SetFileTimesNow(
    ISequence<Dafny.Rune> path,
    bool followSymlink,
    out bool ok,
    out BigInteger err
  ) {
    SetPathTimes(
      path, followSymlink,
      new[] { BuildCurrentTimespec(), BuildCurrentTimespec() },
      out ok, out err
    );
  }

  public static void SetFileAccessTimeNow(
    ISequence<Dafny.Rune> path,
    bool followSymlink,
    out bool ok,
    out BigInteger err
  ) {
    SetPathTimes(
      path, followSymlink,
      new[] { BuildCurrentTimespec(), BuildKeepTimespec() },
      out ok, out err
    );
  }

  public static void SetFileModificationTimeNow(
    ISequence<Dafny.Rune> path,
    bool followSymlink,
    out bool ok,
    out BigInteger err
  ) {
    SetPathTimes(
      path, followSymlink,
      new[] { BuildKeepTimespec(), BuildCurrentTimespec() },
      out ok, out err
    );
  }


  public static void GetFileMode(ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out uint mode, out BigInteger err) {
    ok = false;
    mode = 0;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    if (!TryStatPath(pathStr, followSymlink, out var statResult, out var statErr)) {
      err = new BigInteger(statErr);
      return;
    }
    ok = true;
    mode = statResult.st_mode & PermissionModeMask;
  }


  public static void IsSymlink(ISequence<Dafny.Rune> path, out bool ok, out bool isSymlink, out BigInteger err) {
    ok = false;
    isSymlink = false;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    // Always use lstat to check the symlink itself
    if (!TryStatPath(pathStr, false, out var statResult, out var statErr)) {
      err = new BigInteger(statErr);
      return;
    }
    ok = true;
    isSymlink = (statResult.st_mode & S_IFMT) == S_IFLNK;
  }

  public static void CreateFile(ISequence<Dafny.Rune> path, out bool ok, out BigInteger err) {
    ok = false;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(EINVAL);
      return;
    }
    int fd;
    try {
      fd = open(pathStr, O_WRONLY | O_CREAT | O_NONBLOCK | O_NOCTTY, DefaultCreateMode);
    } catch {
      fd = -1;
    }
    if (fd < 0) {
      err = new BigInteger(Marshal.GetLastWin32Error());
      return;
    }
    try {
      close(fd);
    } catch {
    }
    ok = true;
  }

  public static void WriteFile(ISequence<Dafny.Rune> path, ISequence<Dafny.Rune> data, out bool ok, out BigInteger err) {
    ok = false;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(EINVAL);
      return;
    }
    var text = data?.ToVerbatimString(false) ?? string.Empty;
    var bytes = Encoding.Latin1.GetBytes(text);
    int fd;
    try {
      fd = open(pathStr, O_WRONLY | O_CREAT | O_TRUNC | O_NOCTTY, DefaultCreateMode);
    } catch {
      fd = -1;
    }
    if (fd < 0) {
      err = new BigInteger(Marshal.GetLastWin32Error());
      return;
    }

    var writeOk = TryWriteAllToFd(fd, bytes, out var writeErr);
    int closeRc;
    try {
      closeRc = close(fd);
    } catch {
      closeRc = -1;
    }
    if (!writeOk) {
      err = new BigInteger(writeErr);
      return;
    }
    if (closeRc < 0) {
      err = new BigInteger(Marshal.GetLastWin32Error());
      return;
    }
    ok = true;
  }

  public static void CreateSymlink(ISequence<Dafny.Rune> path, ISequence<Dafny.Rune> target, out bool ok, out BigInteger err) {
    ok = false;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    var targetStr = target?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(EINVAL);
      return;
    }
    int rc;
    try {
      rc = symlink(targetStr, pathStr);
    } catch {
      rc = -1;
    }
    if (rc == 0) {
      ok = true;
      return;
    }
    err = new BigInteger(Marshal.GetLastWin32Error());
  }

  public static void GetFileStatus(
      ISequence<Dafny.Rune> path,
      bool followSymlink,
      out bool ok,
      out BenchWorld._IFileStatus status,
      out BigInteger err) {
    ok = false;
    status = BenchWorld.FileStatus.Default();
    err = BigInteger.Zero;
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    if (!TryStatPath(pathStr, followSymlink, out var statResult, out var statErr)) {
      // Match the symbolic path model, which represents an overlong unresolved
      // component as a missing path rather than a separate host errno.
      err = new BigInteger(statErr == ENAMETOOLONG ? ENOENT : statErr);
      return;
    }

    status = FileStatusFromStat(statResult);
    ok = true;
  }

  private static BenchWorld._IFileStatus FileStatusFromStat(Stat statResult) {
    BenchWorld._IFileKind kind;
    var kindBits = statResult.st_mode & S_IFMT;
    if (kindBits == S_IFDIR) {
      kind = BenchWorld.FileKind.create_DirectoryKind();
    } else if (kindBits == S_IFLNK) {
      kind = BenchWorld.FileKind.create_SymlinkKind();
    } else if (kindBits == S_IFBLK) {
      kind = BenchWorld.FileKind.create_BlockDeviceKind();
    } else if (kindBits == S_IFCHR) {
      kind = BenchWorld.FileKind.create_CharacterDeviceKind();
    } else if (kindBits == S_IFIFO) {
      kind = BenchWorld.FileKind.create_FifoKind();
    } else if (kindBits == S_IFSOCK) {
      kind = BenchWorld.FileKind.create_SocketKind();
    } else {
      // Linux stat reports S_IFREG for ordinary files. Keep an ordinary-file
      // fallback for runtimes whose libc exposes an unknown nonzero type.
      kind = BenchWorld.FileKind.create_RegularKind();
    }
    var size = new BigInteger(Math.Max(0L, statResult.st_size));
    var blocks = new BigInteger(Math.Max(0L, statResult.st_blocks));
    // Retain the positive high-level projection for StorageInfo callers.
    var ioBlockBytes = new BigInteger(
      statResult.st_blksize > 0 ? statResult.st_blksize : 4096L
    );
    return BenchWorld.FileStatus.create_FileStatus(
      kind,
      statResult.st_mode & PermissionModeMask,
      BenchWorld.Ownership.create_Ownership(
        new BigInteger(statResult.st_uid),
        new BigInteger(statResult.st_gid)
      ),
      BenchWorld.StorageInfo.create_StorageInfo(size, blocks, ioBlockBytes),
      BenchWorld.FileTimes.create_FileTimes(
        new BigInteger(statResult.st_atim.tv_sec),
        new BigInteger(statResult.st_atim.tv_nsec),
        new BigInteger(statResult.st_mtim.tv_sec),
        new BigInteger(statResult.st_mtim.tv_nsec),
        new BigInteger(statResult.st_ctim.tv_sec),
        new BigInteger(statResult.st_ctim.tv_nsec)
      ),
      BenchWorld.HostInodeKey.create_HostInodeKey(
        new BigInteger(statResult.st_dev),
        new BigInteger(statResult.st_ino)
      ),
      new BigInteger(statResult.st_nlink)
    );
  }

  public static void DeletePath(ISequence<Dafny.Rune> path, out bool ok, out BigInteger err) {
    ok = false;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    int rc;
    try {
      rc = unlink(pathStr);
    } catch {
      rc = -1;
    }
    if (rc == 0) {
      ok = true;
      return;
    }
    err = new BigInteger(Marshal.GetLastWin32Error());
  }

  private static bool TryPublicPath(
      ISequence<Dafny.Rune> path, out string pathText, out BigInteger err) {
    pathText = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathText) || !IsAbiPath(pathText)) {
      err = new BigInteger(string.IsNullOrEmpty(pathText) ? ENOENT : EINVAL);
      return false;
    }
    err = BigInteger.Zero;
    return true;
  }

  private static void BoolResultFromNative(int result, out bool ok, out BigInteger err) {
    ok = result == 0;
    var nativeErr = ok ? 0 : Marshal.GetLastPInvokeError();
    err = new BigInteger(nativeErr == 0 && !ok ? EIO : nativeErr);
  }

  public static void CreateDirectory(
      ISequence<Dafny.Rune> path, uint mode, out bool ok, out BigInteger err) {
    if (!TryPublicPath(path, out var pathText, out err)) {
      ok = false;
      return;
    }
    BoolResultFromNative(mkdir(pathText, mode & PermissionModeMask), out ok, out err);
  }

  public static void RemoveDirectory(
      ISequence<Dafny.Rune> path, out bool ok, out BigInteger err) {
    if (!TryPublicPath(path, out var pathText, out err)) {
      ok = false;
      return;
    }
    BoolResultFromNative(rmdir(pathText), out ok, out err);
  }

  public static void CreateHardLink(
      ISequence<Dafny.Rune> source,
      ISequence<Dafny.Rune> target,
      out bool ok,
      out BigInteger err) {
    if (!TryPublicPath(source, out var sourceText, out err) ||
        !TryPublicPath(target, out var targetText, out err)) {
      ok = false;
      return;
    }
    BoolResultFromNative(linkPath(sourceText, targetText), out ok, out err);
  }

  public static void UnlinkPath(
      ISequence<Dafny.Rune> path, out bool ok, out BigInteger err) {
    if (!TryPublicPath(path, out var pathText, out err)) {
      ok = false;
      return;
    }
    BoolResultFromNative(unlink(pathText), out ok, out err);
  }

  public static void TruncateFile(
      ISequence<Dafny.Rune> path,
      BigInteger size,
      out bool ok,
      out BigInteger err) {
    if (!TryPublicPath(path, out var pathText, out err) ||
        size < BigInteger.Zero || size > new BigInteger(long.MaxValue)) {
      ok = false;
      if (err == BigInteger.Zero) err = new BigInteger(EINVAL);
      return;
    }
    BoolResultFromNative(truncatePath(pathText, (long)size), out ok, out err);
  }

  public static void CreateSpecialNode(
      ISequence<Dafny.Rune> path,
      BenchWorld._ISpecialNodeKind kind,
      uint mode,
      BigInteger major,
      BigInteger minor,
      out bool ok,
      out BigInteger err) {
    if (!TryPublicPath(path, out var pathText, out err) ||
        major < BigInteger.Zero || major > new BigInteger(uint.MaxValue) ||
        minor < BigInteger.Zero || minor > new BigInteger(uint.MaxValue)) {
      ok = false;
      if (err == BigInteger.Zero) err = new BigInteger(EINVAL);
      return;
    }
    var permissionMode = mode & PermissionModeMask;
    int result;
    if (kind.is_FifoNode) {
      result = makeFifo(pathText, permissionMode);
    } else {
      var typeMode = kind.is_BlockDeviceNode ? S_IFBLK : S_IFCHR;
      var device = makeDevice((uint)major, (uint)minor);
      result = makeNode(pathText, permissionMode | (uint)typeMode, device);
    }
    BoolResultFromNative(result, out ok, out err);
  }

  private static void SyncPath(
      string path,
      BenchWorld._ISyncMode mode,
      out bool ok,
      out BigInteger err) {
    var fd = open(path, O_RDONLY | O_NONBLOCK | O_NOCTTY, 0);
    if (fd < 0) {
      ok = false;
      var openErr = Marshal.GetLastPInvokeError();
      err = new BigInteger(openErr == 0 ? EIO : openErr);
      return;
    }
    int result;
    if (mode.is_SyncDataOnly) {
      result = fdatasync(fd);
    } else if (mode.is_SyncContainingFilesystem) {
      result = syncfs(fd);
    } else {
      result = fsync(fd);
    }
    var operationErr = result < 0 ? Marshal.GetLastPInvokeError() : 0;
    var closeResult = close(fd);
    var closeErr = closeResult < 0 ? Marshal.GetLastPInvokeError() : 0;
    ok = operationErr == 0 && closeErr == 0;
    var finalErr = operationErr != 0 ? operationErr : closeErr;
    err = new BigInteger(finalErr == 0 && !ok ? EIO : finalErr);
  }

  public static void Sync(
      BenchWorld._ISyncTarget target,
      BenchWorld._ISyncMode mode,
      out bool ok,
      out BigInteger err) {
    err = BigInteger.Zero;
    if (target.is_AllSyncTargets) {
      if (!mode.is_SyncAllFilesystems) {
        ok = false;
        err = new BigInteger(EINVAL);
        return;
      }
      syncAll();
      ok = true;
      err = BigInteger.Zero;
      return;
    }
    if (mode.is_SyncAllFilesystems ||
        !TryPublicPath(target.dtor_path, out var pathText, out err)) {
      ok = false;
      if (err == BigInteger.Zero) err = new BigInteger(EINVAL);
      return;
    }
    SyncPath(pathText, mode, out ok, out err);
  }

  private static void SetStdoutTargetTimes(
    Timespec[] times,
    out bool ok,
    out BigInteger err
  ) {
    ok = false;
    err = new BigInteger(0);
    int rc;
    try {
      rc = futimens(1, times);
    } catch {
      rc = -1;
    }
    if (rc == 0) {
      ok = true;
      return;
    }
    err = new BigInteger(Marshal.GetLastWin32Error());
  }

  private static bool TryBuildTimestampUpdate(BenchWorld._ITimestampUpdate update, out Timespec value) {
    if (update.is_Current) {
      value = BuildCurrentTimespec();
      return true;
    }
    if (update.is_Keep) {
      value = BuildKeepTimespec();
      return true;
    }
    value = default;
    if (!TryToLong(update.dtor_sec, out var sec) || !TryToLong(update.dtor_nsec, out var nsec)) {
      return false;
    }
    value = BuildExactTimespec(sec, nsec);
    return true;
  }

  public static void SetStdoutTimes(
    BenchWorld._ITimestampUpdate atime,
    BenchWorld._ITimestampUpdate mtime,
    out bool ok,
    out BigInteger err
  ) {
    if (!TryBuildTimestampUpdate(atime, out var atimeValue)
        || !TryBuildTimestampUpdate(mtime, out var mtimeValue)) {
      ok = false;
      err = new BigInteger(EINVAL);
      return;
    }
    SetStdoutTargetTimes(
      new[] {
        atimeValue,
        mtimeValue
      },
      out ok, out err
    );
  }

  public static void SetStdoutTimesNow(
    out bool ok,
    out BigInteger err
  ) {
    SetStdoutTargetTimes(
      new[] { BuildCurrentTimespec(), BuildCurrentTimespec() },
      out ok, out err
    );
  }

  public static void SetStdoutAccessTimeNow(
    out bool ok,
    out BigInteger err
  ) {
    SetStdoutTargetTimes(
      new[] { BuildCurrentTimespec(), BuildKeepTimespec() },
      out ok, out err
    );
  }

  public static void SetStdoutModificationTimeNow(
    out bool ok,
    out BigInteger err
  ) {
    SetStdoutTargetTimes(
      new[] { BuildKeepTimespec(), BuildCurrentTimespec() },
      out ok, out err
    );
  }

  public static void Exit(BigInteger code) {
    int exitCode;
    try {
      exitCode = (int)code;
    } catch {
      exitCode = 1;
    }
    Environment.Exit(exitCode);
  }

  public static void SetFileMode(ISequence<Dafny.Rune> path, bool followSymlink, uint mode, out bool ok, out BigInteger err) {
    ok = false;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    uint modeValue = mode & PermissionModeMask;
    int rc;
    if (!followSymlink) {
      // Use fchmodat with AT_SYMLINK_NOFOLLOW for symlink control
      try {
        rc = fchmodat(AT_FDCWD, pathStr, modeValue, AT_SYMLINK_NOFOLLOW);
      } catch {
        rc = -1;
      }
      // If fchmodat with AT_SYMLINK_NOFOLLOW fails with ENOTSUP/EOPNOTSUPP on symlinks, that's expected
      if (rc < 0) {
        var errno = Marshal.GetLastWin32Error();
        // For symlinks, ENOTSUP is expected when trying to chmod without following
        if (errno == ENOTSUP || errno == EOPNOTSUPP) {
          // Check if it's actually a symlink
          if (TryStatPath(pathStr, false, out var statResult, out _)) {
            if ((statResult.st_mode & S_IFMT) == S_IFLNK) {
              // It's a symlink and we can't chmod it - this is OK, just return success
              ok = true;
              return;
            }
          }
        }
        err = new BigInteger(errno);
        return;
      }
    } else {
      // Follow symlinks - use regular chmod
      try {
        rc = chmod(pathStr, modeValue);
      } catch {
        rc = -1;
      }
      if (rc < 0) {
        err = new BigInteger(Marshal.GetLastWin32Error());
        return;
      }
    }
    ok = true;
  }

  public static uint GetUmask() {
    uint oldMask;
    try {
      // Get current umask by setting to 0, then restore it immediately
      oldMask = umask(0);
      umask(oldMask);
    } catch {
      // Default umask if we can't read it
      oldMask = 0x12; // 022 octal
    }
    return oldMask;
  }

  public static void OpenDir(
    ISequence<Dafny.Rune> path,
    out bool ok,
    out BigInteger handle,
    out BigInteger err
  ) {
    ok = false;
    handle = new BigInteger(0);
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    IntPtr dirPtr;
    var openErr = 0;
    try {
      dirPtr = opendir(pathStr);
    } catch {
      dirPtr = IntPtr.Zero;
      openErr = EIO;
    }
    if (dirPtr == IntPtr.Zero) {
      var errno = openErr != 0 ? openErr : Marshal.GetLastWin32Error();
      err = new BigInteger(errno == 0 ? EIO : errno);
      return;
    }

    lock (dirLock) {
      var id = nextDirHandle++;
      Dirs[id] = new DirEntry(dirPtr, pathStr);
      handle = new BigInteger(id);
      ok = true;
    }
  }

  public static void ResolvePathIdentity(
    ISequence<Dafny.Rune> path,
    out bool ok,
    out ISequence<Dafny.Rune> resolvedPath,
    out BigInteger err
  ) {
    ok = false;
    resolvedPath = Sequence<Dafny.Rune>.Empty;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }

    IntPtr canonicalPointer;
    var canonicalErr = 0;
    try {
      canonicalPointer = realpath(pathStr, IntPtr.Zero);
    } catch {
      canonicalPointer = IntPtr.Zero;
      canonicalErr = EIO;
    }
    if (canonicalPointer == IntPtr.Zero) {
      var errno = canonicalErr != 0 ? canonicalErr : Marshal.GetLastWin32Error();
      err = new BigInteger(errno == 0 ? EIO : errno);
      return;
    }
    string canonicalPath;
    try {
      canonicalPath = Marshal.PtrToStringAnsi(canonicalPointer) ?? string.Empty;
    } finally {
      free(canonicalPointer);
    }
    resolvedPath = Sequence<Dafny.Rune>.UnicodeFromString(canonicalPath);
    ok = true;
  }

  public static void ReadDir(BigInteger handle, out bool hasMore, out ISequence<Dafny.Rune> name, out bool isDir, out bool isSymlink, out BigInteger err) {
    hasMore = false;
    name = Sequence<Dafny.Rune>.Empty;
    isDir = false;
    isSymlink = false;
    err = new BigInteger(0);
    int id;
    try {
      id = (int)handle;
    } catch {
      err = new BigInteger(EINVAL);
      return;
    }
    DirEntry entry;
    lock (dirLock) {
      if (!Dirs.TryGetValue(id, out entry)) {
        err = new BigInteger(EINVAL);
        return;
      }
    }
    if (entry == null || entry.DirPtr == IntPtr.Zero) {
      err = new BigInteger(EINVAL);
      return;
    }
    IntPtr entryPtr;
    try {
      // Clear errno before readdir
      Marshal.SetLastSystemError(0);
      entryPtr = readdir(entry.DirPtr);
    } catch {
      return;
    }
    if (entryPtr == IntPtr.Zero) {
      // EOF or error - check errno to distinguish
      var errno = Marshal.GetLastWin32Error();
      if (errno == 0) {
        // EOF
        hasMore = false;
      } else {
        err = new BigInteger(errno);
      }
      return;
    }
    var dirent = Marshal.PtrToStructure<Dirent>(entryPtr);
    // Extract null-terminated name from d_name
    var nameBytes = dirent.d_name;
    var nameLen = 0;
    while (nameLen < nameBytes.Length && nameBytes[nameLen] != 0) {
      nameLen++;
    }
    var nameStr = Encoding.UTF8.GetString(nameBytes, 0, nameLen);
    // Skip "." and ".." entries
    if (nameStr == "." || nameStr == "..") {
      // Recursively read next entry
      ReadDir(handle, out hasMore, out name, out isDir, out isSymlink, out err);
      return;
    }
    hasMore = true;
    name = Sequence<Dafny.Rune>.UnicodeFromString(nameStr);
    isDir = (dirent.d_type == DT_DIR);
    isSymlink = (dirent.d_type == DT_LNK);
  }

  public static void CloseDir(BigInteger handle) {
    int id;
    try {
      id = (int)handle;
    } catch {
      return;
    }
    DirEntry entry = null;
    lock (dirLock) {
      if (Dirs.TryGetValue(id, out entry)) {
        Dirs.Remove(id);
      }
    }
    if (entry != null && entry.DirPtr != IntPtr.Zero) {
      try {
        closedir(entry.DirPtr);
      } catch {
      }
    }
  }

  public static void IsDirectory(ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out bool isDir, out BigInteger err) {
    ok = false;
    isDir = false;
    err = new BigInteger(0);
    var pathStr = path?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    if (!TryStatPath(pathStr, followSymlink, out var statResult, out var statErr)) {
      err = new BigInteger(statErr);
      return;
    }
    ok = true;
    isDir = StatIsDirectory(statResult);
  }

  public static void RenamePath(ISequence<Dafny.Rune> source, ISequence<Dafny.Rune> target, out bool ok, out BigInteger err) {
    ok = false;
    err = new BigInteger(0);
    var sourceStr = source?.ToVerbatimString(false) ?? string.Empty;
    var targetStr = target?.ToVerbatimString(false) ?? string.Empty;
    int rc;
    var renameErr = 0;
    try {
      rc = rename(sourceStr, targetStr);
    } catch {
      rc = -1;
      renameErr = EIO;
    }

    if (rc == 0) {
      ok = true;
      return;
    }
    var errno = renameErr != 0 ? renameErr : Marshal.GetLastWin32Error();
    err = new BigInteger(errno == 0 ? EIO : errno);
  }

}

public static class BenchIOExtern {
  public static readonly BenchIO.IO ProcessHandle = new BenchIO.IO();

  public static void Exit(BigInteger code) {
    IOExtern.Exit(code);
  }
}

namespace BenchIO {
  public partial class IO {
    public BenchWorld._IResult<Dafny.ISequence<Dafny.Rune>> ReadFile(ISequence<Dafny.Rune> path) {
      IOExtern.ReadFileContents(path, out var ok, out var content);
      if (ok) {
        return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Ok(content);
      }
      IOExtern.IsDirectory(path, true, out var okDir, out var isDir, out var errCode);
      if (okDir && isDir) {
        return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Err(BenchWorld.IOError.create_IsDirectory());
      }
      if (errCode == new BigInteger(13)) {
        return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Err(BenchWorld.IOError.create_PermissionDenied());
      }
      return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Err(BenchWorld.IOError.create_NoSuchFile());
    }

    public void ReadFileWithOutcome(
        ISequence<Dafny.Rune> path,
        out ISequence<Dafny.Rune> data,
        out BigInteger err) {
      IOExtern.ReadFileWithOutcome(path, out data, out err);
    }

    public BenchWorld._IResult<Dafny.ISequence<Dafny.Rune>> ReadLink(ISequence<Dafny.Rune> path) {
      IOExtern.ReadLinkTarget(path, out var ok, out var target, out var errCode);
      if (ok) {
        return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Ok(target);
      }
      if (errCode == new BigInteger(2)) {
        return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Err(BenchWorld.IOError.create_NoSuchFile());
      }
      if (errCode == new BigInteger(13)) {
        return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Err(BenchWorld.IOError.create_PermissionDenied());
      }
      if (errCode == new BigInteger(20)) {
        return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Err(BenchWorld.IOError.create_NotDirectory());
      }
      if (errCode == new BigInteger(22) || errCode == new BigInteger(40)) {
        return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Err(BenchWorld.IOError.create_InvalidPath());
      }
      return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Err(
        BenchWorld.IOError.create_Other(IOExtern.ErrnoMessage(errCode))
      );
    }

    public Dafny.ISequence<Dafny.Rune> ReadStdinAll() {
      return IOExtern.ReadStdin();
    }

    public void ReadStdinWithOutcome(
        out ISequence<Dafny.Rune> data,
        out BigInteger err) {
      IOExtern.ReadStdinWithOutcome(out data, out err);
    }

    public void AppendStdout(Dafny.ISequence<Dafny.Rune> b) {
      IOExtern.WriteStdout(b);
    }

    public void AppendStderr(Dafny.ISequence<Dafny.Rune> b) {
      IOExtern.WriteStderr(b);
    }

    public void WriteStdoutWithOutcome(
        Dafny.ISequence<Dafny.Rune> b,
        out BigInteger committed,
        out BigInteger err) {
      IOExtern.WriteStdoutWithOutcome(b, out committed, out err);
    }

    public void WriteStderrWithOutcome(
        Dafny.ISequence<Dafny.Rune> b,
        out BigInteger committed,
        out BigInteger err) {
      IOExtern.WriteStderrWithOutcome(b, out committed, out err);
    }

    public Dafny.ISequence<Dafny.Rune> GetCLocaleErrnoText(BigInteger err) {
      return IOExtern.GetCLocaleErrnoText(err);
    }

    public Dafny.ISequence<Dafny.Rune> QuoteafPath(Dafny.ISequence<Dafny.Rune> path) {
      return IOExtern.QuoteafPath(path);
    }

    public Dafny.ISequence<Dafny.Rune> QuoteArgument(Dafny.ISequence<Dafny.Rune> value) {
      return IOExtern.QuoteArgument(value);
    }

    public Dafny.ISequence<Dafny.Rune> GetCwd() {
      IOExtern.GetCurrentDirectory(out var ok, out var value);
      if (ok) {
        return value;
      }
      return Sequence<Dafny.Rune>.UnicodeFromString(".");
    }

    public BenchWorld._IResult<Dafny.ISequence<Dafny.Rune>> GetEnv(Dafny.ISequence<Dafny.Rune> key) {
      IOExtern.GetEnv(key, out var ok, out var value);
      if (ok) {
        return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Ok(value);
      }
      var keyStr = key?.ToVerbatimString(false) ?? string.Empty;
      return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Err(
        BenchWorld.IOError.create_Other(Sequence<Dafny.Rune>.UnicodeFromString("missing env key: " + keyStr))
      );
    }

    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> GetEnvironment() {
      return IOExtern.GetEnvironment();
    }

    public BenchWorld._IResult<Dafny.ISequence<Dafny.Rune>> GetLoginName() {
      IOExtern.GetLoginName(out var ok, out var value);
      if (ok) {
        return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Ok(value);
      }
      return BenchWorld.Result<Dafny.ISequence<Dafny.Rune>>.create_Err(
        BenchWorld.IOError.create_Other(Sequence<Dafny.Rune>.UnicodeFromString("missing login name"))
      );
    }

    public BigInteger Now() {
      IOExtern.GetCurrentTime(out var sec, out var nsec);
      return sec;
    }

    public void ParseTimestamp(Dafny.ISequence<Dafny.Rune> timestamp, BigInteger nowSec, BigInteger nowNsec, out bool ok, out BigInteger sec, out BigInteger nsec) {
      IOExtern.ParseTimestamp(timestamp, nowSec, nowNsec, out ok, out sec, out nsec);
    }

    public void ParseDate(Dafny.ISequence<Dafny.Rune> date, BigInteger refSec, BigInteger refNsec, out bool ok, out BigInteger sec, out BigInteger nsec) {
      IOExtern.ParseDate(date, refSec, refNsec, out ok, out sec, out nsec);
    }

    public void PathExists(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool found, out BigInteger err) {
      IOExtern.PathExists(path, followSymlink, out found, out err);
    }


    public void SetFileTimesNow(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BigInteger err) {
      IOExtern.SetFileTimesNow(path, followSymlink, out ok, out err);
    }

    public void SetFileAccessTimeNow(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BigInteger err) {
      IOExtern.SetFileAccessTimeNow(path, followSymlink, out ok, out err);
    }

    public void SetFileModificationTimeNow(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BigInteger err) {
      IOExtern.SetFileModificationTimeNow(path, followSymlink, out ok, out err);
    }


    public void GetFileTimes(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BigInteger atimeSec, out BigInteger atimeNsec, out BigInteger mtimeSec, out BigInteger mtimeNsec, out bool isDir, out bool isSymlink, out BigInteger device, out BigInteger inode, out BigInteger linkCount, out BigInteger err) {
      IOExtern.GetFileTimes(path, followSymlink, out ok, out atimeSec, out atimeNsec, out mtimeSec, out mtimeNsec, out isDir, out isSymlink, out device, out inode, out linkCount, out err);
    }


    public void SetFileTimes(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, BigInteger atimeSec, BigInteger atimeNsec, BigInteger mtimeSec, BigInteger mtimeNsec, out bool ok, out BigInteger err) {
      IOExtern.SetFileTimes(path, followSymlink, atimeSec, atimeNsec, mtimeSec, mtimeNsec, out ok, out err);
    }


    public void GetFileMode(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out uint mode, out BigInteger err) {
      IOExtern.GetFileMode(path, followSymlink, out ok, out mode, out err);
    }


    public void IsDirectory(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out bool isDir, out BigInteger err) {
      IOExtern.IsDirectory(path, followSymlink, out ok, out isDir, out err);
    }


    public void IsDirectoryStrict(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out bool isDir, out BigInteger err) {
      IOExtern.IsDirectory(path, followSymlink, out ok, out isDir, out err);
    }


    public void IsSymlink(Dafny.ISequence<Dafny.Rune> path, out bool ok, out bool isSymlink, out BigInteger err) {
      IOExtern.IsSymlink(path, out ok, out isSymlink, out err);
    }

    public void CreateFile(Dafny.ISequence<Dafny.Rune> path, out bool ok, out BigInteger err) {
      IOExtern.CreateFile(path, out ok, out err);
    }

    public void WriteFile(Dafny.ISequence<Dafny.Rune> path, Dafny.ISequence<Dafny.Rune> data, out bool ok, out BigInteger err) {
      IOExtern.WriteFile(path, data, out ok, out err);
    }

    public void CreateSymlink(Dafny.ISequence<Dafny.Rune> path, Dafny.ISequence<Dafny.Rune> target, out bool ok, out BigInteger err) {
      IOExtern.CreateSymlink(path, target, out ok, out err);
    }

    public void DeletePath(Dafny.ISequence<Dafny.Rune> path, out bool ok, out BigInteger err) {
      IOExtern.DeletePath(path, out ok, out err);
    }

    public void CreateDirectory(
        Dafny.ISequence<Dafny.Rune> path,
        uint mode,
        out bool ok,
        out BigInteger err) {
      IOExtern.CreateDirectory(path, mode, out ok, out err);
    }

    public void RemoveDirectory(
        Dafny.ISequence<Dafny.Rune> path,
        out bool ok,
        out BigInteger err) {
      IOExtern.RemoveDirectory(path, out ok, out err);
    }

    public void CreateHardLink(
        Dafny.ISequence<Dafny.Rune> source,
        Dafny.ISequence<Dafny.Rune> target,
        out bool ok,
        out BigInteger err) {
      IOExtern.CreateHardLink(source, target, out ok, out err);
    }

    public void UnlinkPath(
        Dafny.ISequence<Dafny.Rune> path,
        out bool ok,
        out BigInteger err) {
      IOExtern.UnlinkPath(path, out ok, out err);
    }

    public void TruncateFile(
        Dafny.ISequence<Dafny.Rune> path,
        BigInteger size,
        out bool ok,
        out BigInteger err) {
      IOExtern.TruncateFile(path, size, out ok, out err);
    }

    public void CreateSpecialNode(
        Dafny.ISequence<Dafny.Rune> path,
        BenchWorld._ISpecialNodeKind kind,
        uint mode,
        BigInteger major,
        BigInteger minor,
        out bool ok,
        out BigInteger err) {
      IOExtern.CreateSpecialNode(path, kind, mode, major, minor, out ok, out err);
    }

    public void Sync(
        BenchWorld._ISyncTarget target,
        BenchWorld._ISyncMode mode,
        out bool ok,
        out BigInteger err) {
      IOExtern.Sync(target, mode, out ok, out err);
    }

    public void GetFileStatus(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BenchWorld._IFileStatus status, out BigInteger err) {
      IOExtern.GetFileStatus(path, followSymlink, out ok, out status, out err);
    }

    public void SetStdoutTimesNow(out bool ok, out BigInteger err) {
      IOExtern.SetStdoutTimesNow(out ok, out err);
    }

    public void SetStdoutAccessTimeNow(out bool ok, out BigInteger err) {
      IOExtern.SetStdoutAccessTimeNow(out ok, out err);
    }

    public void SetStdoutModificationTimeNow(out bool ok, out BigInteger err) {
      IOExtern.SetStdoutModificationTimeNow(out ok, out err);
    }

    public void SetStdoutTimes(BenchWorld._ITimestampUpdate atime, BenchWorld._ITimestampUpdate mtime, out bool ok, out BigInteger err) {
      IOExtern.SetStdoutTimes(atime, mtime, out ok, out err);
    }

    public void SetFileMode(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, uint mode, out bool ok, out BigInteger err) {
      IOExtern.SetFileMode(path, followSymlink, mode, out ok, out err);
    }

    public uint GetUmask() {
      return IOExtern.GetUmask();
    }

    public void OpenDir(
      Dafny.ISequence<Dafny.Rune> path,
      out bool ok,
      out BigInteger handle,
      out BigInteger err
    ) {
      IOExtern.OpenDir(path, out ok, out handle, out err);
    }

    public void ResolvePathIdentity(
      Dafny.ISequence<Dafny.Rune> path,
      out bool ok,
      out Dafny.ISequence<Dafny.Rune> resolvedPath,
      out BigInteger err
    ) {
      IOExtern.ResolvePathIdentity(path, out ok, out resolvedPath, out err);
    }

    public void ReadDir(BigInteger handle, out bool hasMore, out Dafny.ISequence<Dafny.Rune> name, out bool isDir, out bool isSymlink, out BigInteger err) {
      IOExtern.ReadDir(handle, out hasMore, out name, out isDir, out isSymlink, out err);
    }

    public void CloseDir(BigInteger handle) {
      IOExtern.CloseDir(handle);
    }

    public void RenamePath(Dafny.ISequence<Dafny.Rune> source, Dafny.ISequence<Dafny.Rune> target, out bool ok, out BigInteger err) {
      IOExtern.RenamePath(source, target, out ok, out err);
    }
  }
}
