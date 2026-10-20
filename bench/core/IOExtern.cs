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
using Errno = Errnos.__default;

public static partial class IOExtern {

  // Independent capability namespace: legacy CloseDir cannot consume these DIR*.
  private sealed class LiveDirectoryCapability {
    internal readonly IntPtr Pointer;
    internal int? Descriptor;
    internal readonly bool IncludeDots;
    internal LiveDirectoryCapability(IntPtr pointer, bool includeDots = false) {
      Pointer = pointer;
      IncludeDots = includeDots;
    }
  }
  private static readonly Dictionary<BigInteger, LiveDirectoryCapability> LiveDirectories = new();
  private static readonly object liveDirectoryGate = new();
  private static BigInteger nextLiveDirectoryHandle = -BigInteger.One;

  [DllImport("libc", SetLastError = true)]
  private static extern int fchdir(int fd);
  [DllImport("libc", SetLastError = true)]
  private static extern int chdir(string path);

  private static BenchWorld._IDirectoryResponse DirectoryResponse(
      int err = 0, ISequence<Dafny.Rune> path = null,
      BenchWorld._IFileStatus status = null, BigInteger? handle = null,
      int fd = 0, BenchWorld._IDirectoryRead read = null) {
    return BenchWorld.DirectoryResponse.create_DirectoryResponse(
      new BigInteger(err), path ?? Sequence<Dafny.Rune>.Empty,
      status ?? BenchWorld.FileStatus.Default(), handle ?? BigInteger.Zero,
      new BigInteger(fd), read ?? BenchWorld.DirectoryRead.create_DirectoryEnd());
  }

  private static bool LiveDirectoryForHandle(BigInteger handle, out LiveDirectoryCapability capability) {
    lock (liveDirectoryGate) { return LiveDirectories.TryGetValue(handle, out capability); }
  }

  private static bool LiveDirectoryOwnsDescriptor(BigInteger descriptor, out int fd) {
    fd = -1;
    if (descriptor < int.MinValue || descriptor > int.MaxValue) return false;
    var candidate = (int)descriptor;
    lock (liveDirectoryGate) {
      foreach (var capability in LiveDirectories.Values) {
        if (capability.Descriptor == candidate) { fd = candidate; return true; }
      }
    }
    return false;
  }

  public static BenchWorld._IDirectoryResponse DirectoryGetCwd() {
    GetCurrentDirectory(out var path, out var err);
    return DirectoryResponse((int)err, path: path);
  }

  public static BenchWorld._IDirectoryResponse DirectoryCurrentStatus() {
    GetFileStatus(Sequence<Dafny.Rune>.UnicodeFromString("."), true,
      out var ok, out var status, out var err);
    return DirectoryResponse((int)err, status: status);
  }

  public static BenchWorld._IDirectoryResponse DirectoryOpenParent() {
    var pointer = opendir("..");
    var err = pointer == IntPtr.Zero ? Marshal.GetLastPInvokeError() : 0;
    if (err != 0) return DirectoryResponse(err);
    lock (liveDirectoryGate) {
      var handle = nextLiveDirectoryHandle--;
      LiveDirectories.Add(handle, new LiveDirectoryCapability(pointer));
      return DirectoryResponse(handle: handle);
    }
  }

  // Absolute operands do not consult the parent capability, as with fstatat/openat.
  // Relative operands borrow an owned DIR* without reconstructing its pathname.
  private static bool TryDirectoryCapabilityFd(BigInteger parent, string path,
      out int fd, out int err) {
    fd = AT_FDCWD;
    err = 0;
    if (path.StartsWith("/", StringComparison.Ordinal)) return true;
    IntPtr pointer;
    if (LiveDirectories.TryGetValue(parent, out var capability)) {
      pointer = capability.Pointer;
    } else if (Dirs.TryGetValue(parent, out var legacy) && legacy.DirPtr != IntPtr.Zero) {
      pointer = legacy.DirPtr;
    } else {
      err = parent < 0 ? EBADF : EINVAL;
      return false;
    }
    fd = dirfd(pointer);
    if (fd >= 0) return true;
    err = Marshal.GetLastPInvokeError();
    return false;
  }

  private static BenchWorld._IDirectoryResponse DirectoryOpenAt(int parentFd,
      string path, bool includeDots) {
    var descriptor = openat(parentFd, path,
      O_RDONLY | O_NONBLOCK | O_DIRECTORY | O_CLOEXEC, 0);
    if (descriptor < 0) return DirectoryResponse(Marshal.GetLastPInvokeError());
    var pointer = fdopendir(descriptor);
    if (pointer == IntPtr.Zero) {
      var err = Marshal.GetLastPInvokeError();
      close(descriptor);
      return DirectoryResponse(err);
    }
    var handle = nextLiveDirectoryHandle--;
    LiveDirectories.Add(handle, new LiveDirectoryCapability(pointer, includeDots));
    return DirectoryResponse(handle: handle);
  }

  public static BenchWorld._IDirectoryResponse DirectoryOpenAtCwd(
      ISequence<Dafny.Rune> path, bool includeDots) {
    if (!TryPublicPath(path, out var raw, out var err, allowEmpty: true))
      return DirectoryResponse((int)err);
    if (raw.Length == 0) return DirectoryResponse(ENOENT);
    lock (liveDirectoryGate) {
      return DirectoryOpenAt(AT_FDCWD, raw, includeDots);
    }
  }

  public static BenchWorld._IDirectoryResponse DirectoryOpenAtDir(BigInteger parent,
      ISequence<Dafny.Rune> path, bool includeDots) {
    if (!TryPublicPath(path, out var raw, out var err, allowEmpty: true))
      return DirectoryResponse((int)err);
    if (raw.Length == 0) return DirectoryResponse(ENOENT);
    lock (liveDirectoryGate) {
      lock (dirLock) {
        if (!TryDirectoryCapabilityFd(parent, raw, out var fd, out var fdErr))
          return DirectoryResponse(fdErr);
        return DirectoryOpenAt(fd, raw, includeDots);
      }
    }
  }

  public static BenchWorld._IDirectoryResponse DirectoryStatusAtDir(BigInteger parent,
      ISequence<Dafny.Rune> path, bool followSymlink) {
    if (!TryPublicPath(path, out var raw, out var err, allowEmpty: true))
      return DirectoryResponse((int)err);
    if (raw.Length == 0) return DirectoryResponse(ENOENT);
    lock (liveDirectoryGate) {
      lock (dirLock) {
        if (!TryDirectoryCapabilityFd(parent, raw, out var fd, out var fdErr))
          return DirectoryResponse(fdErr);
        var result = fstatat(fd, raw, out var status, followSymlink ? 0 : AT_SYMLINK_NOFOLLOW);
        var statErr = result < 0 ? Marshal.GetLastPInvokeError() : 0;
        return DirectoryResponse(statErr, status: result < 0 ? null : FileStatusFromStat(status));
      }
    }
  }

  public static BenchWorld._IDirectoryResponse DirectorySetModeAtDir(BigInteger parent,
      ISequence<Dafny.Rune> path, bool followSymlink, uint mode) {
    if (!TryPublicPath(path, out var raw, out var err, allowEmpty: true))
      return DirectoryResponse((int)err);
    if (raw.Length == 0) return DirectoryResponse(ENOENT);
    lock (liveDirectoryGate) {
      lock (dirLock) {
        if (!TryDirectoryCapabilityFd(parent, raw, out var fd, out var fdErr))
          return DirectoryResponse(fdErr);
        var result = fchmodat(fd, raw, mode & PermissionModeMask,
          followSymlink ? 0 : AT_SYMLINK_NOFOLLOW);
        return DirectoryResponse(result < 0 ? Marshal.GetLastPInvokeError() : 0);
      }
    }
  }

  public static BenchWorld._IDirectoryResponse DirectoryOpenedStatus(BigInteger handle) {
    lock (liveDirectoryGate) {
      if (!LiveDirectories.TryGetValue(handle, out var capability)) return DirectoryResponse(EBADF);
      var fd = dirfd(capability.Pointer);
      if (fd < 0) return DirectoryResponse(Marshal.GetLastPInvokeError());
      GetDirectoryStatusForDescriptor(fd, out var ok, out var status, out var err);
      return DirectoryResponse((int)err, status: ok ? status : null);
    }
  }

  public static BenchWorld._IDirectoryResponse DirectoryGetDescriptor(BigInteger handle) {
    if (!LiveDirectoryForHandle(handle, out var capability)) return DirectoryResponse(EBADF);
    var fd = dirfd(capability.Pointer);
    var err = fd < 0 ? Marshal.GetLastPInvokeError() : 0;
    if (err != 0) return DirectoryResponse(err);
    lock (liveDirectoryGate) { capability.Descriptor = fd; }
    return DirectoryResponse(fd: fd);
  }

  public static BenchWorld._IDirectoryResponse DirectoryFchdir(BigInteger descriptor) {
    if (!LiveDirectoryOwnsDescriptor(descriptor, out var fd)) return DirectoryResponse(EBADF);
    var result = fchdir(fd);
    var err = result < 0 ? Marshal.GetLastPInvokeError() : 0;
    return DirectoryResponse(err);
  }

  public static BenchWorld._IDirectoryResponse DirectoryChdirParent() {
    var result = chdir("..");
    var err = result < 0 ? Marshal.GetLastPInvokeError() : 0;
    return DirectoryResponse(err);
  }

  public static BenchWorld._IDirectoryResponse DirectoryFstat(BigInteger descriptor) {
    if (!LiveDirectoryOwnsDescriptor(descriptor, out var fd)) return DirectoryResponse(EBADF);
    var result = fstat(fd, out var nativeStatus);
    var err = result < 0 ? Marshal.GetLastPInvokeError() : 0;
    return DirectoryResponse(err, status: err == 0 ? FileStatusFromStat(nativeStatus) : null);
  }

  public static BenchWorld._IDirectoryResponse DirectoryReadNext(BigInteger handle) {
    if (!LiveDirectoryForHandle(handle, out var capability)) return DirectoryResponse(EBADF);
    while (true) {
      Marshal.SetLastPInvokeError(0);
      var pointer = readdir(capability.Pointer);
      var err = pointer == IntPtr.Zero ? Marshal.GetLastPInvokeError() : 0;
      if (pointer == IntPtr.Zero) return DirectoryResponse(err);
      var entry = Marshal.PtrToStructure<Dirent>(pointer);
      var nameLength = 0;
      while (nameLength < entry.d_name.Length && entry.d_name[nameLength] != 0) nameLength++;
      var name = Encoding.UTF8.GetString(entry.d_name, 0, nameLength);
      var dot = name == "." || name == "..";
      if (dot && !capability.IncludeDots) continue;
      return DirectoryResponse(read: BenchWorld.DirectoryRead.create_DirectoryItem(
        Sequence<Dafny.Rune>.UnicodeFromString(name),
        DirectoryEntryKindFromNative(dot ? DT_DIR : entry.d_type), new BigInteger(entry.d_ino)));
    }
  }

  public static BenchWorld._IDirectoryResponse DirectoryEntryLstat(ISequence<Dafny.Rune> name) {
    GetFileStatus(name, false, out var ok, out var status, out var err);
    return DirectoryResponse((int)err, status: status);
  }

  public static BenchWorld._IDirectoryResponse DirectoryClose(BigInteger handle) {
    LiveDirectoryCapability capability;
    lock (liveDirectoryGate) {
      if (!LiveDirectories.Remove(handle, out capability)) return DirectoryResponse(EBADF);
    }
    var result = closedir(capability.Pointer);
    var err = result < 0 ? Marshal.GetLastPInvokeError() : 0;
    return DirectoryResponse(err);
  }

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
        if (availabilityErrno == EBADF && nativeFd == -1) continue;
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
    public bool IncludeDots { get; }

    public DirEntry(IntPtr dirPtr, string path, bool includeDots) {
      DirPtr = dirPtr;
      Path = path;
      IncludeDots = includeDots;
    }
  }

  private static readonly Dictionary<BigInteger, DirEntry> Dirs = new Dictionary<BigInteger, DirEntry>();
  private static BigInteger nextDirHandle = BigInteger.One;
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
  private static extern int openat(int dirfd, string path, int flags, uint mode);

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
  private static extern int fstatat(int dirfd, string path, out Stat buf, int flags);

  [DllImport("libc", SetLastError = true)]
  private static extern int statx(int dirfd, string pathname, int flags, uint mask, out Statx buf);

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

  [DllImport("libc", EntryPoint = "linkat", SetLastError = true)]
  private static extern int linkAt(int oldDirFd, string source, int newDirFd, string target, int flags);

  [DllImport("libc", SetLastError = true)]
  private static extern IntPtr opendir(string path);

  [DllImport("libc", SetLastError = true)]
  private static extern IntPtr fdopendir(int fd);

  [DllImport("libc", SetLastError = true)]
  private static extern int dirfd(IntPtr dirp);

  [DllImport("libc", SetLastError = true)]
  private static extern IntPtr readdir(IntPtr dirp);

  [DllImport("libc", SetLastError = true)]
  private static extern int closedir(IntPtr dirp);

  [DllImport("libc", SetLastError = true)]
  private static extern IntPtr realpath(string path, IntPtr resolvedPath);

  [DllImport("libc", SetLastError = true)]
  private static extern IntPtr getcwd(IntPtr buffer, UIntPtr size);

  [DllImport("libc")]
  private static extern void free(IntPtr pointer);

  [DllImport("libc")]
  private static extern IntPtr strerror(int errnum);

  private const int F_GETFL = 3;
  private const int O_APPEND = 0x400;
  private const int SEEK_SET = 0;
  private const int SEEK_CUR = 1;
  private const int O_WRONLY = 0x1;
  private const int O_RDONLY = 0x0;
  private const int O_CREAT = 0x40;
  private const int O_TRUNC = 0x200;
  private const int O_NONBLOCK = 0x800;
  private const int O_NOCTTY = 0x100;
  private const int O_DIRECTORY = 0x10000;
  private const int O_CLOEXEC = 0x80000;
  private const int AT_FDCWD = -100;
  private const int AT_SYMLINK_NOFOLLOW = 0x100;
  private const int AT_NO_AUTOMOUNT = 0x800;
  private const int AT_EMPTY_PATH = 0x1000;
  private const uint STATX_INO = 0x100;
  // STATX_BASIC_STATS: the set of fields FileStatusFromStatx reads and
  // GetOpenDirectoryStatusContractFields (IOContract.dfy) promises the caller
  // (kind/mode, nlink, uid/gid, atime/mtime/ctime, ino, size, blocks). No
  // smaller mask suffices: every one of these bits backs a FileStatus field
  // FileStatusFromStatx fills in unconditionally.
  private const uint STATX_BASIC_STATS = 0x7ff;
  private const int S_IFMT = 0xF000;
  private const int S_IFIFO = 0x1000;
  private const int S_IFCHR = 0x2000;
  private const int S_IFDIR = 0x4000;
  private const int S_IFBLK = 0x6000;
  private const int S_IFLNK = 0xA000;
  private const int S_IFSOCK = 0xC000;
  private const uint PermissionModeMask = 0x0FFF;
  private static readonly int ENOENT = (int)Errno.ENOENT;
  private static readonly int EINTR = (int)Errno.EINTR;
  private static readonly int EIO = (int)Errno.EIO;
  private static readonly int EBADF = (int)Errno.EBADF;
  private static readonly int EINVAL = (int)Errno.EINVAL;
  private static readonly int ENAMETOOLONG = (int)Errno.ENAMETOOLONG;
  private static readonly int EOPNOTSUPP = (int)Errno.EOPNOTSUPP;
  private static readonly int EOVERFLOW = (int)Errno.EOVERFLOW;
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
  private const byte DT_FIFO = 1;
  private const byte DT_CHR = 2;
  private const byte DT_DIR = 4;
  private const byte DT_BLK = 6;
  private const byte DT_REG = 8;
  private const byte DT_LNK = 10;
  private const byte DT_SOCK = 12;

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
  private struct StatxTimestamp {
    public long tv_sec;
    public uint tv_nsec;
    public int __reserved;
  }

  // Mirrors the Linux kernel's fixed 256-byte struct statx (linux/stat.h). GNU
  // coreutils' fstat_for_ino issues the raw statx(2) syscall requesting only
  // STATX_INO on an open directory fd (see ls.c's fstat_for_ino), and the
  // kernel still returns the basic fields for local filesystems, so this
  // layout is read the same way FileStatusFromStat reads Stat.
  [StructLayout(LayoutKind.Sequential)]
  private struct Statx {
    public uint stx_mask;
    public uint stx_blksize;
    public ulong stx_attributes;
    public uint stx_nlink;
    public uint stx_uid;
    public uint stx_gid;
    public ushort stx_mode;
    public ushort __spare0;
    public ulong stx_ino;
    public ulong stx_size;
    public ulong stx_blocks;
    public ulong stx_attributes_mask;
    public StatxTimestamp stx_atime;
    public StatxTimestamp stx_btime;
    public StatxTimestamp stx_ctime;
    public StatxTimestamp stx_mtime;
    public uint stx_rdev_major;
    public uint stx_rdev_minor;
    public uint stx_dev_major;
    public uint stx_dev_minor;
    public ulong stx_mnt_id;
    public uint stx_dio_mem_align;
    public uint stx_dio_offset_align;
    [MarshalAs(UnmanagedType.ByValArray, SizeConst = 12)]
    public ulong[] __spare3;
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
    err = EBADF;
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
    err = EBADF;
    invoked = false;
    if (!FindCapability(handle, out var capability)) return;
    lock (capability.Gate) {
      if (capability.Closed) return;
      invoked = true;
      WriteDescriptor(capability.NativeFd, data, out count, out err);
    }
  }

  public static void CloseCapability(BigInteger handle, out int err, out bool invoked) {
    err = EBADF;
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
    err = EBADF;
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
    err = EBADF;
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
    err = EBADF;
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

  public static void ReadFile(
      ISequence<Dafny.Rune> path,
      bool readContents,
      out ISequence<Dafny.Rune> content,
      out BigInteger err,
      out BenchWorld._IFileReadStage stage) {
    content = Sequence<Dafny.Rune>.Empty;
    err = BigInteger.Zero;
    stage = BenchWorld.FileReadStage.create_OpenFailed();
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
    stage = BenchWorld.FileReadStage.create_ReadFailed();
    var bytes = Array.Empty<byte>();
    var readErr = 0;
    if (readContents) ReadAllFromFdWithOutcome(fd, out bytes, out readErr);
    var closeResult = close(fd);
    var closeErr = closeResult < 0 ? Marshal.GetLastPInvokeError() : 0;
    content = Sequence<Dafny.Rune>.UnicodeFromString(Encoding.Latin1.GetString(bytes));
    var finalErr = readErr != 0 ? readErr : closeErr;
    err = new BigInteger(finalErr == 0 ? 0 : finalErr);
    if (readErr == 0 && closeErr != 0) {
      stage = BenchWorld.FileReadStage.create_CloseFailed();
    } else if (finalErr == 0) {
      stage = BenchWorld.FileReadStage.create_ReadSucceeded();
    }
  }

  public static void ReadStdin(
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

  public static void WriteStdout(
      ISequence<Dafny.Rune> content,
      out BigInteger committed,
      out BigInteger err) {
    WriteStandardWithOutcome(BigInteger.One, content, out committed, out err);

  }

  public static void WriteStderr(
      ISequence<Dafny.Rune> content,
      out BigInteger committed,
      out BigInteger err) {
    WriteStandardWithOutcome(new BigInteger(2), content, out committed, out err);

  }

  public static void GetEnv(ISequence<Dafny.Rune> name, out bool ok, out ISequence<Dafny.Rune> value) {
    ok = false;
    value = Sequence<Dafny.Rune>.Empty;
    var nameStr = name?.ToVerbatimString(false) ?? string.Empty;
    if (string.IsNullOrEmpty(nameStr) || nameStr.IndexOf('\0') >= 0 || nameStr.IndexOf('=') >= 0) {
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

  public static void GetCurrentDirectory(
      out ISequence<Dafny.Rune> value,
      out BigInteger err) {
    value = Sequence<Dafny.Rune>.Empty;
    err = BigInteger.Zero;
    var pointer = getcwd(IntPtr.Zero, UIntPtr.Zero);
    if (pointer == IntPtr.Zero) {
      var savedErrno = Marshal.GetLastPInvokeError();
      err = new BigInteger(savedErrno);
      return;
    }
    try {
      value = Sequence<Dafny.Rune>.UnicodeFromString(Marshal.PtrToStringUTF8(pointer)!);
    } finally {
      free(pointer);
    }
  }

  [DllImport("libc", SetLastError = true)]
  private static extern ulong getauxval(ulong tag);

  public static void GetAuxiliaryValue(BigInteger tag, out BigInteger value, out int err) {
    value = BigInteger.Zero;
    if (tag < BigInteger.Zero || tag > ulong.MaxValue) {
      err = EOVERFLOW; // EOVERFLOW: the request does not fit unsigned long on LP64.
      return;
    }
    if (!RuntimeInformation.IsOSPlatform(OSPlatform.Linux)
        || RuntimeInformation.ProcessArchitecture != Architecture.X64) {
      err = EOPNOTSUPP;
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
      err = EOPNOTSUPP;
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
    if (err < int.MinValue || err > int.MaxValue) {
      return Sequence<Dafny.Rune>.UnicodeFromString(
        "Unknown error " + err.ToString(CultureInfo.InvariantCulture));
    }
    var errValue = (int)err;
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

  private static bool IsQuoteafDoubleQuoteCompatible(byte value, bool atStart, bool singleton) {
    if (value < 0x20 || value >= 0x7f) return false;
    switch (value) {
      case (byte)'?': case (byte)'\\':
        return false;
      case (byte)'{': case (byte)'}':
        return singleton;
      case (byte)'#': case (byte)'~':
        return atStart;
      case (byte)'!': case (byte)'"': case (byte)'$': case (byte)'&':
      case (byte)'(': case (byte)')': case (byte)'*': case (byte)';':
      case (byte)'<': case (byte)'=': case (byte)'>': case (byte)'[':
      case (byte)'^': case (byte)'`': case (byte)'|':
        return false;
      default:
        return true;
    }
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
    for (var index = 0; index < pathBytes.Length; index++) {
      var value = pathBytes[index];
      encounteredSingleQuote |= value == (byte)'\'';
      allDoubleQuoteCompatible &= IsQuoteafDoubleQuoteCompatible(
        value, index == 0, pathBytes.Length == 1);
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
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    var buffer = new byte[MaxLinkPath];
    var length = readlink(pathStr, buffer, buffer.Length);
    if (length < 0) {
      var nativeErr = Marshal.GetLastPInvokeError();
      err = new BigInteger(nativeErr);
      return;
    }
    ok = true;
    target = Sequence<Dafny.Rune>.UnicodeFromString(Encoding.UTF8.GetString(buffer, 0, (int)length));
  }

  public static void PathExists(ISequence<Dafny.Rune> path, bool followSymlink, out bool exists, out BigInteger err) {
    exists = false;
    err = new BigInteger(0);
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
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
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
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
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    int flags = followSymlink ? 0 : AT_SYMLINK_NOFOLLOW;
    var rc = utimensatPath(AT_FDCWD, pathStr, times, flags);
    if (rc == 0) {
      ok = true;
      return;
    }
    var nativeErr = Marshal.GetLastPInvokeError();
    err = new BigInteger(nativeErr);
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
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
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
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
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
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    var fd = open(pathStr, O_WRONLY | O_CREAT | O_NONBLOCK | O_NOCTTY, DefaultCreateMode);
    if (fd < 0) {
      err = new BigInteger(Marshal.GetLastPInvokeError());
      return;
    }
    if (close(fd) < 0) {
      err = new BigInteger(Marshal.GetLastPInvokeError());
      return;
    }
    ok = true;
  }

  public static void WriteFile(
      ISequence<Dafny.Rune> path, ISequence<Dafny.Rune> data, uint createMode,
      out bool ok, out BigInteger err, out BigInteger committed,
      out BenchWorld._IFileWriteStage stage) {
    WriteFileWithFlags(path, data, O_WRONLY | O_CREAT | O_TRUNC | O_NOCTTY, createMode,
      out ok, out err, out committed, out stage);
  }

  public static void AppendFile(
      ISequence<Dafny.Rune> path, ISequence<Dafny.Rune> data,
      out bool ok, out BigInteger err, out BigInteger committed,
      out BenchWorld._IFileWriteStage stage) {
    WriteFileWithFlags(path, data, O_WRONLY | O_CREAT | O_APPEND | O_NOCTTY, DefaultCreateMode,
      out ok, out err, out committed, out stage);
  }

  private static void WriteFileWithFlags(
      ISequence<Dafny.Rune> path, ISequence<Dafny.Rune> data, int flags, uint createMode,
      out bool ok, out BigInteger err, out BigInteger committed,
      out BenchWorld._IFileWriteStage stage) {
    ok = false;
    committed = BigInteger.Zero;
    stage = BenchWorld.FileWriteStage.create_WriteOpenFailed();
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    var text = data?.ToVerbatimString(false) ?? string.Empty;
    var bytes = Encoding.Latin1.GetBytes(text);
    var fd = open(pathStr, flags, createMode & PermissionModeMask);
    if (fd < 0) {
      err = new BigInteger(Marshal.GetLastPInvokeError());
      return;
    }

    WriteAllToFdWithOutcome(fd, bytes, out var written, out var writeErr);
    committed = new BigInteger(written);
    var closeRc = close(fd);
    var closeErr = closeRc < 0 ? Marshal.GetLastPInvokeError() : 0;
    if (writeErr != 0) {
      err = new BigInteger(writeErr);
      stage = BenchWorld.FileWriteStage.create_WriteFailed();
      return;
    }
    if (closeRc < 0) {
      err = new BigInteger(closeErr);
      stage = BenchWorld.FileWriteStage.create_WriteCloseFailed();
      return;
    }
    ok = true;
    stage = BenchWorld.FileWriteStage.create_WriteSucceeded();
  }

  public static void CreateSymlink(ISequence<Dafny.Rune> path, ISequence<Dafny.Rune> target, out bool ok, out BigInteger err) {
    ok = false;
    err = new BigInteger(0);
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    if (!TryPublicPath(target, out var targetStr, out err, allowEmpty: true)) return;
    var rc = symlink(targetStr, pathStr);
    if (rc == 0) {
      ok = true;
      return;
    }
    var nativeErr = Marshal.GetLastPInvokeError();
    err = new BigInteger(nativeErr);
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
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    if (!TryStatPath(pathStr, followSymlink, out var statResult, out var statErr)) {
      err = new BigInteger(statErr);
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

  // Converts a raw statx(2) result into the same modeled status FileStatusFromStat
  // builds from struct stat. Local filesystems return the basic fields (mode,
  // size, times, ownership) even when only STATX_INO was requested, matching
  // the pinned GNU fstat_for_ino call this mirrors.
  private static BenchWorld._IFileStatus FileStatusFromStatx(Statx statxResult) {
    BenchWorld._IFileKind kind;
    var kindBits = (uint)statxResult.stx_mode & S_IFMT;
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
      kind = BenchWorld.FileKind.create_RegularKind();
    }
    var size = new BigInteger(statxResult.stx_size);
    var blocks = new BigInteger(statxResult.stx_blocks);
    var ioBlockBytes = new BigInteger(
      statxResult.stx_blksize > 0 ? statxResult.stx_blksize : 4096u
    );
    // Re-encode the split major/minor statx fields into the same glibc dev_t
    // bit layout struct stat's raw st_dev already uses (sysmacros.h makedev),
    // so a HostInodeKey built here compares equal to one built by
    // FileStatusFromStat for the same device.
    var devMajor = (ulong)statxResult.stx_dev_major;
    var devMinor = (ulong)statxResult.stx_dev_minor;
    var dev = new BigInteger(
      (devMinor & 0xFFUL) |
      ((devMajor & 0xFFFUL) << 8) |
      ((devMinor & ~0xFFUL) << 12) |
      ((devMajor & ~0xFFFUL) << 32)
    );
    return BenchWorld.FileStatus.create_FileStatus(
      kind,
      statxResult.stx_mode & PermissionModeMask,
      BenchWorld.Ownership.create_Ownership(
        new BigInteger(statxResult.stx_uid),
        new BigInteger(statxResult.stx_gid)
      ),
      BenchWorld.StorageInfo.create_StorageInfo(size, blocks, ioBlockBytes),
      BenchWorld.FileTimes.create_FileTimes(
        new BigInteger(statxResult.stx_atime.tv_sec),
        new BigInteger(statxResult.stx_atime.tv_nsec),
        new BigInteger(statxResult.stx_mtime.tv_sec),
        new BigInteger(statxResult.stx_mtime.tv_nsec),
        new BigInteger(statxResult.stx_ctime.tv_sec),
        new BigInteger(statxResult.stx_ctime.tv_nsec)
      ),
      BenchWorld.HostInodeKey.create_HostInodeKey(dev, new BigInteger(statxResult.stx_ino)),
      new BigInteger(statxResult.stx_nlink)
    );
  }

  public static void DeletePath(ISequence<Dafny.Rune> path, out bool ok, out BigInteger err) {
    ok = false;
    err = new BigInteger(0);
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    var rc = unlink(pathStr);
    if (rc == 0) {
      ok = true;
      return;
    }
    var nativeErr = Marshal.GetLastPInvokeError();
    err = new BigInteger(nativeErr);
  }

  private static bool TryPublicPath(
      ISequence<Dafny.Rune> path, out string pathText, out BigInteger err,
      bool allowEmpty = false) {
    pathText = path?.ToVerbatimString(false) ?? string.Empty;
    if ((!allowEmpty && string.IsNullOrEmpty(pathText)) || !IsAbiPath(pathText)) {
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
      bool followSource,
      out bool ok,
      out BigInteger err) {
    // Let native link select errno when an empty operand competes with another path error.
    if (!TryPublicPath(source, out var sourceText, out err, allowEmpty: true) ||
        !TryPublicPath(target, out var targetText, out err, allowEmpty: true)) {
      ok = false;
      return;
    }
    BoolResultFromNative(followSource
      ? linkAt(AT_FDCWD, sourceText, AT_FDCWD, targetText, 0x400)
      : linkPath(sourceText, targetText), out ok, out err);
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
    } catch (DllNotFoundException) {
      err = new BigInteger(EIO);
      return;
    } catch (EntryPointNotFoundException) {
      err = new BigInteger(EIO);
      return;
    }
    var nativeErr = rc == 0 ? 0 : Marshal.GetLastPInvokeError();
    if (rc == 0) {
      ok = true;
      return;
    }
    err = new BigInteger(nativeErr);
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
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }
    uint modeValue = mode & PermissionModeMask;
    var rc = followSymlink
      ? chmod(pathStr, modeValue)
      : fchmodat(AT_FDCWD, pathStr, modeValue, AT_SYMLINK_NOFOLLOW);
    BoolResultFromNative(rc, out ok, out err);
  }

  public static uint GetUmask() {
    // POSIX umask has no error result; observe and restore the process value.
    var previousMask = umask(0);
    umask(previousMask);
    return previousMask;
  }

  private static bool TryAtDirectoryFd(BigInteger parent, string path, out int fd, out BigInteger err) {
    fd = AT_FDCWD;
    err = BigInteger.Zero;
    if (path.StartsWith("/", StringComparison.Ordinal)) return true;
    lock (dirLock) {
      if (!Dirs.TryGetValue(parent, out var entry) || entry == null || entry.DirPtr == IntPtr.Zero) {
        err = new BigInteger(EINVAL);
        return false;
      }
      fd = dirfd(entry.DirPtr);
      if (fd < 0) {
        err = new BigInteger(Marshal.GetLastWin32Error());
        return false;
      }
    }
    return true;
  }

  private static BigInteger RegisterDirectory(IntPtr dirPtr, string path, bool includeDots) {
    lock (dirLock) {
      var id = nextDirHandle++;
      Dirs[id] = new DirEntry(dirPtr, path, includeDots);
      return id;
    }
  }

  public static void GetFileStatusAtDir(
    BigInteger parent, ISequence<Dafny.Rune> path, bool followSymlink,
    out bool ok, out BenchWorld._IFileStatus status, out BigInteger err
  ) {
    ok = false;
    status = BenchWorld.FileStatus.Default();
    err = BigInteger.Zero;
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    if (pathStr.Length == 0) {
      err = new BigInteger(ENOENT);
      return;
    }
    if (!TryAtDirectoryFd(parent, pathStr, out var fd, out err)) return;
    var rc = fstatat(fd, pathStr, out var nativeStatus, followSymlink ? 0 : AT_SYMLINK_NOFOLLOW);
    if (rc != 0) {
      err = new BigInteger(Marshal.GetLastWin32Error());
      return;
    }
    status = FileStatusFromStat(nativeStatus);
    ok = true;
  }

  public static void SetFileModeAtDir(
    BigInteger parent, ISequence<Dafny.Rune> path, bool followSymlink, uint mode,
    out bool ok, out BigInteger err
  ) {
    ok = false;
    err = BigInteger.Zero;
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    if (pathStr.Length == 0) {
      err = new BigInteger(ENOENT);
      return;
    }
    if (!TryAtDirectoryFd(parent, pathStr, out var fd, out err)) return;
    var rc = fchmodat(fd, pathStr, mode & PermissionModeMask, followSymlink ? 0 : AT_SYMLINK_NOFOLLOW);
    if (rc != 0) {
      err = new BigInteger(Marshal.GetLastWin32Error());
      return;
    }
    ok = true;
  }

  public static void OpenDirAtDir(
    BigInteger parent, ISequence<Dafny.Rune> path, bool includeDots,
    out bool ok, out BigInteger handle, out BigInteger err
  ) {
    ok = false;
    handle = BigInteger.Zero;
    err = BigInteger.Zero;
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    if (pathStr.Length == 0) {
      err = new BigInteger(ENOENT);
      return;
    }
    if (!TryAtDirectoryFd(parent, pathStr, out var fd, out err)) return;
    var openedFd = openat(fd, pathStr, O_RDONLY | O_NONBLOCK | O_DIRECTORY | O_CLOEXEC, 0);
    if (openedFd < 0) {
      err = new BigInteger(Marshal.GetLastWin32Error());
      return;
    }
    var dirPtr = fdopendir(openedFd);
    if (dirPtr == IntPtr.Zero) {
      var openErr = Marshal.GetLastWin32Error();
      close(openedFd);
      err = new BigInteger(openErr);
      return;
    }
    handle = RegisterDirectory(dirPtr, pathStr, includeDots);
    ok = true;
  }

  public static void OpenDir(
    ISequence<Dafny.Rune> path,
    bool includeDots,
    out bool ok,
    out BigInteger handle,
    out BigInteger err
  ) {
    ok = false;
    handle = new BigInteger(0);
    err = new BigInteger(0);
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
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

    handle = RegisterDirectory(dirPtr, pathStr, includeDots);
    ok = true;
  }

  public static void GetOpenDirectoryStatus(
    BigInteger handle,
    out bool ok,
    out BenchWorld._IFileStatus status,
    out BigInteger err
  ) {
    ok = false;
    status = BenchWorld.FileStatus.Default();
    err = BigInteger.Zero;
    var id = handle;
    DirEntry entry;
    lock (dirLock) {
      if (!Dirs.TryGetValue(id, out entry) || entry == null || entry.DirPtr == IntPtr.Zero) {
        err = new BigInteger(EINVAL);
        return;
      }
    }
    int fd;
    try {
      fd = dirfd(entry.DirPtr);
    } catch (DllNotFoundException) {
      err = new BigInteger(EIO);
      return;
    } catch (EntryPointNotFoundException) {
      err = new BigInteger(EIO);
      return;
    }
    if (fd < 0) {
      var fdErr = Marshal.GetLastWin32Error();
      err = new BigInteger(fdErr == 0 ? EIO : fdErr);
      return;
    }
    GetDirectoryStatusForDescriptor(fd, out ok, out status, out err);
  }

  private static void GetDirectoryStatusForDescriptor(int fd,
      out bool ok, out BenchWorld._IFileStatus status, out BigInteger err) {
    ok = false;
    status = BenchWorld.FileStatus.Default();
    err = BigInteger.Zero;
    int rc;
    Statx nativeStatus;
    try {
      // Mirrors GNU ls's fstat_for_ino (ls.c), which issues statx(fd, "",
      // AT_EMPTY_PATH, STATX_INO) rather than fstat(fd) on an already-open
      // directory fd. glibc's opendir() already performed its own internal
      // fstat before this call runs; using the same statx form GNU uses here
      // keeps this the single additional identity status per opened
      // directory instead of a second, differently-shaped fstat.
      rc = statx(fd, "", AT_EMPTY_PATH | AT_NO_AUTOMOUNT, STATX_INO, out nativeStatus);
    } catch (DllNotFoundException) {
      err = new BigInteger(EIO);
      return;
    } catch (EntryPointNotFoundException) {
      err = new BigInteger(EIO);
      return;
    }
    if (rc < 0) {
      var statErr = Marshal.GetLastWin32Error();
      err = new BigInteger(statErr == 0 ? EIO : statErr);
      return;
    }
    // The kernel may report a subset of the requested mask (STATX_INO here);
    // FileStatusFromStatx unconditionally reads every STATX_BASIC_STATS
    // field, so fail closed instead of claiming fields the kernel did not
    // actually report.
    if ((nativeStatus.stx_mask & STATX_BASIC_STATS) != STATX_BASIC_STATS) {
      err = new BigInteger(EIO);
      return;
    }
    status = FileStatusFromStatx(nativeStatus);
    ok = true;
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
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
    if (string.IsNullOrEmpty(pathStr)) {
      err = new BigInteger(ENOENT);
      return;
    }

    var canonicalPointer = realpath(pathStr, IntPtr.Zero);
    if (canonicalPointer == IntPtr.Zero) {
      var errno = Marshal.GetLastPInvokeError();
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

  private static void ReadDirRaw(BigInteger handle, out bool hasMore, out ISequence<Dafny.Rune> name, out byte dType, out BigInteger inode, out BigInteger err) {
    hasMore = false;
    name = Sequence<Dafny.Rune>.Empty;
    dType = DT_UNKNOWN;
    inode = BigInteger.Zero;
    err = new BigInteger(0);
    var id = handle;
    DirEntry entry;
    lock (dirLock) {
      if (!Dirs.TryGetValue(id, out entry) || entry == null) {
        err = new BigInteger(EINVAL);
        return;
      }
    }
    if (entry == null || entry.DirPtr == IntPtr.Zero) {
      err = new BigInteger(EINVAL);
      return;
    }
    var includeDots = entry.IncludeDots;
    IntPtr entryPtr;
    try {
      // Clear errno before readdir
      Marshal.SetLastSystemError(0);
      entryPtr = readdir(entry.DirPtr);
    } catch {
      err = new BigInteger(EIO);
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
    if (!includeDots && (nameStr == "." || nameStr == "..")) {
      // Recursively read next entry
      ReadDirRaw(handle, out hasMore, out name, out dType, out inode, out err);
      return;
    }
    hasMore = true;
    inode = new BigInteger(dirent.d_ino);
    name = Sequence<Dafny.Rune>.UnicodeFromString(nameStr);
    // Dot entries name an opened directory or its parent even on filesystems
    // that report DT_UNKNOWN for these synthetic entries.
    dType = includeDots && (nameStr == "." || nameStr == "..")
      ? DT_DIR : dirent.d_type;
  }

  private static BenchWorld._IDirectoryEntryKind DirectoryEntryKindFromNative(byte dType) {
    switch (dType) {
      case DT_REG:
        return BenchWorld.DirectoryEntryKind.create_RegularDirentKind();
      case DT_DIR:
        return BenchWorld.DirectoryEntryKind.create_DirectoryDirentKind();
      case DT_LNK:
        return BenchWorld.DirectoryEntryKind.create_SymlinkDirentKind();
      case DT_FIFO:
        return BenchWorld.DirectoryEntryKind.create_FifoDirentKind();
      case DT_BLK:
        return BenchWorld.DirectoryEntryKind.create_BlockDeviceDirentKind();
      case DT_CHR:
        return BenchWorld.DirectoryEntryKind.create_CharacterDeviceDirentKind();
      case DT_SOCK:
        return BenchWorld.DirectoryEntryKind.create_SocketDirentKind();
      default:
        // DT_UNKNOWN and unsupported native kinds retain unknown evidence.
        return BenchWorld.DirectoryEntryKind.create_UnknownDirentKind();
    }
  }

  public static void ReadDir(BigInteger handle, out bool hasMore, out ISequence<Dafny.Rune> name, out BenchWorld._IDirectoryEntryKind kind, out BigInteger inode, out BigInteger err) {
    ReadDirRaw(handle, out hasMore, out name, out var dType, out inode, out err);
    kind = DirectoryEntryKindFromNative(dType);
  }

  public static void CloseDir(BigInteger handle, out bool ok, out BigInteger err) {
    ok = false;
    err = new BigInteger(EINVAL);
    var id = handle;
    DirEntry entry;
    lock (dirLock) {
      if (!Dirs.TryGetValue(id, out entry) || entry == null || entry.DirPtr == IntPtr.Zero) return;
      Dirs.Remove(id);
    }
    // glibc frees the DIR allocation before closing its fd; ownership ends even
    // when that final close reports an error.
    var rc = closedir(entry.DirPtr);
    var closeErr = rc == 0 ? 0 : Marshal.GetLastPInvokeError();
    ok = rc == 0;
    err = new BigInteger(closeErr);
  }

  public static void IsDirectory(ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out bool isDir, out BigInteger err) {
    ok = false;
    isDir = false;
    err = new BigInteger(0);
    if (!TryPublicPath(path, out var pathStr, out err, allowEmpty: true)) return;
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
    if (!TryPublicPath(source, out var sourceStr, out err, allowEmpty: true) ||
        !TryPublicPath(target, out var targetStr, out err, allowEmpty: true)) return;
    var rc = rename(sourceStr, targetStr);
    if (rc == 0) {
      ok = true;
      return;
    }
    err = new BigInteger(Marshal.GetLastPInvokeError());
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
    private void NativeReadFile(
        ISequence<Dafny.Rune> path,
        bool readContents,
        out ISequence<Dafny.Rune> data,
        out BigInteger err,
        out BenchWorld._IFileReadStage stage) {
      IOExtern.ReadFile(path, readContents, out data, out err, out stage);
    }

    public Results._IResult<Dafny.ISequence<Dafny.Rune>, BenchWorld._IIOError> ReadLink(ISequence<Dafny.Rune> path) {
      IOExtern.ReadLinkTarget(path, out var ok, out var target, out var errCode);
      if (ok) {
        return Results.Result<Dafny.ISequence<Dafny.Rune>, BenchWorld._IIOError>.create_Ok(target);
      }
      return Results.Result<Dafny.ISequence<Dafny.Rune>, BenchWorld._IIOError>.create_Err(
        BenchWorld.IOError.create_NativeFailure(errCode, IOExtern.GetCLocaleErrnoText(errCode))
      );
    }

    private void NativeReadStdin(
          out ISequence<Dafny.Rune> data,
        out BigInteger err) {
      IOExtern.ReadStdin(out data, out err);
    }

    private void NativeWriteStdout(
        Dafny.ISequence<Dafny.Rune> b,
          out BigInteger committed,
        out BigInteger err) {
      IOExtern.WriteStdout(b, out committed, out err);
    }

    private void NativeWriteStderr(
        Dafny.ISequence<Dafny.Rune> b,
          out BigInteger committed,
        out BigInteger err) {
      IOExtern.WriteStderr(b, out committed, out err);
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


    public Results._IResult<Dafny.ISequence<Dafny.Rune>, BenchWorld._IIOError> GetEnv(Dafny.ISequence<Dafny.Rune> key) {
      IOExtern.GetEnv(key, out var ok, out var value);
      if (ok) {
        return Results.Result<Dafny.ISequence<Dafny.Rune>, BenchWorld._IIOError>.create_Ok(value);
      }
      var keyStr = key?.ToVerbatimString(false) ?? string.Empty;
      return Results.Result<Dafny.ISequence<Dafny.Rune>, BenchWorld._IIOError>.create_Err(
        BenchWorld.IOError.create_Other(Sequence<Dafny.Rune>.UnicodeFromString("missing env key: " + keyStr))
      );
    }

    public Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> GetEnvironment() {
      return IOExtern.GetEnvironment();
    }

    public Results._IResult<Dafny.ISequence<Dafny.Rune>, BenchWorld._IIOError> GetLoginName() {
      IOExtern.GetLoginName(out var ok, out var value);
      if (ok) {
        return Results.Result<Dafny.ISequence<Dafny.Rune>, BenchWorld._IIOError>.create_Ok(value);
      }
      return Results.Result<Dafny.ISequence<Dafny.Rune>, BenchWorld._IIOError>.create_Err(
        BenchWorld.IOError.create_Other(Sequence<Dafny.Rune>.UnicodeFromString("missing login name"))
      );
    }

    public BigInteger Now() {
      IOExtern.GetCurrentTime(out var sec, out var nsec);
      return sec;
    }

    private void NativeParseTimestamp(Dafny.ISequence<Dafny.Rune> timestamp, BigInteger nowSec, BigInteger nowNsec, out bool ok, out BigInteger sec, out BigInteger nsec) {
      IOExtern.ParseTimestamp(timestamp, nowSec, nowNsec, out ok, out sec, out nsec);
    }

    private void NativeParseDate(Dafny.ISequence<Dafny.Rune> date, BigInteger refSec, BigInteger refNsec, out bool ok, out BigInteger sec, out BigInteger nsec) {
      IOExtern.ParseDate(date, refSec, refNsec, out ok, out sec, out nsec);
    }

    private void NativePathExists(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool found, out BigInteger err) {
      IOExtern.PathExists(path, followSymlink, out found, out err);
    }


    private void NativeSetFileTimesNow(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BigInteger err) {
      IOExtern.SetFileTimesNow(path, followSymlink, out ok, out err);
    }

    private void NativeSetFileAccessTimeNow(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BigInteger err) {
      IOExtern.SetFileAccessTimeNow(path, followSymlink, out ok, out err);
    }

    private void NativeSetFileModificationTimeNow(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BigInteger err) {
      IOExtern.SetFileModificationTimeNow(path, followSymlink, out ok, out err);
    }


    private void NativeGetFileTimes(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BigInteger atimeSec, out BigInteger atimeNsec, out BigInteger mtimeSec, out BigInteger mtimeNsec, out bool isDir, out bool isSymlink, out BigInteger device, out BigInteger inode, out BigInteger linkCount, out BigInteger err) {
      IOExtern.GetFileTimes(path, followSymlink, out ok, out atimeSec, out atimeNsec, out mtimeSec, out mtimeNsec, out isDir, out isSymlink, out device, out inode, out linkCount, out err);
    }


    private void NativeSetFileTimes(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, BigInteger atimeSec, BigInteger atimeNsec, BigInteger mtimeSec, BigInteger mtimeNsec, out bool ok, out BigInteger err) {
      IOExtern.SetFileTimes(path, followSymlink, atimeSec, atimeNsec, mtimeSec, mtimeNsec, out ok, out err);
    }


    private void NativeGetFileMode(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out uint mode, out BigInteger err) {
      IOExtern.GetFileMode(path, followSymlink, out ok, out mode, out err);
    }


    private void NativeIsDirectory(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out bool isDir, out BigInteger err) {
      IOExtern.IsDirectory(path, followSymlink, out ok, out isDir, out err);
    }


    private void NativeIsSymlink(Dafny.ISequence<Dafny.Rune> path, out bool ok, out bool isSymlink, out BigInteger err) {
      IOExtern.IsSymlink(path, out ok, out isSymlink, out err);
    }

    private void NativeCreateFile(Dafny.ISequence<Dafny.Rune> path, out bool ok, out BigInteger err) {
      IOExtern.CreateFile(path, out ok, out err);
    }

    private void NativeWriteFile(
        Dafny.ISequence<Dafny.Rune> path, Dafny.ISequence<Dafny.Rune> data, uint createMode,
        out bool ok, out BigInteger err, out BigInteger committed,
        out BenchWorld._IFileWriteStage stage) {
      IOExtern.WriteFile(path, data, createMode, out ok, out err, out committed, out stage);
    }

    private void NativeAppendFile(
        Dafny.ISequence<Dafny.Rune> path, Dafny.ISequence<Dafny.Rune> data,
        out bool ok, out BigInteger err, out BigInteger committed,
        out BenchWorld._IFileWriteStage stage) {
      IOExtern.AppendFile(path, data, out ok, out err, out committed, out stage);
    }

    private void NativeCreateSymlink(Dafny.ISequence<Dafny.Rune> path, Dafny.ISequence<Dafny.Rune> target, out bool ok, out BigInteger err) {
      IOExtern.CreateSymlink(path, target, out ok, out err);
    }

    private void NativeDeletePath(Dafny.ISequence<Dafny.Rune> path, out bool ok, out BigInteger err) {
      IOExtern.DeletePath(path, out ok, out err);
    }

    private void NativeCreateDirectory(
        Dafny.ISequence<Dafny.Rune> path,
        uint mode,
        out bool ok,
        out BigInteger err) {
      IOExtern.CreateDirectory(path, mode, out ok, out err);
    }

    private void NativeRemoveDirectory(
        Dafny.ISequence<Dafny.Rune> path,
        out bool ok,
        out BigInteger err) {
      IOExtern.RemoveDirectory(path, out ok, out err);
    }

    private void NativeCreateHardLink(
        Dafny.ISequence<Dafny.Rune> source,
        Dafny.ISequence<Dafny.Rune> target,
        bool followSource,
        out bool ok,
        out BigInteger err) {
      IOExtern.CreateHardLink(source, target, followSource, out ok, out err);
    }

    private void NativeUnlinkPath(
        Dafny.ISequence<Dafny.Rune> path,
        out bool ok,
        out BigInteger err) {
      IOExtern.UnlinkPath(path, out ok, out err);
    }

    private void NativeTruncateFile(
        Dafny.ISequence<Dafny.Rune> path,
        BigInteger size,
        out bool ok,
        out BigInteger err) {
      IOExtern.TruncateFile(path, size, out ok, out err);
    }

    private void NativeCreateSpecialNode(
        Dafny.ISequence<Dafny.Rune> path,
        BenchWorld._ISpecialNodeKind kind,
        uint mode,
        BigInteger major,
        BigInteger minor,
        out bool ok,
        out BigInteger err) {
      IOExtern.CreateSpecialNode(path, kind, mode, major, minor, out ok, out err);
    }

    private void NativeSync(
        BenchWorld._ISyncTarget target,
        BenchWorld._ISyncMode mode,
        out bool ok,
        out BigInteger err) {
      IOExtern.Sync(target, mode, out ok, out err);
    }

    public Results._IResult<Dafny.ISequence<Dafny.Rune>, BenchWorld._IIOError> ReadLinkAtCwd(Dafny.ISequence<Dafny.Rune> path) {
      return ReadLink(path);
    }

    private void NativeGetFileStatusAtDir(BigInteger parent, Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BenchWorld._IFileStatus status, out BigInteger err) {
      var response = IOExtern.DirectoryStatusAtDir(parent, path, followSymlink);
      err = response.dtor_err;
      ok = err == BigInteger.Zero;
      status = response.dtor_status;
    }

    private void NativeSetFileModeAtDir(BigInteger parent, Dafny.ISequence<Dafny.Rune> path, bool followSymlink, uint mode, out bool ok, out BigInteger err) {
      var response = IOExtern.DirectorySetModeAtDir(parent, path, followSymlink, mode);
      err = response.dtor_err;
      ok = err == BigInteger.Zero;
    }

    private void NativeOpenDirAtDir(BigInteger parent, Dafny.ISequence<Dafny.Rune> path, bool includeDots, out bool ok, out BigInteger handle, out BigInteger err) {
      var response = IOExtern.DirectoryOpenAtDir(parent, path, includeDots);
      err = response.dtor_err;
      ok = err == BigInteger.Zero;
      handle = response.dtor_handle;
    }

    private void NativeGetFileStatusAtCwd(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BenchWorld._IFileStatus status, out BigInteger err) {
      IOExtern.GetFileStatus(path, followSymlink, out ok, out status, out err);
    }

    private void NativeSetFileModeAtCwd(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, uint mode, out bool ok, out BigInteger err) {
      IOExtern.SetFileMode(path, followSymlink, mode, out ok, out err);
    }

    private void NativeOpenDirAtCwd(Dafny.ISequence<Dafny.Rune> path, bool includeDots, out bool ok, out BigInteger handle, out BigInteger err) {
      var response = IOExtern.DirectoryOpenAtCwd(path, includeDots);
      err = response.dtor_err;
      ok = err == BigInteger.Zero;
      handle = response.dtor_handle;
    }

    private void NativeGetFileStatus(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, out bool ok, out BenchWorld._IFileStatus status, out BigInteger err) {
      IOExtern.GetFileStatus(path, followSymlink, out ok, out status, out err);
    }

    private void NativeSetStdoutTimesNow(out bool ok, out BigInteger err) {
      IOExtern.SetStdoutTimesNow(out ok, out err);
    }

    private void NativeSetStdoutAccessTimeNow(out bool ok, out BigInteger err) {
      IOExtern.SetStdoutAccessTimeNow(out ok, out err);
    }

    private void NativeSetStdoutModificationTimeNow(out bool ok, out BigInteger err) {
      IOExtern.SetStdoutModificationTimeNow(out ok, out err);
    }

    private void NativeSetStdoutTimes(BenchWorld._ITimestampUpdate atime, BenchWorld._ITimestampUpdate mtime, out bool ok, out BigInteger err) {
      IOExtern.SetStdoutTimes(atime, mtime, out ok, out err);
    }

    private void NativeSetFileMode(Dafny.ISequence<Dafny.Rune> path, bool followSymlink, uint mode, out bool ok, out BigInteger err) {
      IOExtern.SetFileMode(path, followSymlink, mode, out ok, out err);
    }

    public uint GetUmask() {
      return IOExtern.GetUmask();
    }

    private void NativeOpenDir(
      Dafny.ISequence<Dafny.Rune> path,
      bool includeDots,
      out bool ok,
      out BigInteger handle,
      out BigInteger err
    ) {
      IOExtern.OpenDir(path, includeDots, out ok, out handle, out err);
    }

    private void NativeGetOpenDirectoryCapabilityStatus(BigInteger handle,
        out bool ok, out BenchWorld._IFileStatus status, out BigInteger err) {
      var response = IOExtern.DirectoryOpenedStatus(handle);
      err = response.dtor_err;
      ok = err == BigInteger.Zero;
      status = response.dtor_status;
    }

    private void NativeGetOpenDirectoryStatus(BigInteger handle, out bool ok, out BenchWorld._IFileStatus status, out BigInteger err) {
      IOExtern.GetOpenDirectoryStatus(handle, out ok, out status, out err);
    }

    private void NativeResolvePathIdentity(
      Dafny.ISequence<Dafny.Rune> path,
      out bool ok,
      out Dafny.ISequence<Dafny.Rune> resolvedPath,
      out BigInteger err
    ) {
      IOExtern.ResolvePathIdentity(path, out ok, out resolvedPath, out err);
    }

    private void NativeReadDir(BigInteger handle, out bool hasMore, out Dafny.ISequence<Dafny.Rune> name, out BenchWorld._IDirectoryEntryKind kind, out BigInteger inode, out BigInteger err) {
      IOExtern.ReadDir(handle, out hasMore, out name, out kind, out inode, out err);
    }

    private void NativeCloseDir(BigInteger handle, out bool ok, out BigInteger err) {
      IOExtern.CloseDir(handle, out ok, out err);
    }

    private void NativeRenamePath(Dafny.ISequence<Dafny.Rune> source, Dafny.ISequence<Dafny.Rune> target, out bool ok, out BigInteger err) {
      IOExtern.RenamePath(source, target, out ok, out err);
    }
    private BenchWorld._IDirectoryResponse NativeGetCwd() {
      return IOExtern.DirectoryGetCwd();
    }

    private BenchWorld._IDirectoryResponse NativeGetCwdDirectoryIdentity() {
      return IOExtern.DirectoryCurrentStatus();
    }

    private BenchWorld._IDirectoryResponse NativeOpenParentDirectory() {
      return IOExtern.DirectoryOpenParent();
    }

    private BenchWorld._IDirectoryResponse NativeGetDirectoryDescriptor(BigInteger handle) {
      return IOExtern.DirectoryGetDescriptor(handle);
    }

    private BenchWorld._IDirectoryResponse NativeFchdirDirectory(BigInteger fd) {
      return IOExtern.DirectoryFchdir(fd);
    }

    private BenchWorld._IDirectoryResponse NativeChdirParent() {
      return IOExtern.DirectoryChdirParent();
    }

    private BenchWorld._IDirectoryResponse NativeFstatDirectory(BigInteger fd) {
      return IOExtern.DirectoryFstat(fd);
    }

    private BenchWorld._IDirectoryResponse NativeReadDirectoryCapability(BigInteger handle) {
      return IOExtern.DirectoryReadNext(handle);
    }

    private BenchWorld._IDirectoryResponse NativeLstatCwdEntry(Dafny.ISequence<Dafny.Rune> name) {
      return IOExtern.DirectoryEntryLstat(name);
    }

    private BenchWorld._IDirectoryResponse NativeCloseDirectoryCapability(BigInteger handle) {
      return IOExtern.DirectoryClose(handle);
    }


  }
}
