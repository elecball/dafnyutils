// Linux errno values used by the benchmark's modeled and native IO boundaries.
module Errnos {
  // Operation is forbidden, e.g. creating a hard link to a directory.
  const EPERM: int := 1
  // A required path entry or symlink target does not exist, or the path is empty.
  const ENOENT: int := 2
  // A system call is interrupted by a signal before completing.
  const EINTR: int := 4
  // An underlying device or filesystem operation fails during IO.
  const EIO: int := 5
  // A file descriptor is invalid, closed, or not open for the requested access.
  const EBADF: int := 9
  // A required kernel or library memory allocation cannot be satisfied.
  const ENOMEM: int := 12
  // File access or directory traversal is denied by access permissions.
  const EACCES: int := 13
  // A resource is busy, e.g. removing or renaming a mount point.
  const EBUSY: int := 16
  // A create/link destination already exists, or rename targets a nonempty directory.
  const EEXIST: int := 17
  // A hard link or rename would cross a mounted filesystem boundary.
  const EXDEV: int := 18
  // A path component or a target required to be a directory is not a directory.
  const ENOTDIR: int := 20
  // An operation requiring a non-directory file encounters a directory.
  const EISDIR: int := 21
  // Arguments are invalid, e.g. invalid timestamps or an ABI path containing NUL.
  const EINVAL: int := 22
  // Opening a file or directory would exceed the system-wide open-file limit.
  const ENFILE: int := 23
  // Opening a file or directory would exceed this process's descriptor limit.
  const EMFILE: int := 24
  // A write or truncation would exceed a filesystem or process file-size limit.
  const EFBIG: int := 27
  // The filesystem has no free space or inodes for the requested change.
  const ENOSPC: int := 28
  // A write or metadata change is attempted on a read-only filesystem.
  const EROFS: int := 30
  // Creating a hard link or subdirectory would exceed an inode's link-count limit.
  const EMLINK: int := 31
  // Writing to a pipe with no readers or to a disconnected stream socket fails.
  const EPIPE: int := 32
  // A result is out of range or its output buffer is too small, e.g. for getcwd.
  const ERANGE: int := 34
  // A pathname or one of its components exceeds the supported length limit.
  const ENAMETOOLONG: int := 36
  // A directory being removed or replaced via rename still contains entries.
  const ENOTEMPTY: int := 39
  // Path resolution encounters a symlink loop or exceeds the symlink-follow limit.
  const ELOOP: int := 40
  // A result, such as file metadata, cannot be represented by the target ABI type.
  const EOVERFLOW: int := 75
  // The requested system call is not implemented by the running kernel.
  const ENOSYS: int := 38
  // The requested operation is unsupported by this filesystem or descriptor.
  const EOPNOTSUPP: int := 95
  // A write or creation would exceed a user's, group's, or project's disk quota.
  const EDQUOT: int := 122
}
