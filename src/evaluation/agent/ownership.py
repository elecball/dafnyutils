"""Bounded metadata handoff for terminated trusted-controller containers."""

from __future__ import annotations

import argparse
import os
import signal
import stat
import time
from pathlib import Path

_MAX_ENTRIES = 100000
_MAX_DEPTH = 128
_TIMEOUT_SECONDS = 120


def validate_handoff_sources(roots: tuple[Path, ...], *, protected: tuple[Path, ...]) -> None:
    """Reject substituted bind sources using fresh post-termination metadata only."""
    _validate_paths((*roots, *protected))
    protected_identities = {_source_identity(path) for path in protected}
    for root in roots:
        identity = _source_identity(root)
        if identity in protected_identities:
            raise ValueError("handoff source aliases a protected input")


def _source_identity(path: Path) -> tuple[int, int]:
    descriptor = _open_components(path, os.O_PATH)
    try:
        metadata = os.fstat(descriptor)
        if not (stat.S_ISDIR(metadata.st_mode) or stat.S_ISREG(metadata.st_mode)):
            raise ValueError("handoff source must be a real file or directory")
        if stat.S_ISREG(metadata.st_mode) and metadata.st_nlink != 1:
            raise ValueError("handoff source cannot be hardlinked")
        return metadata.st_dev, metadata.st_ino
    finally:
        os.close(descriptor)


def _validate_paths(paths: tuple[Path, ...]) -> None:
    for path in paths:
        if not path.is_absolute() or ".." in path.parts or path == Path("/"):
            raise ValueError("handoff paths must be strictly below root without parent traversal")


def handoff_ownership(
    roots: tuple[Path, ...], *, exclusions: tuple[Path, ...], uid: int, gid: int
) -> None:
    """Transfer declared output metadata without following links or changing contents."""
    if uid < 0 or gid < 0:
        raise ValueError("handoff UID/GID must be nonnegative")
    _validate_paths((*roots, *exclusions))
    budget = [_MAX_ENTRIES]
    deadline = time.monotonic() + _TIMEOUT_SECONDS
    for root in roots:
        if _excluded(root, exclusions):
            continue
        descriptor = _open_root(root)
        try:
            _handoff_entry(descriptor, root, exclusions, uid, gid, budget, deadline, 0)
        finally:
            os.close(descriptor)


def _open_root(path: Path) -> int:
    return _open_components(path, os.O_RDONLY | os.O_NONBLOCK)


def _open_components(path: Path, final_flags: int) -> int:
    descriptor = os.open("/", os.O_PATH | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        for index, component in enumerate(path.parts[1:]):
            flags = final_flags | os.O_CLOEXEC | os.O_NOFOLLOW
            if index < len(path.parts) - 2:
                flags = os.O_PATH | os.O_DIRECTORY | os.O_CLOEXEC | os.O_NOFOLLOW
            child = os.open(component, flags, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = child
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def _excluded(path: Path, exclusions: tuple[Path, ...]) -> bool:
    return any(path == excluded or path.is_relative_to(excluded) for excluded in exclusions)


def _handoff_entry(
    descriptor: int,
    path: Path,
    exclusions: tuple[Path, ...],
    uid: int,
    gid: int,
    budget: list[int],
    deadline: float,
    depth: int,
) -> None:
    _consume_budget(budget, deadline, depth)
    metadata = os.fstat(descriptor)
    directory = stat.S_ISDIR(metadata.st_mode)
    if not directory and not stat.S_ISREG(metadata.st_mode):
        raise ValueError("handoff root must be a regular file or directory")
    if not directory and metadata.st_nlink != 1:
        raise ValueError("handoff refuses hardlinked files")
    mode = stat.S_IMODE(metadata.st_mode)
    os.fchown(descriptor, uid, gid)
    if stat.S_IMODE(os.fstat(descriptor).st_mode) != mode:
        os.fchmod(descriptor, mode)
    if not directory:
        return
    _handoff_children(descriptor, path, exclusions, uid, gid, budget, deadline, depth)


def _consume_budget(budget: list[int], deadline: float, depth: int) -> None:
    budget[0] -= 1
    if budget[0] < 0 or depth > _MAX_DEPTH or time.monotonic() >= deadline:
        raise TimeoutError("candidate metadata handoff exceeded its bounds")


def _handoff_children(
    descriptor: int,
    path: Path,
    exclusions: tuple[Path, ...],
    uid: int,
    gid: int,
    budget: list[int],
    deadline: float,
    depth: int,
) -> None:
    with os.scandir(descriptor) as entries:
        for entry in entries:
            _consume_budget(budget, deadline, depth)
            child_path = path / entry.name
            if _excluded(child_path, exclusions):
                continue
            metadata = os.stat(entry.name, dir_fd=descriptor, follow_symlinks=False)
            if (
                stat.S_ISLNK(metadata.st_mode)
                or stat.S_ISSOCK(metadata.st_mode)
                or stat.S_ISFIFO(metadata.st_mode)
            ):
                continue
            if not (stat.S_ISDIR(metadata.st_mode) or stat.S_ISREG(metadata.st_mode)):
                raise ValueError("handoff refuses an unsupported filesystem entry")
            flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK
            if stat.S_ISDIR(metadata.st_mode):
                flags |= os.O_DIRECTORY
            child = os.open(entry.name, flags, dir_fd=descriptor)
            try:
                opened = os.fstat(child)
                if (metadata.st_dev, metadata.st_ino) != (opened.st_dev, opened.st_ino):
                    raise ValueError("handoff entry changed before metadata transfer")
                _handoff_entry(child, child_path, exclusions, uid, gid, budget, deadline, depth + 1)
            finally:
                os.close(child)


def _expired(signum: int, frame: object) -> None:
    raise TimeoutError("candidate metadata handoff timed out")


def main() -> None:
    """Apply the bounded handoff to explicitly supplied roots inside its helper."""
    parser = argparse.ArgumentParser()
    parser.add_argument("uid", type=int)
    parser.add_argument("gid", type=int)
    parser.add_argument("--root", action="append", type=Path, required=True)
    parser.add_argument("--exclude", action="append", type=Path, default=[])
    parser.add_argument("--protect", action="append", type=Path, default=[])
    parser.add_argument("--validate-sources", action="store_true")
    arguments = parser.parse_args()
    signal.signal(signal.SIGALRM, _expired)
    signal.alarm(_TIMEOUT_SECONDS)
    if arguments.validate_sources:
        validate_handoff_sources(tuple(arguments.root), protected=tuple(arguments.protect))
        return
    handoff_ownership(
        tuple(arguments.root),
        exclusions=tuple(arguments.exclude),
        uid=arguments.uid,
        gid=arguments.gid,
    )


if __name__ == "__main__":
    main()
