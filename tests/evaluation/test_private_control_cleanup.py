"""Exercise private-control collection with in-memory metadata and process boundaries."""

from __future__ import annotations

import os
import shutil
import stat
import subprocess
import tempfile
from contextlib import nullcontext
from dataclasses import dataclass, field
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from evaluation.agent import ownership, runtime
from evaluation.enums import MountMode
from evaluation.submission.container_mounts import ContainerMount, ContainerWorkspacePlan

_HOST_UID = 1013
_HOST_GID = 1013
_CONTROL = Path("/virtual/control")
_HOME = _CONTROL / "home"
_PRIVATE = _HOME / ".dotnet"
_PUBLIC = Path("/virtual/public")
_OUTPUT = Path("/virtual/output")
_RUN = Path("/virtual/run")


def _forbidden(*args: Any, **kwargs: Any) -> Any:
    raise AssertionError("real filesystem/process/content boundary must be faked")


@dataclass
class _Node:
    mode: int
    uid: int = _HOST_UID
    gid: int = _HOST_GID
    inode: int = 0
    links: int = 1

    def metadata(self) -> SimpleNamespace:
        return SimpleNamespace(
            st_mode=self.mode,
            st_uid=self.uid,
            st_gid=self.gid,
            st_dev=1,
            st_ino=self.inode,
            st_nlink=self.links,
        )


@dataclass
class _Memory:
    nodes: dict[Path, _Node] = field(default_factory=dict)
    descriptors: dict[int, Path] = field(default_factory=dict)
    events: list[str] = field(default_factory=list)
    chmods: list[Path] = field(default_factory=list)
    next_descriptor: int = 10

    def add(self, path: Path, mode: int, *, uid: int = _HOST_UID) -> None:
        self.nodes[path] = _Node(mode, uid=uid, inode=len(self.nodes) + 1)

    def open(self, path: str | Path, flags: int, *, dir_fd: int | None = None) -> int:
        target = Path(path)
        if dir_fd is not None:
            target = self.descriptors[dir_fd] / target
        node = self.nodes[target]
        if stat.S_ISLNK(node.mode) and flags & os.O_NOFOLLOW:
            raise OSError("refuse symlink component")
        if flags & os.O_DIRECTORY and not stat.S_ISDIR(node.mode):
            raise NotADirectoryError(str(target))
        self.next_descriptor += 1
        self.descriptors[self.next_descriptor] = target
        return self.next_descriptor

    def fchown(self, descriptor: int, uid: int, gid: int) -> None:
        node = self.nodes[self.descriptors[descriptor]]
        node.uid, node.gid = uid, gid
        node.mode &= ~(stat.S_ISUID | stat.S_ISGID)

    def fchmod(self, descriptor: int, mode: int) -> None:
        node = self.nodes[self.descriptors[descriptor]]
        node.mode = stat.S_IFMT(node.mode) | mode

    def chmod(self, path: Path, mode: int, **_: Any) -> None:
        node = self.nodes[path]
        if node.uid != _HOST_UID:
            raise PermissionError(1, "Operation not permitted", str(path))
        self.chmods.append(path)
        node.mode = stat.S_IFMT(node.mode) | mode

    def scandir(self, descriptor: int) -> Any:
        root = self.descriptors[descriptor]
        return nullcontext(
            [SimpleNamespace(name=path.name) for path in self.nodes if path.parent == root]
        )

    def walk(self, path: Path, **_: Any) -> Any:
        directories = [
            p.name for p, n in self.nodes.items() if p.parent == path and stat.S_ISDIR(n.mode)
        ]
        files = [
            p.name for p, n in self.nodes.items() if p.parent == path and not stat.S_ISDIR(n.mode)
        ]
        yield str(path), directories, files
        for name in directories:
            yield from self.walk(path / name)

    def remove_control(self, root: Path) -> None:
        self.events.append("control-cleanup")
        for path, node in self.nodes.items():
            if path.is_relative_to(root) and stat.S_ISDIR(node.mode):
                if node.uid != _HOST_UID or node.mode & 0o700 != 0o700:
                    raise PermissionError(str(path))
        self.nodes = {p: n for p, n in self.nodes.items() if not p.is_relative_to(root)}


def _plan() -> ContainerWorkspacePlan:
    return ContainerWorkspacePlan(
        service="agent-workflow",
        mounts=(
            ContainerMount(_PUBLIC, "/workspace", MountMode.READ_ONLY),
            ContainerMount(_OUTPUT, "/workspace/output", MountMode.READ_WRITE),
            ContainerMount(_OUTPUT / "input", "/workspace/output/input", MountMode.READ_ONLY),
            ContainerMount(_HOME, "/run/agent_home", MountMode.READ_WRITE),
            ContainerMount(_RUN, "/run", MountMode.READ_WRITE),
        ),
        working_dir="/workspace",
        environment={"HOME": "/run/agent_home"},
    )


@pytest.fixture
def memory(monkeypatch: pytest.MonkeyPatch) -> _Memory:
    # All staging, content, subprocess, archive, cleanup and sync boundaries are denied.
    for name in ("mkdir", "read_text", "read_bytes", "write_text", "write_bytes", "touch"):
        monkeypatch.setattr(Path, name, _forbidden)
    for module, names in (
        (tempfile, ("mkdtemp", "TemporaryDirectory")),
        (shutil, ("copytree", "copy2", "rmtree")),
        (subprocess, ("run", "Popen")),
        (os, ("fsync", "fdatasync", "sync", "read", "write")),
        (runtime, ("package_workspace",)),
    ):
        for name in names:
            monkeypatch.setattr(module, name, _forbidden)
    fs = _Memory()
    for path in (Path("/"), Path("/virtual"), _CONTROL, _HOME, _PUBLIC, _OUTPUT, _RUN):
        fs.add(path, stat.S_IFDIR | 0o700)
    fs.add(_PRIVATE, stat.S_IFDIR | 0o755, uid=0)
    fs.add(_PRIVATE / "cache", stat.S_IFREG | 0o600, uid=0)
    fs.add(_HOME / "credential", stat.S_IFREG | 0o600)
    fs.add(_HOME / "link", stat.S_IFLNK | 0o777, uid=0)
    fs.add(_OUTPUT / "input", stat.S_IFREG | 0o444, uid=0)
    fs.add(_OUTPUT / "result", stat.S_IFREG | 0o640, uid=0)
    fs.add(_RUN / "tools", stat.S_IFDIR | 0o555, uid=0)
    fs.add(_RUN / "tools" / "trusted", stat.S_IFREG | 0o4555, uid=0)
    monkeypatch.setattr(Path, "resolve", lambda path, **kwargs: path)
    monkeypatch.setattr(Path, "exists", lambda path: path in fs.nodes)
    monkeypatch.setattr(
        Path, "is_symlink", lambda path: path in fs.nodes and stat.S_ISLNK(fs.nodes[path].mode)
    )
    monkeypatch.setattr(
        Path, "is_dir", lambda path: path in fs.nodes and stat.S_ISDIR(fs.nodes[path].mode)
    )
    monkeypatch.setattr(
        Path, "is_file", lambda path: path in fs.nodes and stat.S_ISREG(fs.nodes[path].mode)
    )
    monkeypatch.setattr(Path, "stat", lambda path, **kwargs: fs.nodes[path].metadata())
    monkeypatch.setattr(Path, "chmod", lambda path, mode, **kwargs: fs.chmod(path, mode, **kwargs))
    monkeypatch.setattr(Path, "touch", lambda path: fs.add(path, stat.S_IFREG | 0o600))
    monkeypatch.setattr(os, "open", fs.open)
    monkeypatch.setattr(os, "close", lambda fd: fs.descriptors.pop(fd))
    monkeypatch.setattr(os, "fstat", lambda fd: fs.nodes[fs.descriptors[fd]].metadata())
    monkeypatch.setattr(os, "fchown", fs.fchown)
    monkeypatch.setattr(os, "fchmod", fs.fchmod)
    monkeypatch.setattr(os, "scandir", fs.scandir)
    monkeypatch.setattr(os, "walk", fs.walk)
    monkeypatch.setattr(
        os,
        "stat",
        lambda name, *, dir_fd, follow_symlinks: fs.nodes[fs.descriptors[dir_fd] / name].metadata(),
    )
    monkeypatch.setattr(os.path, "realpath", lambda path: str(path))
    monkeypatch.setattr(shutil, "rmtree", fs.remove_control)
    monkeypatch.setattr(ownership.time, "monotonic", lambda: 1.0)
    return fs


def _context() -> runtime.AgentSandboxContext:
    return runtime.AgentSandboxContext(
        docker_available=True,
        workspace_dir=_OUTPUT,
        task_dir=_PUBLIC,
        run_dir=_RUN,
        artifact_directory=Path("/virtual/artifacts"),
        compose_files=(),
        compose_project_name="fake",
        mount_manifest_path=_RUN / "mounts",
        agent_container_name="fake",
        container_cleanup_label="fake",
        command="fake",
        env={},
        notes=(),
        control_dir=_CONTROL,
        ownership_handoff_command=("fake-handoff",),
        ownership_handoff_validation_command=("fake-validate",),
        ownership_handoff_complete_path=_CONTROL / "complete",
    )


def _lifecycle(
    monkeypatch: pytest.MonkeyPatch,
    fs: _Memory,
    *,
    exit_code: int = 0,
) -> runtime.CandidateLifecycleOutcome[str]:
    selected, protected = runtime._ownership_handoff_targets(_plan())
    roots = tuple(mount.source for mount in selected)

    def stopped(*args: Any) -> None:
        fs.events.append("confirmed-stopped")

    def process(command: tuple[str, ...], **kwargs: Any) -> Any:
        assert fs.events[0] == "confirmed-stopped"
        if command == ("fake-validate",):
            fs.events.append("validated")
            ownership.validate_handoff_sources(roots, protected=protected)
        elif command == ("fake-handoff",):
            assert fs.events[-1] == "validated"
            ownership.handoff_ownership(roots, exclusions=protected, uid=_HOST_UID, gid=_HOST_GID)
            fs.events.append("transferred")
            assert fs.nodes[_PRIVATE].mode == stat.S_IFDIR | 0o755
            assert fs.nodes[_HOME / "credential"].mode == stat.S_IFREG | 0o600
        else:
            raise AssertionError(command)
        return SimpleNamespace(returncode=0)

    def package(*args: Any) -> None:
        assert _CONTROL not in fs.nodes
        assert fs.events[-1] == "control-cleanup"
        fs.events.append("packaged")

    monkeypatch.setattr(runtime, "stop_agent_sandbox_containers", stopped)
    monkeypatch.setattr(
        runtime,
        "cleanup_agent_sandbox_context",
        lambda context: fs.events.append("container-cleanup"),
    )
    monkeypatch.setattr(runtime.subprocess, "run", process)
    monkeypatch.setattr(runtime, "package_workspace", package)
    return runtime.run_candidate_lifecycle(
        prepare=_context,
        execute=lambda context: runtime.CandidateExecution("payload", True, exit_code, False, None),
        manifest=SimpleNamespace(),
        archive_path=Path("/virtual/result.tar.gz"),
    )


# A normal root controller's private runtime directories are transferred before host cleanup.
@pytest.mark.integration
def test_normal_collection_after_private_runtime_metadata_handoff(
    monkeypatch: pytest.MonkeyPatch,
    memory: _Memory,
) -> None:
    protected_before = {
        p: (n.uid, n.mode)
        for p, n in memory.nodes.items()
        if p == _PUBLIC or p == _OUTPUT / "input" or p.is_relative_to(_RUN / "tools")
    }
    link = memory.nodes[_HOME / "link"]
    private_file = memory.nodes[_PRIVATE / "cache"]
    outcome = _lifecycle(monkeypatch, memory)
    assert outcome.failure_reason is None
    assert outcome.agent_failed is False
    assert memory.events == [
        "confirmed-stopped",
        "validated",
        "transferred",
        "container-cleanup",
        "control-cleanup",
        "packaged",
    ]
    assert private_file.uid == _HOST_UID
    assert private_file.mode == stat.S_IFREG | 0o600
    assert link.uid == 0
    assert not any(path.name in {"cache", "credential", "link"} for path in memory.chmods)
    assert {
        p: (memory.nodes[p].uid, memory.nodes[p].mode) for p in protected_before
    } == protected_before
    assert not memory.descriptors


# Failed container termination never grants authority to handoff, private cleanup or packaging.
@pytest.mark.integration
def test_termination_failure_preserves_private_control(
    monkeypatch: pytest.MonkeyPatch,
    memory: _Memory,
) -> None:
    def reject(*args: Any) -> None:
        raise runtime.CandidateTerminationError("still active")

    monkeypatch.setattr(runtime, "stop_agent_sandbox_containers", reject)
    monkeypatch.setattr(runtime, "cleanup_agent_sandbox_context", lambda context: None)
    monkeypatch.setattr(runtime, "handoff_agent_sandbox_ownership", _forbidden)
    outcome = runtime.run_candidate_lifecycle(
        prepare=_context,
        execute=lambda context: runtime.CandidateExecution("ok", True, 0, False, None),
        manifest=SimpleNamespace(),
        archive_path=Path("/virtual/result.tar.gz"),
    )
    assert outcome.failure_reason == "still active"
    assert outcome.agent_failed is True
    assert _PRIVATE in memory.nodes


# Failed handoff remains an infrastructure failure and leaves private control available.
@pytest.mark.integration
def test_ownership_failure_does_not_cleanup_or_package(
    monkeypatch: pytest.MonkeyPatch,
    memory: _Memory,
) -> None:
    def reject(*args: Any, **kwargs: Any) -> Any:
        raise subprocess.CalledProcessError(1, "handoff")

    monkeypatch.setattr(runtime, "stop_agent_sandbox_containers", lambda *args: None)
    monkeypatch.setattr(runtime, "cleanup_agent_sandbox_context", lambda context: None)
    monkeypatch.setattr(runtime.subprocess, "run", reject)
    outcome = runtime.run_candidate_lifecycle(
        prepare=_context,
        execute=lambda context: runtime.CandidateExecution("ok", True, 0, False, None),
        manifest=SimpleNamespace(),
        archive_path=Path("/virtual/result.tar.gz"),
    )
    assert outcome.failure_reason == "candidate output ownership handoff failed"
    assert outcome.agent_failed is False
    assert _PRIVATE in memory.nodes


# Host cleanup errors continue to block packaging instead of being ignored.
@pytest.mark.integration
def test_cleanup_failure_blocks_packaging(
    monkeypatch: pytest.MonkeyPatch,
    memory: _Memory,
) -> None:
    def reject(path: Path) -> None:
        raise PermissionError("control deletion denied")

    monkeypatch.setattr(shutil, "rmtree", reject)
    outcome = _lifecycle(monkeypatch, memory)
    assert outcome.failure_reason == "host sandbox control cleanup failed: control deletion denied"
    assert outcome.agent_failed is False
    assert "packaged" not in memory.events
    assert _PRIVATE in memory.nodes


# A failed candidate exit remains a candidate error after successful host cleanup.
@pytest.mark.integration
def test_abnormal_exit_never_packages(
    monkeypatch: pytest.MonkeyPatch,
    memory: _Memory,
) -> None:
    outcome = _lifecycle(monkeypatch, memory, exit_code=1)
    assert outcome.failure_reason is not None
    assert outcome.termination_detail is not None
    assert outcome.agent_failed is True
    assert "packaged" not in memory.events
    assert _CONTROL not in memory.nodes


# Private-home source validation rejects an alias of a read-only public input.
def test_home_source_alias_is_rejected(memory: _Memory) -> None:
    memory.nodes[_HOME].inode = memory.nodes[_PUBLIC].inode
    with pytest.raises(ValueError, match="aliases a protected"):
        ownership.validate_handoff_sources((_HOME,), protected=(_PUBLIC,))


# A substituted symlink in the private-home source path is rejected without following it.
def test_home_source_symlink_is_rejected(memory: _Memory) -> None:
    memory.nodes[_HOME].mode = stat.S_IFLNK | 0o777
    with pytest.raises(OSError, match="refuse symlink"):
        ownership.validate_handoff_sources((_HOME,), protected=(_PUBLIC,))
    assert not memory.descriptors


# Private descendants cannot use hardlinks to change unrelated file ownership.
def test_private_hardlink_is_rejected(memory: _Memory) -> None:
    memory.nodes[_PRIVATE / "cache"].links = 2
    with pytest.raises(ValueError, match="hardlinked"):
        ownership.handoff_ownership((_HOME,), exclusions=(), uid=_HOST_UID, gid=_HOST_GID)
    assert memory.nodes[_PRIVATE / "cache"].uid == 0
    assert not memory.descriptors


# Private traversal remains subject to the existing metadata entry bound.
def test_private_handoff_budget_is_enforced(
    monkeypatch: pytest.MonkeyPatch,
    memory: _Memory,
) -> None:
    monkeypatch.setattr(ownership, "_MAX_ENTRIES", 1)
    with pytest.raises(TimeoutError, match="exceeded its bounds"):
        ownership.handoff_ownership((_HOME,), exclusions=(), uid=_HOST_UID, gid=_HOST_GID)
    assert memory.nodes[_PRIVATE].uid == 0
    assert not memory.descriptors
