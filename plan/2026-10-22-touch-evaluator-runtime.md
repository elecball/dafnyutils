# Restore the trusted touch evaluator runtime

Status: done
Date: 2026-10-22

## Objective and acceptance

Operator maintenance on baseline `16f2778`: restore the trusted native date parser
beside the evaluator DLL before checks. The canonical configuration name selects
touch even when its public task identifier is an alias. Existing blocks skip
preparation; other utilities do nothing. Build, missing/unusable helper and staging
failures become explicit infrastructure blocks and notes through the existing
runner contract. No candidate rejection or scoring change is permitted.

Parent plan: [integration repair](../../plan/2026-10-22-touch-evaluator-runtime.md).
No new dependencies or approvals are needed. Do not change specifications,
implementation/proof sources, datasets, oracles, public resources/build scripts,
mounts or images. Do not build native tools, replay tasks, call providers, modify
the running weekly experiment, stage Git files or commit in this implementation.

## Inspected evidence and design

`benchmarks.make_tasks._build` prepares touch's parser with the existing Make
target; generated evaluation builds only compile Dafny. IOExtern's adjacent-file
lookup and trusted-repository fallback can conceal omitted deployment during
parity. Fuzzer deployment explicitly requires `touch_time_parser` beside the DLL.
The helper is trusted external runtime packaging, not candidate code or a task
resource. The shared `_evaluate_captured` route covers archive evaluation with
new or caller-managed evaluators and each task of multi-task submissions.

Prepare on the trusted host using the existing `build-time-parser` Make target,
letting Make check freshness on each preparation. Keep `BUILD_DIR` in the trusted
repository and override `TOUCH_TIME_PARSER` with the exact isolated evaluator DLL
sibling. Validate that output with lstat and executable access. This avoids
concurrent linkers sharing an output; no copy or new lock is needed. Do not copy
trees or expose GNU inputs to candidates.

## Change table

| Exact files / symbols | Change and necessity | Validation |
| --- | --- | --- |
| `src/evaluation/submission/workspace.py` | Documented runtime preparer and narrow infrastructure error; build existing trusted target directly at the isolated evaluator sibling, reject symlink/nonregular/nonexecutable helper | Fake build and stat/access; normal, no-op, separate target roots and individual failures |
| `src/evaluation/submission/api.py::_evaluate_captured` | Prepare canonical utility before checks when runnable; pass infrastructure failure as existing runner block and add note | Fake runner/persistence and preparation; regression before source repair, aliases, ordering and block precedence |
| `tests/evaluation/test_evaluator_runtime.py` | In-memory behavioral regression and boundary checks | Default-deny subprocess, filesystem mutation and logging; no temporary directories or real native calls |
| This plan, `plan/INDEX.md`, `wiki/evaluator-runtime.md`, `wiki/INDEX.md` | Record durable ownership, deployment and verification limits | Markdown-only trees and focused diff review |

## Validation and risks

From `/workspace/dafnyutils`, run `python3 -m pytest -c pytest-dev.ini -q
tests/evaluation/test_evaluator_runtime.py` before and after the source repair,
then `ruff format --check src/evaluation/submission/workspace.py
src/evaluation/submission/api.py tests/evaluation/test_evaluator_runtime.py` and
`ruff check` on the same files. Tests must fake every transitive write/process
boundary and fail closed if an unexpected path executes. Parent owns broad unit,
static/final gates and fresh independent verification. No benchmark tests or
Dafny proofs are needed for this Python packaging change.

Current Make/C/.NET/Dafny/Docker/tmux commands and trusted GNU library/helper
artifacts exist. Fake validation establishes orchestration, not successful native
compilation, live differential behavior or proof success. Host-produced helper
must remain compatible with the evaluator's existing Linux runtime, as in normal
benchmark builds. Build/staging failure must stop checks explicitly.

Durable knowledge: [evaluator runtime dependencies](../wiki/evaluator-runtime.md).

## Progress

Ready plan saved before implementation. Baseline dirty `coreutils`, `dafny` and
untracked note are unrelated and will be preserved. No restricted candidate,
hidden oracle or solution material was read.

Pre-fix regression (working tree based on `16f2778`): from the owner root,
`PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -c pytest-dev.ini -q -p no:cacheprovider
tests/evaluation/test_evaluator_runtime.py` produced two expected failures in
0.29s. Both shared evaluator argument variants ran checks without the required
preparation event. All runner, persistence, filesystem mutation and subprocess
boundaries were faked or denied; no native build or task execution occurred.

Concurrency finding: `build-time-parser` serializes GNU preparation through the
existing coreutils lock, but compiles its helper after that lock is released.
Preparing a shared helper and copying it can race another linker in concurrent
evaluations. Parent approved and updated its plan before source edits: preserve trusted
`BUILD_DIR`, override the existing `TOUCH_TIME_PARSER` Make variable with the
isolated evaluator sibling, and validate that exact output. This removes shared
helper compilation and the redundant copy without changing candidate views.

Implementation is complete in the planned source/test files. The helper uses the
canonical configuration name, preserves existing block precedence, anchors
relative target paths before Make changes directories, and validates the isolated
regular executable after Make. Expected failures feed the existing runner block
and an infrastructure note without changing candidate capture or score logic.
No public build scripts, task resources, mounts, images or benchmark layers were
edited. The related wiki page and index now record the durable deployment rule.

Focused validation from `/workspace/dafnyutils`, working tree on `16f2778`:
`python3 --version` reports Python 3.12.3; `ruff --version` reports Ruff 0.15.12.

- `PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -c pytest-dev.ini -q -p no:cacheprovider tests/evaluation/test_evaluator_runtime.py`: 17 passed in 0.23s after implementation; final pass after scoped formatting: 17 passed in 0.31s. These cases deny native subprocesses and filesystem mutation, and fake runner/persistence/metadata boundaries. Distinct-root cases establish isolated output arguments, not actual concurrent execution.
- Initial `ruff format --check` and `ruff check` on the three changed Python files reported formatting/line-length issues. Ran `ruff format src/evaluation/submission/workspace.py src/evaluation/submission/api.py tests/evaluation/test_evaluator_runtime.py`; repeated checks report three files formatted and all checks passed.
- `git diff --check`: passed. Recursive `find plan wiki -type f ! -name '*.md' -print`: no violations. All four owner plan/wiki record paths are ignored by Git; parent owns exact-path staging, with no unrelated ignored paths to be added.

At implementation handoff, parent-owned full owner unit/static/final checks,
typing, root compatibility and fresh independent verification remained; their
completed outcomes follow below. Parent owns focused commits. No Git staging/commit, native build,
Docker/provider/task replay or running-experiment change was performed here.

## Parent and independent validation

Parent ran supported `make test-unit`: 130 passed, 16 integrations deselected in
4.07s. Repository-wide `ruff format --check src tests` and `ruff check src tests`
passed all 86 files. The root in-memory protocol roundtrip passed one case in
0.13s with the task scratch's ordinary Cosyn alias and current root/owner sources.
Final owner `make test-integration` passed all 16 cases with 130 units deselected
in 82.89s. Its selected paths were audited for bounded analysis/fingerprinting and
subprocess I/O, with no native build/proof or temporary-directory/sync workload
identified. Native analysis acceptance does not establish benchmark proof or
generated helper runtime success.

Default `pyright src` and `pyright --pythonpath /usr/bin/python3 src` each report
11 missing-dependency errors and 6 warnings. Full-source mapping at
`/workspace/tmp/touch-evaluator-runtime-20261022/validation/pyrightconfig.json`
resolves installed dependencies without suppressing diagnostics and checks all
67 source files. Its one error is the unchanged baseline `_compose_yaml` return
type at `evaluation/agent/runtime.py:834` (blob
`3d50a8a04d674fc118c51cd63398be13f86693ee`); the two changed modules pass the same
unsuppressed mapping with zero errors/warnings. Full-source typing is not green.

Fresh independent verification passed the 17 focused cases and scoped Ruff,
reviewed trusted input/output selection, every shared evaluation route, narrow
failure blocks and fake boundaries, then reproduced the baseline typing limit
and clean affected-source result. Report:
`/workspace/tmp/touch-evaluator-runtime-20261022/verification/report.md` (SHA-256
`8c350463214f1faaa23d88a2c1b420e4dbef6f8c41a70953d32902f1bd30ff92`).

These record paths were ignored and untracked in the baseline. The focused
commit will track this plan, this task's index entry and the new wiki page/index.
The pre-existing unrelated local plan index entries remain in the working tree
and are excluded from the staged new index to avoid publishing dangling links.

Implementation, required local validation and independent acceptance are complete.
No source/test changes followed the accepted hashes. Python 3.12.3, Ruff 0.15.12
and Pyright 1.1.414 were used; owner native gitlink remains recorded at `10dca3b`
while unrelated working native HEAD is `df5816d`. No nested gitlink is included
in this repair. Parent owns focused owner/root commits and records their IDs in
the integration plan. The original weekly inputs and results remain unchanged;
no provider call, native/helper build, Docker/image operation or task replay ran.
