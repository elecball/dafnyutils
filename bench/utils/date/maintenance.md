# Date contributor-maintenance record

This is contributor-maintenance memory, not an authorized evaluated-run input.
It is not a declared task resource. An evaluated run may read it only when its
protocol explicitly authorizes this record; the title alone grants no access.
The authoritative observable scope is [date.md](date.md).

The acceptance results and binary fingerprints below describe the earlier
four-utility source snapshot. Subsequent shared stdin-layering maintenance is
recorded in `plan/2026-10-23-stream-read-layering.md`. Date does not call the
stdin APIs, and the user explicitly deferred further time-related expansion.

## Scope, implementation and trust

This repository-maintenance contribution started from
`37b35bac3d4cf84cdd8ea02eb3279e8aa49307df` in the detached worktree
`/workspace/tmp/coreutils-four-20261022/date`. The required reference-file,
UTC and three explicit formats remain supported. The expanded and deferred
behavior is recorded in the public scope document; this contribution does not
claim full GNU date equivalence.

`DateModel` contains independent Gregorian-calendar and positional-decimal
relations. `DateSpec` constrains selected timestamps, civil/ISO-week fields,
format/output partitions, exact diagnostics, stream observations and status.
Fixed user text lives in Spec. The direct `RunCore` postcondition is
`DateSpec.Spec`. Calendar conversion and numeric formatting are proved locally
in candidate-editable Calendar/Format targets. The year search has at most 399
iterations for an arbitrary integer epoch.

Trusted operations are the existing IO streams, errno/argument quoting, file
metadata, whole-second clock and gnulib `ParseDate` contracts. Conditional
filename quoting reuses `StringEscaping.SpecQuoteFBytes`. The native
`touch_time_parser` companion uses the canonical shared source and pinned GNU
libraries. No native calendar conversion, formatter or utility-answer wrapper,
assumption, trust annotation or verification skip was added. The fixed CLI
parser remains the repository's protocol boundary.

The date Makefile exposes `build-time-parser` with the existing
`TOUCH_TIME_PARSER` output override. It requires prebuilt GNU configuration and
archives and delegates the canonical companion build; it does not rebuild the
shared GNU tree. The root integration agent owns isolated evaluator deployment
and the unchanged mandatory contribution gate.

Named source scenarios come from `tests/date/reference.sh`, `tests/date/date.pl`
and `tests/date/percent-percent.sh`, plus help/version/write-error behavior.
Runtime tests compare complete stdout, stderr and status with pinned GNU.
Existing read-only files provide reference fixtures; no Python temporary-directory
fixtures or toolchain-tree reads/hashes were added. Fully specified epochs cover
negative fractions, leap/century boundaries, negative and extended years,
ISO week transitions and signed time_t limits. Generator guard tests use only
in-memory data. The fixed regression corpus retains each repaired strict
comparison trigger.

## Environment and reproducibility

Evidence is available locally under
[/workspace/tmp/coreutils-four-20261022/evidence/date/](/workspace/tmp/coreutils-four-20261022/evidence/date/).
It is outside plan/wiki. Scripts beside the logs record exact commands, working
directories, settings and exit statuses. Experiments ran in named tmux sessions;
GNU build artifacts were reused read-only by this agent.

The environment used Python 3.12.3, .NET SDK 8.0.131, Rust 1.94.0, Ruff 0.15.12,
tmux 3.4, and Dafny
`4.11.1+5fa47c6e949dad736db25e02b5edad95d0b0be1a`, with
`PYTHONPATH=$PWD/src` and `DOTNET_PROCESSOR_COUNT=2`. GNU coreutils was pinned to
`2cf491412c199e2211880ec3f4ba387026638a33` (`9.10.13-2cf49`). Differential
campaigns use image
`sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76`.

`source-freeze-02.sha256` identifies the frozen executable/proof/generator state;
its manifest SHA-256 is
`ba14e57aa6c3b2dd6b88b953e80aaa0eb7b2a4b43f4864c826d5c822914353d9`.
A later test-fixture-only cleanup requires prebuilt candidate/GNU artifacts
instead of conditionally invoking build helpers. Only `Tests.py` differs in
`source-freeze-02-test-only-01.sha256`, whose manifest SHA-256 is
`6bc7ec3c2f16a0485a1bd5baadd271fb4e0306186f119a536f415d0bb6dedd9a`.
`binaries-freeze-02.sha256` pins the unchanged candidate DLL, native parser
companion and GNU date binary. This maintenance record is excluded from the
source manifest because it receives evidence-only updates after source freeze.

## Verification and runtime results

Proof success and runtime parity are recorded separately:

- Supported `make -C bench/utils/date verify`, in `verify-project-02.log`, passed
  all 34 declarations and 578 obligations with exit 0. This snapshot precedes
  the later empty-precision and locale-composite corrections; its source
  manifest and the earlier failed full verification are preserved.
- After those corrections, the eight permanent marked proof cases all passed
  (`proof-tests-locale-fixed.log`, exit 0). They cover Model, Schema, Spec,
  Calendar, Format, Core, Proof and entry. Focused isolated checks additionally
  verified `Core.EarlyPlan` (19 obligations), `Spec.Meaning` (44) and
  `Format.Render` (86), all exit 0. Standard expected library warnings are
  filtered by the canonical verifier options; there are no task proof warnings.
- Supported build and utility runtime test targets both passed on the frozen
  source (`build-locale-fixed.log`, `test-locale-fixed.log`, exits 0): 76 runtime
  scenarios passed, with eight proof cases selected separately. After the
  prebuilt-artifact fixture cleanup, the supported runtime target again passed
  all 76 cases (`test-prebuilt-01.log`, exit 0), and Ruff check/format passed.
  Retained parity helpers call only native execution; there is no transitive
  build, fixture-copy or temporary-directory path and no autouse/conftest setup.
  The standalone worktree reports the unregistered integration-marker warning;
  the combined integration configuration registers that execution-weight marker.
- Six persistent source-backed strict regression expectations passed
  (`regressions-locale-fixed.log`, exit 0). Replaying the original saved mismatch
  returned `replay_not_reproduced` (`replay-locale-fixed.log`); its exit 2 is the
  replay tool's result for a mismatch that no longer reproduces, not a passing
  process exit.
- Four in-memory Rust generator tests and the registered-pattern allowlist test
  passed. Ruff checks, Ruff format checks and Rust format checks passed. The
  unrelated full Rust development suite was not run because it includes
  filesystem-heavy fixture lifecycles outside this contribution's checks.
- Profile generation and actual task-workspace inspection both passed on freeze
  02. The union of resources, copied/generated files and read-only paths excludes
  this record and `Tests.py`. Calendar/Format are editable generated stubs with
  their contributed implementations removed. Logs:
  `profile-freeze-02.log` and `workspace-freeze-02.log` (exits 0).
- Recursive inspection of this worktree's plan/wiki found no non-Markdown files;
  `git diff --check` passed. No commits were created.

The root agent's unchanged mandatory `make check TASK=date` against the
combined integration tree passed with exit 0: 34 declarations, 578 obligations,
zero failures and all eight marked proof cases passed. Evidence:
[/workspace/tmp/coreutils-four-20261022/evidence/integration/date-check-v2.log](/workspace/tmp/coreutils-four-20261022/evidence/integration/date-check-v2.log)
and its `.status` file. The integrated supported runtime rerun after the
prebuilt-artifact fixture cleanup also passed all 76 scenarios, with eight proof
cases deselected, exit 0. Evidence:
[/workspace/tmp/coreutils-four-20261022/evidence/integration/date-runtime-final.log](/workspace/tmp/coreutils-four-20261022/evidence/integration/date-runtime-final.log)
and its `.status` file. The root's integrated shared parser-branch consolidation
uses equivalent build arguments. An obsolete gate against the previous snapshot
was cancelled and retained as superseded, not reported as a pass.

## Differential campaigns and preserved failures

The final command is `python3 tools/coreutils_fuzzer/run.py fuzz date --seeds
1,7,19 --iterations 1000 --metrics-out
/workspace/tmp/coreutils-four-20261022/evidence/date/fuzz-freeze-02.json`.
It runs in tmux session `date-fuzz-freeze-02`; the exact shell command is in
`fuzz-freeze-02.sh`. Comparisons include complete stderr and status, with no time
stripping or tolerance. Reference-file timestamps are controlled and parsed
inputs are deterministic. This is not current-time coverage.

Freeze-02 seeds 1, 7 and 19 each requested, submitted and completed 1,000
iterations: 3,000 exact matches in total, zero mismatches, timeouts, other errors,
abandoned or unstarted cases. All three metrics record `ignore_stderr=false`.
The wrapper exited 0. Elapsed times were 221.07, 222.86 and 212.27 seconds.
Per-seed metrics are `fuzz-freeze-02-seed1.json`,
`fuzz-freeze-02-seed7.json` and `fuzz-freeze-02-seed19.json`.

The raw metrics retain pre-existing generic labels
`filesystem_time_policy=unsupported` and a blanket time-behavior limitation.
Those annotations do not describe date's controlled-reference execution path:
`execute_case_in_work_dir` reads date's `controlled_fixture_times=true`, passes it
to `stage_iteration_dirs`, and the existing fixture controller sets atime to
4102444800, mtime to 2000000000 and nanoseconds to zero. The runner preserves or
restores exact reference prestate before DUT execution. Explicit epochs and
reference comparisons are therefore deterministic; current-clock/asynchronous
time behavior remains untested. Generic metadata and raw evidence were not
rewritten to hide this distinction.

Useful failed approaches and real defects remain available:

- `calendar-01` through `calendar-03` preserve initial proof failures/timeouts.
  Local proof guidance and smaller arithmetic obligations resolved them without
  increasing the time limit. `calendar-04.log` passed 85 obligations. The first
  supported full-project attempt later timed out at an isolated era boundary;
  explicit constant-division facts resolved it for `verify-project-02` without
  changing proof scope.
- `test-01.log` preserves four exact diagnostic failures (64 runtime passes).
  Conditional filename quoting and complete ISO/RFC option diagnostics fixed
  those triggers. `precision-probe-01.log` exposed GNU's ambiguous-argument
  classification for empty ISO/RFC precision; both now have fixed regressions.
- The first final campaign stopped with a real seed-1/iteration-264 mismatch:
  264 matches and one mismatch, with the remaining iterations not started.
  The original bundle is retained at
  `mismatch-bundles/date-seed1-iter264`; the campaign log, metrics and source
  fingerprint remain unchanged. GNU/Linux glibc C-locale `%x` uses a nonnegative
  short-year remainder while gnulib `%D`/`%y` use short-year magnitude for
  negative years; `%c` uses an unpadded signed full year. Source inspection and
  deterministic small/negative-year probes established these distinct rules.
  The local mathematical specification now preserves each rule, with the exact
  mismatch and five additional year variants retained in permanent runtime
  tests. Negative inputs and the accepted plain-directive grammar were retained.
- An early focused proof script omitted the canonical expected-library-warning
  option and exited 2 despite proving its obligations. A permanent Spec proof
  case then exposed two task indentation warnings. Parenthesized logical
  clauses removed those warnings without changing meaning or removing the test;
  all eight permanent proof cases subsequently passed.

The date contribution's required checks have finished. No date blocker remains;
the next action is the root agent's integration review and final report. Deferred
valid GNU format modifiers and `--file`, plus the explicitly documented
system-observation limits, remain outside this contribution's implemented/proved
scope.

## Final merged-checkout acceptance

The worker results above are preserved. Parent integration additionally ran the
complete final campaigns from `/workspace/dafnyutils`, using the merged shared
core, native adapter and all-four generator registry. This removes the worker
source-state difference caused by the additive bounded-read API. Utility
algorithms, specifications and proofs are unchanged. The unchanged mandatory
`make check TASK=date` passed in the integration worktree
(`date-check-v2.log/status`, exit 0, 578 obligations, zero failed).

The final original-checkout build and runtime targets passed. Campaigns in tmux
`four-utils-main-fuzz-date` each completed seeds `1,7,19` with 1,000 exact
generated matches, no mismatches/timeouts/errors, and stderr included. Metrics
are `evidence/integration/main-fuzz-date-seed{1,7,19}.json`;
`main-fuzz-date-sources.sha256` and `main-fuzz-date-source-check.status`
bind the unchanged source and artifact across the run. These final merged-tree
campaigns are the canonical final integration evidence. Option/semantic coverage
annotations are not a claim of exhaustive input coverage. Existing domain and
time-observation limitations above still apply.

Final DLL: `/workspace/dafnyutils/_build/bench/date_bench.dll`, 1208832 bytes,
SHA-256 `d23c23f977f8d2917a2d3bd227437ceadee5a3225a64ad4159d9802b2e45e20e`. Artifacts remain locally available under
`/workspace/tmp/coreutils-four-20261022/evidence/integration/`; they are not
candidate inputs. No commits were created. The complete final campaign stdout
follows verbatim, including its command and metadata.

```text
UTC: 2026-10-22T17:38:14.537028+00:00
CWD: /workspace/dafnyutils
CMD: python3 tools/coreutils_fuzzer/run.py fuzz date --seeds 1,7,19 --iterations 1000 --metrics-out /workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-date.json
Artifact SHA256: d23c23f977f8d2917a2d3bd227437ceadee5a3225a64ad4159d9802b2e45e20e
All four tasks use the final merged core, native adapter and generator registry.
selected utilities: date
==> utility: date
    seed: 1

=== Coreutils fuzz campaign ===
Configuration
  Utility    : date
  Seed       : 1
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/date" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/date_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-date-seed1.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 14 (discovered)
  Outside scope: --debug, --file, --resolution, --set, -04, -0400, -f, -s
Coverage
  Option coverage: singles 13/14 (92.9%), pairs 12/91 (13.2%)
  Semantic coverage: buckets 19/27 (70.4%), extra=0, missing: arg:empty, fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, stdin:consumed
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 214.40s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
    seed: 7

=== Coreutils fuzz campaign ===
Configuration
  Utility    : date
  Seed       : 7
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/date" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/date_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-date-seed7.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 14 (discovered)
  Outside scope: --debug, --file, --resolution, --set, -04, -0400, -f, -s
Coverage
  Option coverage: singles 13/14 (92.9%), pairs 12/91 (13.2%)
  Semantic coverage: buckets 18/27 (66.7%), extra=0, missing: arg:empty, fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, operand:dash, stdin:consumed
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 210.40s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
    seed: 19

=== Coreutils fuzz campaign ===
Configuration
  Utility    : date
  Seed       : 19
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/date" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/date_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-date-seed19.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 14 (discovered)
  Outside scope: --debug, --file, --resolution, --set, -04, -0400, -f, -s
Coverage
  Option coverage: singles 13/14 (92.9%), pairs 12/91 (13.2%)
  Semantic coverage: buckets 18/27 (66.7%), extra=0, missing: arg:empty, fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, operand:dash, stdin:consumed
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 215.85s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
```
