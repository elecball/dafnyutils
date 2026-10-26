# join maintenance validation

This is repository-maintenance evidence, not an evaluated-run memory snapshot.
The candidate contract is `join.md` and its analyzed Dafny specification closure.
The generated profile and workspace seed paths exclude this document, `Tests.py`
and the input fixture directory. No reference answers are stored with the inputs.

The acceptance results and binary fingerprints below describe the earlier
four-utility source snapshot. Subsequent shared stdin-layering maintenance and
affected join regression results are recorded in
`plan/2026-10-23-stream-read-layering.md`; those later results must be checked
before treating a new shared-API rebuild as validated.

## Source and execution environment

The isolated worktree is `/workspace/tmp/coreutils-four-20261022/join`, based on
`37b35bac3d4cf84cdd8ea02eb3279e8aa49307df`. The inspected, prebuilt GNU checkout
is `2cf491412c199e2211880ec3f4ba387026638a33`. No commit was created and no shared
core contract, runtime, evaluator or scoring source was changed by join.

The frozen source manifest is
`/workspace/tmp/coreutils-four-20261022/evidence/join/frozen-v2-source.sha256`:
137 files, including every evaluator input, build/configuration source, generator,
registration change and fixed regression. Shared Rust registration is integrated
by the parent task with other utilities. Documentation is the only mutable handoff
content after this freeze.

Commands run from the worktree, with `PYTHONPATH=$PWD/src`,
`DOTNET_PROCESSOR_COUNT=2`, `PYTHONDONTWRITEBYTECODE=1`, and offline Cargo cache
access. Tools are Dafny benchmark 4.11.1+5fa47c6e949dad736db25e02b5edad95d0b0be1a,
Python 3.12.3, dotnet 8.0.131, Rust/Cargo 1.94.0, Ruff 0.15.12 and tmux 3.4.
GNU comparisons use C locale and UTC0. Fuzzing uses
`dafnyutils-coreutils-fuzzer:latest`, image
`sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76`.

All experiments run in named tmux sessions. Exact shell commands, unedited logs,
statuses, frozen source hashes, profiles, metrics and original mismatch bundles
are retained at `/workspace/tmp/coreutils-four-20261022/evidence/join/` on the
maintenance host. They are external scratch artifacts, not committed repository
resources or candidate inputs.

## Behavior and proof boundary

All GNU join options are modeled in C locale, including zero-terminated records,
NUL field separators, headers, output formats, case-insensitive matching, both
order policies and legacy argument forms. The scope is not reduced from the
minimum tracking row. `JoinBenchmarkItem.RunCore` directly ensures `JoinSpec.Spec`
and modifies only stdin, stdout and stderr regions.

The specification uses complete record/field partitions, maximal contiguous
matching rectangles, Cartesian-product row indices and observable read ranks.
The algorithms, partition/concatenation lemmas, quotient bounds, formatting and
warning/exit policy are task-local and proved. Existing IO, UTF-8, quoting, errno
and CLI contracts remain the native boundary. No assumptions, trust annotations,
verification skips, utility algorithms in trusted core or raised proof limits
were introduced.

Core methods and loops have termination metrics. CLI planning and process entry
retain the repository's existing `decreases *` interface, so the result does not
claim a separate termination proof for the complete process/CLI lifecycle.
The whole-input stream abstraction and environmental limits remain documented
in `join.md`; read errors and committed write prefixes remain explicit.

## Checks

- `make -C bench/utils/join build`: final-v2 exit 0. This supported target builds
  with `--no-verify`; it is not proof evidence.
- `make -C bench/utils/join test`: final-v2 exit 0, 117 strict GNU oracle cases
  passed, 8 proof cases deselected. Stderr remains exact for failures.
- `python3 tools/coreutils_fuzzer/run.py regression
  tools/fixtures/coreutils_fuzzer/v1/regressions/join.json`: final-v2 exit 0,
  all 8 expectations matched.
- `make -C bench/utils/join verify`: final-v2 exit 0, all 34 declarations,
  1,197 verification obligations and zero failures.
- `python3 -m pytest -q -n0 -p no:cacheprovider --import-mode=importlib
  -m dafny_verify bench/utils/join/Tests.py`: final-v2 exit 0, all 8 proof
  cases passed (117 runtime cases deselected), 382.96 seconds. Each module uses
  the fixed seed 42, isolated assertions and 30-second per-obligation limit.
- `python3 tools/coreutils_fuzzer/run.py fuzz join --seeds 1,7,19
  --iterations 1000 --metrics-out
  /workspace/tmp/coreutils-four-20261022/evidence/join/final-campaign-v2-metrics.json`:
  exit 0. Each seed requested, submitted, completed and matched 1,000 cases;
  no abandoned case, mismatch, timeout or other error. Elapsed times were
  214.22, 215.29 and 211.07 seconds. Stderr is included; no option scope or
  comparison check is weakened. Defaults remain 10 arguments, 12 fixture
  entries, 10-second target timeout and 250 shrink attempts.
- `python3 -m benchmarks validate join` and the final generated-profile/in-memory
  workspace audit: exit 0. No oracle fixtures, tests or maintenance record are
  candidate-visible. Ruff check/format, Cargo formatting, focused diff/whitespace
  checks and final metrics/status audit: exit 0.
- Recursive plan/wiki inspection covered the worktree and preserved read-only
  coreutils, Dafny and prebuilt GNU roots: 4 plan/wiki trees, zero non-Markdown
  files or symlinks, zero scan errors. All 137 frozen source/input hashes match.
- Parent-owned unchanged `make check TASK=join`: exit 0 in the integration tree;
  `join: checks passed`, full 1,197/0 verification result and all 8 marked proof
  cases passed (402.71 seconds for that proof-test tier). Evidence:
  `/workspace/tmp/coreutils-four-20261022/evidence/integration/join-check-v1.log`
  and `.status`. The GNU build prerequisite was already checked by the parent,
  with no native rebuild.

The worker DLL SHA-256 is
`cf910aa385605fd9371b1e4d940589fd53b7dfc23c2fd70e4cd68a73ce4cee6a`.
All three final metrics files record DUT fingerprint `fnv1a64:76e98d7ac1947c96`.
The discovered pool contains all 17 real GNU join option tokens plus synthetic
`-k` extracted from the help text's `sort` example; all 17 real tokens are covered.
The extra token was not filtered or used to reduce the input space.

The standalone strict `JoinSpec.dfy` probe completed 1,011 verified obligations,
0 errors and exit 0. The separately guided `JoinPlanCore.Reads` proof completed
153 verified obligations, 0 errors. These narrow proofs supplement the complete
supported and marked proof tiers; they do not replace them.

The in-memory Rust capability/generator registry tests passed 3 tests. The full
unrelated Cargo/Python development suites were not run: their filesystem-heavy
workloads are outside this focused contribution and the active development-test
restrictions. No benchmark gate or meaningful join check was disabled.

## Differential failures and proof diagnostics

Original failing campaigns and mismatch bundles remain unchanged:

- Seed 1, iteration 267: signed minimum `-9223372036854775808` was incorrectly
  accepted as field overflow. GNU rejects that exact value; only magnitudes
  beyond the signed range saturate.
- Seed 1, iteration 438: GNU preserves numeric `ERANGE` for repeated stdin
  operands. The task-local parser now tracks conversion errno reset/overflow,
  including output formats and legacy field setters.
- Seed 7, iteration 999: `-i -v 1 -v 2 left -`, left `c`, stdin backtick.
  GNU `memcasecmp` uppercases before comparison; lowercase folding changed
  punctuation order. ASCII lowercase now folds to uppercase, preserving all
  other binary bytes. This also governs order diagnostics.

Each defect has a fixed strict GNU/Dafny regression. No comparator normalization,
stderr suppression, option-pool filtering or expected-answer rewriting was used.
A contract audit also corrected exit status for unused late read failures:
only an encountered fatal read/order event, a close failure or an order warning
causes failure; disabled tail reads do not invent an observed error.

Early full proofs and standalone probes were retained as partial/failing evidence.
Variable-division bounds use a small proved quotient lemma. The final witness
construction separates its unchanged structural relation to avoid a 30-second
solver timeout. Two read-layout postcondition timeouts were repaired with local
initial-event facts. Strict probes exposed indentation warnings; explicit
parentheses removed them without allowing warnings. The long fixed help/version
text uses the existing UTF-8 encoder to avoid a large raw-byte-literal subtype
proof. Proof limits, scope and warning policy were preserved.

A previous corrected-runtime campaign completed all three seeds with 1,000
matches each and no mismatch, timeout or other error. Final-v2 reruns after the
last proof/encoding cleanup bind the acceptance evidence to the final DLL.

## Development-test and workspace audit

The 116 fixed input fixtures total 1,090 bytes, with a maximum file size of
30 bytes. They are evaluator-only public GNU-derived inputs, not expected
outputs. `Tests.py` only launches already-built GNU/.NET targets against these
read-only inputs, captured stdin and a rejected `/dev/full` write; it does not
build targets, create/copy/publish/clean workspaces or use temporary directories.
Transitive helpers and fixtures were inspected, including candidate execution
and failure-reporting paths. Each subprocess test is marked `integration`;
proof cases also retain `dafny_verify`. The base worker configuration reports
unregistered integration-marker warnings; the parent registers that marker in
its shared integration configuration without suppressing warnings.

Profile validation analyzes the final direct `RunCore ==> Spec` obligation and
its Dafny closure. In-memory workspace inspection checks copied, generated and
read-only paths, without materializing or copying a runtime tree. The evaluator
fixtures, oracle tests and this maintenance record must remain absent from all
candidate-visible path sets.

## Handoff

The parent owns the tracking-row/index/shared-document changes and the unchanged
integration gate. Import all task source/input files, `join.rs`, the module and
capability registrations, and the two fixed JSON files; no build artifacts or
submodule symlinks belong in that diff. The exact frozen file list is
`/workspace/tmp/coreutils-four-20261022/evidence/join/handoff-files.txt`.

Completion state: all required local final checks and the unchanged parent
integration gate passed. No join implementation or validation obligation remains.
The next concrete action is for the parent to import this doc-only maintenance
record and apply the shared tracking/index update; no commit was requested.
The parent explicitly requested preservation of the worktree, build artifacts and
read-only `coreutils`, `dafny` and `_build/coreutils` symlinks for reproducibility.
Their targets were not mutated. Focused Git review uses
`git -c diff.ignoreSubmodules=all status --short --ignore-submodules=all`.

## Final strict campaign stdout

The complete final campaign stdout follows, unedited and in order.

```text
selected utilities: join
==> utility: join
    seed: 1

=== Coreutils fuzz campaign ===
Configuration
  Utility    : join
  Seed       : 1
  Budget     : 1000 iterations
  Reference  : "/workspace/tmp/coreutils-four-20261022/join/_build/coreutils/src/join" (Native)
  DUT        : "/workspace/tmp/coreutils-four-20261022/join/_build/bench/join_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/join/final-campaign-v2-metrics-seed1.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 18 (discovered)
Coverage
  Option coverage: singles 17/18 (94.4%), pairs 102/153 (66.7%)
  Semantic coverage: buckets 20/27 (74.1%), extra=0, missing: fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, operand:symlink
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 214.22s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
    seed: 7

=== Coreutils fuzz campaign ===
Configuration
  Utility    : join
  Seed       : 7
  Budget     : 1000 iterations
  Reference  : "/workspace/tmp/coreutils-four-20261022/join/_build/coreutils/src/join" (Native)
  DUT        : "/workspace/tmp/coreutils-four-20261022/join/_build/bench/join_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/join/final-campaign-v2-metrics-seed7.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 18 (discovered)
Coverage
  Option coverage: singles 17/18 (94.4%), pairs 102/153 (66.7%)
  Semantic coverage: buckets 20/27 (74.1%), extra=0, missing: fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, operand:symlink
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 215.29s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
    seed: 19

=== Coreutils fuzz campaign ===
Configuration
  Utility    : join
  Seed       : 19
  Budget     : 1000 iterations
  Reference  : "/workspace/tmp/coreutils-four-20261022/join/_build/coreutils/src/join" (Native)
  DUT        : "/workspace/tmp/coreutils-four-20261022/join/_build/bench/join_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/join/final-campaign-v2-metrics-seed19.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 18 (discovered)
Coverage
  Option coverage: singles 17/18 (94.4%), pairs 102/153 (66.7%)
  Semantic coverage: buckets 20/27 (74.1%), extra=0, missing: fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, operand:symlink
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 211.07s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
```


## Final merged-checkout acceptance

The worker results above are preserved. Parent integration additionally ran the
complete final campaigns from `/workspace/dafnyutils`, using the merged shared
core, native adapter and all-four generator registry. This removes the worker
source-state difference caused by the additive bounded-read API. Utility
algorithms, specifications and proofs are unchanged. The unchanged mandatory
`make check TASK=join` passed in the integration worktree
(`join-check-v1.log/status`, exit 0, 1197 obligations, zero failed).

The final original-checkout build and runtime targets passed. Campaigns in tmux
`four-utils-main-fuzz-join` each completed seeds `1,7,19` with 1,000 exact
generated matches, no mismatches/timeouts/errors, and stderr included. Metrics
are `evidence/integration/main-fuzz-join-seed{1,7,19}.json`;
`main-fuzz-join-sources.sha256` and `main-fuzz-join-source-check.status`
bind the unchanged source and artifact across the run. These final merged-tree
campaigns are the canonical final integration evidence. Option/semantic coverage
annotations are not a claim of exhaustive input coverage. Existing domain and
time-observation limitations above still apply.

Final DLL: `/workspace/dafnyutils/_build/bench/join_bench.dll`, 1249792 bytes,
SHA-256 `b86b21678ffd8c74e37a5cd7dca529c63100e34571059988a577076f8436efe5`. Artifacts remain locally available under
`/workspace/tmp/coreutils-four-20261022/evidence/integration/`; they are not
candidate inputs. No commits were created. The complete final campaign stdout
follows verbatim, including its command and metadata.

```text
UTC: 2026-10-22T17:38:14.558358+00:00
CWD: /workspace/dafnyutils
CMD: python3 tools/coreutils_fuzzer/run.py fuzz join --seeds 1,7,19 --iterations 1000 --metrics-out /workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-join.json
Artifact SHA256: b86b21678ffd8c74e37a5cd7dca529c63100e34571059988a577076f8436efe5
All four tasks use the final merged core, native adapter and generator registry.
selected utilities: join
==> utility: join
    seed: 1

=== Coreutils fuzz campaign ===
Configuration
  Utility    : join
  Seed       : 1
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/join" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/join_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-join-seed1.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 18 (discovered)
Coverage
  Option coverage: singles 17/18 (94.4%), pairs 102/153 (66.7%)
  Semantic coverage: buckets 20/27 (74.1%), extra=0, missing: fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, operand:symlink
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 203.33s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
    seed: 7

=== Coreutils fuzz campaign ===
Configuration
  Utility    : join
  Seed       : 7
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/join" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/join_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-join-seed7.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 18 (discovered)
Coverage
  Option coverage: singles 17/18 (94.4%), pairs 102/153 (66.7%)
  Semantic coverage: buckets 20/27 (74.1%), extra=0, missing: fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, operand:symlink
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 196.90s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
    seed: 19

=== Coreutils fuzz campaign ===
Configuration
  Utility    : join
  Seed       : 19
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/join" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/join_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-join-seed19.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 18 (discovered)
Coverage
  Option coverage: singles 17/18 (94.4%), pairs 102/153 (66.7%)
  Semantic coverage: buckets 20/27 (74.1%), extra=0, missing: fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, operand:symlink
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 201.65s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
```
