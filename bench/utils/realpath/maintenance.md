# Realpath contribution maintenance record

This is repository-maintenance memory, not public benchmark input. Candidate
profiles exclude this file, the completed solution, and external evidence.

The 2026-10-25 GNU traversal extension supersedes the strip-only delivered scope
and unresolved implementation work described in the historical records below.
Current scope is `realpath.md`; current source, commands, validation and limits
are recorded in `plan/2026-10-25-realpath-gnu.md`. Historical logs and artifact
fingerprints remain tied to their original snapshot.

Final integrated traversal validation: `make check TASK=realpath` passes all
43 editable declarations (781 obligations), 54 GNU runtime cases, twenty
generated cases and all four marked proof modules. Three final campaigns at
seeds 1, 7, 19 pass 3,000 exact comparisons, and all nine fixed regressions pass.
The final DLL SHA256 is
`7af162eac846496b699fef353d68b40f38e857424ee875543baa7316a97506bd`.
The plan above records separate immutable-spec author checks, native storage
representation limits and the exact evidence locations. No new trust annotation
or termination waiver is introduced; the shared core is unchanged.

The acceptance records below describe the four-utility source snapshot from
2026-10-22. The subsequent shared stdin-layering maintenance is recorded in
`plan/2026-10-23-stream-read-layering.md`; old binary fingerprints do not describe
a rebuild against that changed shared API implementation.

The follow-up source audit confirms that symlinks and raw `ReadLink` are already
modeled. `SYMLINK_MAX_DEPTH = 40` applies to one kernel-style metadata lookup;
GNU realpath's user-space traversal has no corresponding global forty-link
limit. A bounded 48-link chain succeeded with the pinned GNU `realpath -e`,
while kernel `stat` returned `ELOOP`. Script, log, exit status and fixture are
locally available in
`/workspace/tmp/experiment/realpath-finite-chain-20261023/`, tmux session
`realpath-finite-chain-20261023`. No expanding-loop or resource-pressure probe
was run. Physical traversal remains an unfinished utility-local algorithm/proof,
not an absent symlink primitive.

## Delivered scope and trust boundary

The delivered utility is total-proof strip mode: effective `-s`, `--strip`, or
`--no-symlinks`, with `-E`/`-e`/`-m`, relative output, q/z, multiple and empty
paths, help/version, and GNU parser diagnostics. It includes the original
explicit `-m -s` requirement. Default physical traversal and final `-P`/`-L`
runs are excluded and receive the documented benchmark-only mode diagnostic.
No shared IO contract, runtime adapter, evaluator, comparator, or scoring code
changed. Existing native primitives supply only cwd, path metadata and stream
observations; all path and relative-output calculations and their mathematical
judgments are task-local. `Realpath.RunCore` directly ensures `RealpathSpec.Spec`.
All new utility algorithms and proofs establish termination. Only the unmodified
scaffold process runner retains its existing partial-termination convention.

The generator's candidate and mutation guards classify the fixed GNU-permute
argument grammar. Exact long names take precedence over unique abbreviations;
required relative-option values consume their next token even when it resembles
an option. `--` ends option interpretation, and later link-mode flags override
earlier flags. Informational, parse-error and missing-operand exits are included;
otherwise the effective mode must be strip. No original literal `-s` is required.
The declared random option pool has 17 options and excludes standalone physical
and logical traversal. Separate read-only differential cases cover those flags
when subsequently overridden by strip, option values and `--` operands.

## Expanded scope history and unresolved blocker

Automatic approval review twice rejected writing the proposed full physical
command implementation and entry wiring because it introduced new partial
termination annotations while replacing the scaffold placeholder. Neither
rejected mutation executed. The coordinator then explicitly authorized finishing
this total-proof strip-only scope and retaining the physical drafts separately.
This was a contribution-development scope decision, not a weakened released
benchmark, comparator, or evaluated-run input. No further retry of the declined
physical wiring was made.

The source-backed termination issue is concrete: pinned `canonicalize.c:349-375`
records parent identity plus the entire remaining suffix after twenty link
expansions, without a global link-count bound. A link `l -> l/l` can grow that
suffix without repeating the key until excluded memory exhaustion. No resource
pressure experiment was run. The declined draft used no arbitrary fuel, new
answer-returning primitive, or unproved assumption, but automatic review still
rejected the proposed correctness-on-return boundary. Physical support remains
unfinished and is not counted as passing scope. Exact rejection text is in
`automatic-review-rejections.txt`; discarded drafts are under `physical-draft/`
in the external evidence directory. The coordinator owns disclosure of this
remaining extension blocker.

## Revisions, environment and artifact locations

Worktree: `/workspace/tmp/coreutils-four-20261022/realpath`.
Base: `37b35bac3d4cf84cdd8ea02eb3279e8aa49307df`, with uncommitted task changes.
GNU pin: `2cf491412c199e2211880ec3f4ba387026638a33`.
Dafny pin: `df5816d141a9a3874f4933f86649b38f8380257b`.
Dafny benchmark: `4.11.1+5fa47c6e949dad736db25e02b5edad95d0b0be1a`.
Python 3.12.3, dotnet 8.0.131, Rust 1.94.0, Ruff 0.15.12 and tmux 3.4.
Experiments set `PYTHONPATH=$PWD/src`, `DOTNET_PROCESSOR_COUNT=2` and
`CARGO_BUILD_JOBS=2`, and run in named tmux sessions.

All exact commands, full logs, exit statuses, metrics, original mismatch bundles,
source probes and drafts are available locally under
`/workspace/tmp/coreutils-four-20261022/evidence/realpath`. The companion files
`<name>.command`, `<name>.log` and `<name>.exit` record the working directory and
result for each named run below. These are maintenance artifacts available while
the shared workspace persists, not authorized future benchmark memory.
`probe.log` records versions and pins. Native GNU/Dafny source and GNU output
symlinks reuse owner artifacts; this worker did not rebuild GNU coreutils.
The coordinator ran the official GNU build prerequisite successfully in its
owner checkout and owns the final unchanged integration gate.

Docker image: `dafnyutils-coreutils-fuzzer:latest`, identity
`sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76`.
The tested candidate is `_build/bench/realpath_bench.dll`, 1,196,544 bytes,
fingerprint `fnv1a64:72f5e512108656a8`. `frozen-implementation.json` records
the initial 18-file snapshot. `frozen-implementation-v2.json` records the sole
subsequent specification-parentheses amendment described below. Maintenance
documentation is tracked separately.
No commits were created.

## Validation results

Runtime parity and Dafny verification are independent results. All checks below
completed with exit status 0, with no skipped benchmark cases.

| Evidence run | Exact check | Result |
| --- | --- | --- |
| `total-build-four` | `make -C bench/utils/realpath build` | Supported build passed; this target does not verify proofs. |
| `project-verify-two` | `make -C bench/utils/realpath verify` | 35/35 declarations, 540 assertion batches, 0 failed; `DAFNY_VERIFICATION_OUTCOME=verified`. |
| `marked-proof-tests` | `python3 -m pytest -q -n0 --import-mode=importlib -m dafny_verify bench/utils/realpath/Tests.py` | All 4 proof-module cases passed. The later five Python runtime additions did not change Dafny sources or the proof selection. |
| `runtime-tests-four` | `make test TASK=realpath` | 45 passed, 4 proof cases deselected. Both streams and exit status compared strictly. |
| `guard-tests` | Scoped Cargo test filter `fuzz::input::generators::realpath::tests` | Both pure in-memory guard tests passed; unrelated tests remained filtered. |
| `regression-three` | Fuzzer regression command on `tools/fixtures/coreutils_fuzzer/v1/regressions/realpath.json` | All 3 fixed strict expectations passed. |
| `fuzz-seeds-three` | `python3 tools/coreutils_fuzzer/run.py fuzz realpath --seeds 1,7,19 --iterations 1000 --metrics-out /workspace/tmp/coreutils-four-20261022/evidence/realpath/pr-three-metrics.json` | All 3 campaigns passed, as detailed below. |
| `python-lint-two`, `python-format-two` | Ruff check and format check of `Tests.py` | Both passed. |
| `rust-format` | `cargo fmt --manifest-path tools/coreutils_fuzzer/Cargo.toml -- --check` | Passed. |
| `definition-two` | `python3 -m benchmarks validate realpath` | Definition valid. |
| `profile-two` | `python3 -m tools.generate_task_profiles --utility realpath --output-dir _build/profile-review-final` | Initial profile generated and inspected; superseded by `profile-amended` after the public specification amendment. |
| `profile-amended` | `python3 -m tools.generate_task_profiles --utility realpath --output-dir _build/profile-review-amended` | Final public resource profile generated and inspected. |

The isolated verifier retained its fixed random seed 42, assertion isolation,
30-second VC limit and 100-second process boundary. No limit, obligation,
verification scope or evaluator policy was changed.

Each final campaign requested, submitted and completed exactly 1,000 cases,
with 1,000 matches, 0 abandoned, 0 mismatches, 0 timeouts and 0 other errors.
Seeds 1, 7 and 19 took 202.82, 206.61 and 216.81 seconds respectively. Every
campaign records `ignore_stderr=false` and 17/17 declared single-option coverage.
Metrics are `pr-three-metrics-seed1.json`, `-seed7.json` and `-seed19.json`.
Generation includes fixed scenarios, random bounded trees and corpus mutation,
with ordinary files, directories, links, dangling links, cycles and mode-000
paths. Filesystem comparison and all original comparator behavior are unchanged.

The final profile has 13 public resources: natural/formal specifications and
existing core contracts. It excludes `maintenance.md`, `Tests.py`, completed
Core/Proof/PathProof, all external evidence and physical drafts. Editable paths
are restricted to the task directory; required outputs are Core, Proof and the
entry source. Resource copying was inspected to confirm it copies declared
resources rather than the whole task tree.

## Original failures and retained regressions

Original logs and mismatch bundles remain unchanged; successful reruns use new
names.

- `runtime-tests.log` reported 39 passing cases and one mismatch for `--=x`.
  GNU treats the empty long-option name as ambiguous over all long options. The
  fixed diagnostic text is covered by a retained fixture and the runtime suite.
- `fuzz-seeds.log` stopped at seed 1 iteration 91 after a corpus mutation removed
  the original `-s`. This was an out-of-scope generator escape, preserved under
  `repros/realpath-seed1-iter91`. A mutation guard and effective-mode classifier
  repair the generator boundary; comparison was not weakened. The original
  failing pure mutation test and successful reruns are retained.
- `fuzz-seeds-two.log` stopped at seed 1 iteration 174 on a genuine accepted
  strip-mode error: GNU succeeded for `__rp-blocked/./../missing`, whereas the
  candidate incorrectly reported EACCES. The complete original bundle remains
  under `repros/realpath-seed1-iter174`. Pinned `_build/coreutils/lib/config.h`
  defines `LSTAT_FOLLOWS_SLASHED_SYMLINK=1` at line 3620 and `HAVE_FACCESSAT=1`
  at line 1943, so GNU's `dir_suffix` is `/`. The candidate had used `/./`, which
  unnecessarily requires search permission inside the final directory. Both
  local specification and implementation now observe `path + "/"`. The mode-000
  fixed regression and all three final fuzz campaigns pass without excluding
  permissions or suppressing diagnostics.
- `project-verify.log` passed the first 24 declarations, then preparation hit the
  fixed 100-second process boundary with no reported VC error. The expensive
  `PrepareRelative` proof was guided by hiding unrelated definitions and
  revealing only `RelativeSetup`, `ToOperand` and `SetupFailure`. Its 19 isolated
  batches now pass under unchanged limits, within the complete 540-batch gate.
- `regression.log` initially failed fixture decoding because the case-set field
  was `input` instead of schema field `case`. That setup failure remains logged;
  the corrected two-case run and final three-case run both passed.

The three persistent cases are empty-long-option ambiguity, nondirectory
`plain/./../missing`, and unsearchable-directory `blocked/./../missing`. The
runtime suite also covers `/./../`, `/.//`, `/./.` suffix classification,
relative-prefix boundaries, relative-directory errors, q/z, empty operands,
help/version ordering, invalid UTF-8-byte diagnostics and `/dev/full` failure.

## Additional author-side specification audit

After the first official integration gate passed, the coordinator requested
standalone verification of every pure specification and schema declaration.
This author-side check adds coverage of mathematical helper well-formedness,
recursive termination, read frames and fixed-byte literal ranges; it is separate
from the unchanged candidate/contribution verification gate.

The first standalone `RealpathSpec.dfy` attempt (`standalone-spec-audit`) emitted
three indentation warnings at lines 131, 228 and 281, then hit an added 100-second
whole-file audit cap with exit 124 and no completed VC count. The coordinator
authorized only parentheses around those three existing compound else branches.
Exactly six parentheses were added; no expression meaning, scope, trust,
termination requirement, or implementation changed. The original specification
is preserved as `spec-before-parentheses.dfy`, and the exact amendment is in
`parentheses-amendment.diff`. Final specification SHA-256:
`633931d8e66f60f58e385ddf0c6e1f90a3df3c22e4f2e4770dfe2f9163222629`.

The complete clean audit enumerated all 40 specification declarations, with no
library exclusions, no dependency-verification skip and no warning allowance.
Every final declaration passed: **2,530 verified assertion batches, zero errors,
zero warnings**. The unchanged schema passed its complete standalone audit with
**9 verified batches, zero errors, zero warnings**, exit 0. Commands retained
`--standard-libraries:false`, `--boogie=/randomSeed:42`,
`--verify-included-files`, `--isolate-assertions`,
`--verification-time-limit:30` and `--allow-external-contracts`. File and symbol
filters select each complete requested declaration; no body or obligation is
omitted. The full completion summary and per-declaration commands/logs/exits are
`standalone-spec-completed-summary.json` and `standalone-spec-clean-*`.

The initial per-declaration author audit used an added outer 100-second cap.
Its 39 other declarations passed, totaling 1,267 batches, while `HelpText` alone
hit that aggregate cap with exit 124. Both the failed attempt and its progress
remain unchanged in `standalone-spec-clean-HelpText.*`; the first audit loop's
exit 1 is also retained. This was not an individual VC timeout or a proof defect.
Measured prior evidence was `AmbiguityOptions`: 347 independent fixed-byte
range checks completed in 37.16 seconds. `HelpText` has 1,263 fixed literal bytes,
so the aggregate author-audit cost is inherent in its many isolated checks.

The coordinator explicitly authorized rerunning the **same complete HelpText
declaration** with an author-only outer 600-second cap. Per-VC 30 seconds, seed
42, assertion isolation, source, declaration scope and all other proof options
remained unchanged. `standalone-help-complete` exited 0 in **118.61 seconds**
wall time, with all 1,263 successes reported and counters 1 through 1,263
preserved. Median individual VC time was 0.02047 seconds; maximum was 0.27768
seconds; their sum was 30.77 seconds. This establishes the aggregate-cost basis
for the author-side wall-clock allowance. No repository, candidate,
contribution-gate or evaluator limit was changed, and no assertion batch was
skipped. The final 2,530-batch result includes this successful complete rerun.

`parentheses-build` passed the supported build. The rebuilt worker DLL is
byte-identical to the preserved artifact that passed all three 1,000-case
campaigns: both are 1,196,544 bytes, SHA-256
`d6428577c5edf2e44753852c1b058f3bbb73bd2da3ae1763e613fb39f68ba659`.
`parentheses-dll-comparison.json` records that comparison. Under the coordinator's
explicit criterion, the existing 3,000 strict comparisons therefore remain valid
on the exact final worker artifact. No fuzz rerun was needed. The amended public
profile has the same 13-resource boundary and exclusions. No further source
amendment followed the three pairs of parentheses.

## Test audit, integration handoff and next action

New Python runtime tests reuse already-built reference and candidate artifacts.
The fixture performs only existence assertions and never builds or copies trees.
Transitive execution helpers perform bounded direct subprocess calls, without
workspace publication, temporary directories, bulk reads/hashes, real fixture
writes or sync operations. The tests use fixed read-only repository operands;
`/dev/full` is the only intentional output failure boundary. Native cases carry
`integration`, and proof cases retain `dafny_verify`. Worker benchmark pytest
configuration emits unknown-integration-marker warnings; none were suppressed.
The coordinator's integration configuration already registers the marker.
Unrelated existing development tests were not run or changed. The new Rust tests
are pure in-memory scope and mutation checks. Benchmark fixtures are preserved.

Recursive directory inspection found only root and nested Dafny `plan/` and
`wiki/` trees; their files and symlinks were inspected and no non-Markdown or
artifact-symlink violations were found. No task evidence was stored there.

The coordinator imported all 16 nonshared frozen files and merged the two shared
registry additions with other utilities. It also updated integration's expected
patterned-generator registry set. It reported the unchanged official
`make check TASK=realpath` v1 gate passing with exit 0, then imported the sole
parentheses amendment and reran the same gate. The coordinator confirmed final
**v2 exit 0**: 35 declarations, 540 obligations, zero failed; 45 runtime cases,
20 generated cases and 4 marked proof cases passed. Final integration evidence
is `/workspace/tmp/coreutils-four-20261022/evidence/integration/realpath-check-v2`
with `.log` and `.status` companions. The v1 evidence remains preserved.

All worker checks and the root-owned mandatory gate are complete. The worker's
last handoff is this documentation-only addendum; no further checks or source
changes are needed. No frozen source file should change without notifying the
coordinator and invalidating affected checks. The coordinator's next concrete
action is to import this maintenance addendum and report the completed validation,
physical-extension approval blocker and delivered strip-only scope. No local
implementation or proof obligation remains unfinished within that scope.

## Final merged-checkout acceptance

The worker results above are preserved. Parent integration additionally ran the
complete final campaigns from `/workspace/dafnyutils`, using the merged shared
core, native adapter and all-four generator registry. This removes the worker
source-state difference caused by the additive bounded-read API. Utility
algorithms, specifications and proofs are unchanged. The unchanged mandatory
`make check TASK=realpath` passed in the integration worktree
(`realpath-check-v2.log/status`, exit 0, 540 obligations, zero failed).

The final original-checkout build and runtime targets passed. Campaigns in tmux
`four-utils-main-fuzz-realpath` each completed seeds `1,7,19` with 1,000 exact
generated matches, no mismatches/timeouts/errors, and stderr included. Metrics
are `evidence/integration/main-fuzz-realpath-seed{1,7,19}.json`;
`main-fuzz-realpath-sources.sha256` and `main-fuzz-realpath-source-check.status`
bind the unchanged source and artifact across the run. These final merged-tree
campaigns are the canonical final integration evidence. Option/semantic coverage
annotations are not a claim of exhaustive input coverage. Existing domain and
time-observation limitations above still apply.

Final DLL: `/workspace/dafnyutils/_build/bench/realpath_bench.dll`, 1201152 bytes,
SHA-256 `f3cad138bda83737d2be61e53386639a189fda675227c10af095d2b714856911`. Artifacts remain locally available under
`/workspace/tmp/coreutils-four-20261022/evidence/integration/`; they are not
candidate inputs. No commits were created. The complete final campaign stdout
follows verbatim, including its command and metadata.

```text
UTC: 2026-10-22T17:38:14.564149+00:00
CWD: /workspace/dafnyutils
CMD: python3 tools/coreutils_fuzzer/run.py fuzz realpath --seeds 1,7,19 --iterations 1000 --metrics-out /workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-realpath.json
Artifact SHA256: f3cad138bda83737d2be61e53386639a189fda675227c10af095d2b714856911
All four tasks use the final merged core, native adapter and generator registry.
selected utilities: realpath
==> utility: realpath
    seed: 1

=== Coreutils fuzz campaign ===
Configuration
  Utility    : realpath
  Seed       : 1
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/realpath" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/realpath_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-realpath-seed1.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 17 (discovered)
  Outside scope: --logical, --physical, -L, -P
Coverage
  Option coverage: singles 17/17 (100.0%), pairs 112/136 (82.4%)
  Semantic coverage: buckets 19/27 (70.4%), extra=0, missing: arg:empty, fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, stdin:consumed
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 205.03s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
    seed: 7

=== Coreutils fuzz campaign ===
Configuration
  Utility    : realpath
  Seed       : 7
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/realpath" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/realpath_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-realpath-seed7.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 17 (discovered)
  Outside scope: --logical, --physical, -L, -P
Coverage
  Option coverage: singles 17/17 (100.0%), pairs 114/136 (83.8%)
  Semantic coverage: buckets 19/27 (70.4%), extra=0, missing: arg:empty, fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, stdin:consumed
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 200.01s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
    seed: 19

=== Coreutils fuzz campaign ===
Configuration
  Utility    : realpath
  Seed       : 19
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/realpath" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/realpath_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-realpath-seed19.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 17 (discovered)
  Outside scope: --logical, --physical, -L, -P
Coverage
  Option coverage: singles 17/17 (100.0%), pairs 112/136 (82.4%)
  Semantic coverage: buckets 19/27 (70.4%), extra=0, missing: arg:empty, fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed, stdin:consumed
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 203.49s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
```
