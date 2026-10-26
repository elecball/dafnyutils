# dd contributor-maintenance record

This is repository maintenance, not an evaluated benchmark run. This record is
excluded from public task resources and candidate workspace materialization.
It summarizes external evidence; logs, metrics, binaries and mismatch bundles
remain outside documentation trees.

The acceptance results and binary fingerprints below describe the earlier
four-utility source snapshot. Subsequent verified whole-stdin layering and
affected dd regression results are recorded in
`plan/2026-10-23-stream-read-layering.md`; old artifacts do not describe a rebuild
against that changed shared API implementation. Dd's block policy remains local.

## Scope and proof boundary

The accepted domain is finite captured stdin to stdout with explicit
`status=none`, GNU block/count operands and suffixes, `iflag=fullblock` and
`iflag=count_bytes`, ASCII case conversion, global adjacent-pair `swab`, and NUL
padding with `conv=sync`. Help/version and malformed supported operands have exact
GNU diagnostics. `bs` overrides `ibs`/`obs`; conversion/input flags accumulate.
See [dd.md](dd.md) for the full domain and remaining descriptor, seeking,
record-conversion and elapsed-time limits. Excluded valid GNU invocations are
explicitly labeled benchmark-scope failures, not claimed parity cases.

The only new native primitive is one bounded stdin read. Its contract binds the
observed prefix, unread suffix and errno, permits short reads, consumes no input
on failure, and identifies EOF on an empty successful read in finite capture.
The libc adapter retries EINTR and has no block policy. The public wrapper
independently verifies 21 obligations (`primitive-verify.log`, exit 0).

`DdSpec` uses direct byte-index translation, native-read partitions and ordered
output partitions. Its readiness bound prohibits delaying a full writable output
block. Block assembly, padding, conversion, pair carry, count semantics, exact
partial-write diagnostics and stopping further reads are local Core/Proof
obligations. `Dd.RunCore` directly ensures `DdSpec.Spec`. No assumption, utility
extern, verification skip or termination waiver is added to the utility.

## Source and environment

Worker worktree: `/workspace/tmp/coreutils-four-20261022/dd`, detached at
`37b35bac3d4cf84cdd8ea02eb3279e8aa49307df`. Parent integration:
`/workspace/tmp/coreutils-four-20261022/integration`. No commits were requested
or created. GNU is `2cf491412c199e2211880ec3f4ba387026638a33`,
version `9.10.13-2cf49`. Source changes remain uncommitted. The final worker snapshot is frozen35.sha256;
final merged-checkout source/artifact hashes are recorded separately below.

Tools: Python 3.12.3, .NET SDK 8.0.131, tmux 3.4, Rust/Cargo 1.94.0,
Ruff 0.15.12, and benchmark Dafny
`4.11.1+5fa47c6e949dad736db25e02b5edad95d0b0be1a`.
Experiments run in named `dd-*` worker and `four-utils-*` parent tmux sessions.
Exact commands, working directories, timestamps, statuses and source hashes are
under `/workspace/tmp/coreutils-four-20261022/evidence/{dd,integration}/`.
Verification keeps isolated assertions, seed 42, the 30-second VC limit and
100-second declaration process boundary. Tests require artifacts prepared by
supported builds; they do not create temporary directories or rebuild toolchains.

## Original failures and corrections

- GNU swab pairs bytes across input records. A carried final odd byte can fill an
  output block exactly; that failure uses the full-buffer `writing to` diagnostic,
  while direct/final partial writes use `error writing`. Four bounded `/dev/full`
  scenarios distinguish those observable outcomes.
- Seed 1 iteration 42 exposed GNU's delayed `oflag=fullblock` rejection:
  `status=none oflag=fullblock conv=` must report the invalid conversion first.
  The original bundle is `dd/mismatches/dd-seed1-iter42/`; persistent fixed and
  regression cases preserve it. Canonical option names in unexpected-value
  diagnostics and the first byte of invalid UTF-8 short options are also covered.
- Final source review and `numeric-edge31.log` found incorrect precedence when a
  numeric magnitude overflows before an invalid suffix, and when a leading zero
  multiplier cancels an overflow. `numeric32.md` records the GNU unsigned scan,
  recognized unit prefix, signed range result and recursive multiplication rules.
  `numeric-edge32.log` matches all six original probes. Two observable runtime
  regressions and persistent fuzzer cases retain the defect.

Early exact fixed-text selection proofs timed out at the equality, rather than
at a stream heap obligation. A proposed opaque-text change was rejected by
automatic approval review and never applied. Transparent per-line literals,
local proof guidance and ordinary helper decomposition resolved the cost without
changing the specification or trust boundary.

The monolithic RunCore later exceeded the supported 100-second declaration
process boundary although individual VCs were fast. Verified task-local
`LoopProgress`, `ReadAndAppend`, and `FinishCopy` retain the same relations and
split real proof obligations. Focused snapshot31 results: ReadAndAppend 92/0 in
42.1 seconds, FinishCopy 86/0 in 41.9 seconds, RunCore 172/0 in 73.1 seconds.
The old process caps and root gate v2 failure remain in evidence and are not
counted as passing verification. Intermediate successful 3,000-case campaigns
precede final source changes and do not replace the final frozen-artifact run.

## Final frame correction and acceptance

Independent parent review found that the early Spec branch did not constrain
stdin, while both principal RunCore frames permitted stdin mutation in every
mode. The current implementation already left stdin alone, but the contract
could admit a candidate consuming input on help/version/errors. Frozen35 narrows
exactly the public and Core RunCore modifies clauses: stdin is writable only when
`raw.mode == Copy && raw.error == None`; early modes expose stdout/stderr only.
This follows the existing conditional-frame convention without adding redundant
state equalities, an assumption or a trusted derived fact. The immutable entry
header manifest records the stronger frame. Spec, runtime bodies, Schema, shared
core and generator are unchanged. `frames35.diff` and `frozen35.sha256` record
the exact two-file amendment from frozen34.

Focused amended proofs: Core RunCore 174/0 in 64.383 seconds; direct entry 19/0
in 17.223 seconds, with seed 42, isolated assertions, 30-second VCs and the same
100-second declaration boundary. The amended supported build, 32 runtime cases,
three persistent regressions, definition/profile validation and diff checks pass.
The final public-workspace audit `profile-dd-v4` also passes: the stronger entry
contract is retained and implementation/proof helpers remain incomplete editable
stubs; tests, fixtures and this document are excluded.

The unchanged final `make check TASK=dd` in parent tmux
`four-utils-check-dd-v5` passed, exit 0: 31 declarations,
990 obligations, zero failed; 32 runtime cases; 20 generated comparisons;
three marked proof-module cases. Exact command/source state/output/status are
`evidence/integration/dd-check-v5*`. Prior v4 also fully passed 31 declarations,
986 obligations and three proof cases, but predates the strengthened frames.
Earlier failed or superseded gates remain preserved and are not final evidence.

The final original-checkout build and runtime targets
`make build TASK=dd` / `make test TASK=dd` passed again after the amendment
(`main-build-dd-v2`, `main-runtime-dd-v2`). Final merged-source campaigns ran in
tmux `four-utils-main-dd-v2`: seeds `1,7,19`, each 1,000 requested/submitted/
completed exact generated matches, zero abandoned/mismatch/timeout/other errors,
and `ignore_stderr=false`. The source/artifact check passes. Metrics are
`evidence/integration/main-fuzz-dd-v2-seed{1,7,19}.json`; command/full stdout/status
and SHA-256 sources are adjacent. Final DLL is `/workspace/dafnyutils/_build/bench/dd_bench.dll`,
1207808 bytes, SHA-256 `6f43c4d291885444242dc41ef5f5325f6db0e738c6cbaa285d4eed321b20e3d8`.

Worker frozen34's 3,000 matches are retained as intermediate evidence
(`final-fuzz34*`), not substituted for the amended final artifact. The first main
DD campaign was intentionally cancelled before modifying sources; its exact
owned container was removed and other campaigns preserved.
`main-fuzz-dd-superseded.txt` records that cancellation. No required work remains
in the declared domain. No commits were created. Complete final campaign stdout:

```text
UTC: 2026-10-22T17:46:49.759513+00:00
CWD: /workspace/dafnyutils
CMD: python3 tools/coreutils_fuzzer/run.py fuzz dd --seeds 1,7,19 --iterations 1000 --metrics-out /workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-dd-v2.json
Artifact SHA256: 6f43c4d291885444242dc41ef5f5325f6db0e738c6cbaa285d4eed321b20e3d8
All four tasks use the final merged core, native adapter and generator registry.
selected utilities: dd
==> utility: dd
    seed: 1

=== Coreutils fuzz campaign ===
Configuration
  Utility    : dd
  Seed       : 1
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/dd" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/dd_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-dd-v2-seed1.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 2 (discovered)
Coverage
  Option coverage: singles 2/2 (100.0%), pairs 1/1 (100.0%)
  Semantic coverage: buckets 14/27 (51.9%), extra=0, missing: arg:empty, fixture:has-dir, fixture:has-file, fixture:has-symlink, fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 177.25s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
    seed: 7

=== Coreutils fuzz campaign ===
Configuration
  Utility    : dd
  Seed       : 7
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/dd" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/dd_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-dd-v2-seed7.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 2 (discovered)
Coverage
  Option coverage: singles 2/2 (100.0%), pairs 1/1 (100.0%)
  Semantic coverage: buckets 14/27 (51.9%), extra=0, missing: arg:empty, fixture:has-dir, fixture:has-file, fixture:has-symlink, fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 190.69s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
    seed: 19

=== Coreutils fuzz campaign ===
Configuration
  Utility    : dd
  Seed       : 19
  Budget     : 1000 iterations
  Reference  : "/workspace/dafnyutils/_build/coreutils/src/dd" (Native)
  DUT        : "/workspace/dafnyutils/_build/bench/dd_bench.dll" (DotnetDll)
  Case source: generated (scenarios, random inputs and corpus mutation)
  Limits     : max_args=10 max_fs_entries=12 timeout=10s shrink_attempts=250
  Comparison : stderr=included workdir=per-iteration
  Image      : dafnyutils-coreutils-fuzzer:latest
  Identity   : uid=1000 gid=1000
  Metrics    : "/workspace/tmp/coreutils-four-20261022/evidence/integration/main-fuzz-dd-v2-seed19.json"
  Image ID   : sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76
  Option pool: 2 (discovered)
Coverage
  Option coverage: singles 2/2 (100.0%), pairs 1/1 (100.0%)
  Semantic coverage: buckets 14/27 (51.9%), extra=0, missing: arg:empty, fixture:has-dir, fixture:has-file, fixture:has-symlink, fs:file-added, fs:file-content-changed, fs:file-removed, fs:mode-changed, fs:target-changed, fs:time-changed
Results
  Iterations : requested=1000 submitted=1000 completed=1000 not_started=0 unfinished=0
  Outcomes   : match=1000 mismatch=0 timeout=0 other_errors=0
  Elapsed    : 190.33s
  Status     : PASS - all requested iterations matched; no mismatch found
=== End campaign ===
```
