# Stream and time contract admissibility

Status: done; source, regressions, independent review, separate main integration, and required commit hooks all passed.

## Objective and scope

Repair inconsistent Dafny native stream and time parse contracts in the isolated
`fix/stream-contract-admissibility` worktree at
`37b35bac3d4cf84cdd8ea02eb3279e8aa49307df`. This is repository maintenance,
not an evaluated run. No private evaluator material, benchmark oracle fixtures,
or prior task solutions are authorized or needed.

Acceptance: the full original primitive relations have constructive outcomes for
every provider admitted into IO state; malformed providers remain expressible at
the raw contract layer and cannot establish falsehood; the original public stream
and time result relations and utility `RunCore ==> Spec(...)` obligations remain
unchanged; relevant native-wrapper verification and bounded contract regressions
pass without new assumptions, trust annotations, or verification skips.

Non-goals: runtime ABI or execution changes; stdin chunking; evaluator, dataset,
or scoring changes; main-checkout cleanup; dependency or toolchain builds; commits
before parent review.

## Evidence and proposed design

Read `/workspace/AGENTS.md`, repository `AGENTS.md`, `DAFNYSTYLE.md`,
`bench/AGENTS.md`, `Makefile`, affected `IO.dfy` and `IOContract.dfy`,
`World.dfy` request/result datatypes, `docs/core-api.md`, the contribution guide,
and existing filesystem/native-failure validity subsets. No narrower directory
instructions exist in the affected paths. Plan/wiki indices were read under the
maintenance boundary; unrelated topic bodies were not read.

`NativeReadFile` (read and probe), `NativeReadStdin`, `NativeWriteStdout`,
`NativeWriteStderr`, `NativeParseTimestamp`, and `NativeParseDate` currently assert
full relations over arbitrary ghost observations. Wrong result constructors and
successful time parses with nanoseconds -1 make those postconditions impossible.

Proposed repair: add provider validity predicates defined using the existing full
relations, constructive failure witnesses, and internally validated ghost state,
following `ValidFilesystemObservations` and `ValidNativeFailureObservations`.
Keep the raw datatypes and public observer return types; expose their validity
explicitly. This is a semantic model-state invariant, not merely representation
validity, and it excludes malformed providers from IO state. It leaves malformed
raw providers available for counterexample proofs and leaves all utility Specs
unconditional. Parent approved this boundary before implementation; no additional caller preconditions or utility guards are permitted.
The alternative requires conditional native guarantees and caller admissibility
preconditions across all utilities, because the original unconditional utility
specifications cannot hold for impossible observations.

## Change table

| Owning repository / file or symbol | Change and reason | Unmet without it | Validation |
| --- | --- | --- | --- |
| dafnyutils / `bench/core/IOContract.dfy` | Define validity, constructive witnesses, inhabited provider subsets from existing relations | Arbitrary provider may have no original-contract outcome | Focused Dafny verification and negative/positive ghost regressions |
| dafnyutils / `bench/core/IO.dfy` | Store validated stream and time providers; preserve raw public observer signatures with explicit validity | Native extern postconditions remain contradictory | Verify changed observers, wrappers, and representation constructors |
| dafnyutils / `tests/core/stream_contract_admissibility.dfy` | Prove malformed constructor/time examples have no full-contract outcome, and valid success/partial/failure outcomes remain admitted, including file ReadFailed/CloseFailed and read-only probes | No executable verifier regression for the defect | Direct Dafny verify; one bounded source file, no builds or temporary directories |
| dafnyutils / `docs/core-api.md` | State precise validated-state/trust boundary and compatibility | API guide implies arbitrary providers are supported | Diff review against source |
| dafnyutils / `wiki/stream-contract-admissibility.md` and `wiki/INDEX.md` | Record reusable consistency boundary and proof scope | Future maintenance may silently reintroduce arbitrary providers | Source links and focused verification evidence |
| dafnyutils / this plan and `plan/INDEX.md` | Record scope, evidence, verification, blockers and handoff | No reproducible maintenance record | Markdown/artifact audit |

Affected layers: model-state specification and proof boundary only. Native
implementation, utility observable specifications, evaluator, datasets, scoring,
and reporting remain unchanged. No package approval is needed. Worktree and
scratch writes require the already authorized outside-sandbox execution path.

## Validation

Working directory: `/workspace/tmp/leanutils-port/dafny-contract-fix`.
Dafny binary: `/workspace/dafnyutils/dafny/Binaries/Dafny`, version
`4.11.1+5fa47c6e949dad736db25e02b5edad95d0b0be1a`.

- Inspect supported Make targets before choosing checks: root build/test targets
  and utility `verify` targets exist; no core-only verification Make target exists.
- Direct focused Dafny commands will use `verify --allow-external-contracts
  --verify-included-files --isolate-assertions --verification-time-limit:30
  --boogie=/randomSeed:42 --standard-libraries:false` and explicit symbol filters
  for the affected contract/provider and IO wrapper obligations. Record exact
  commands and results below after confirming the compiler options.
- Verify the bounded ghost regression source without filters or assumptions. As a negative control, feed the baseline IO source plus the two new getter regression lemmas to Dafny on stdin; it must fail to prove validity. This is an in-memory diagnostic, never a submitted source or passing proof.
- Final compatibility: supported utility `make verify` where the local metadata
  and available Python prerequisites permit; otherwise record the exact blocker.
  Do not build all Dafny or invoke benchmark oracle tests.
- `git diff --check`; inspect final hunks and recursively inspect `plan/` and
  `wiki/` for non-Markdown files. Generated evidence belongs under
  `/workspace/tmp/leanutils-port/dafny-contract-evidence/`, never plan/wiki.

## Progress, evidence, blockers and next action

- Completed read-only source inspection and identified the seven affected native
  declarations (eight request variants counting read versus probe).
- Parent approved the semantic state-invariant design, constructive witnesses and request feasibility lemmas.
- No test/proof run claimed yet.
- Next action: implement the approved predicates/subsets, internal state invariant,
  request feasibility lemmas, bounded ghost regressions and API documentation.

### Verified implementation progress

- Original primitive relation preservation: a read-only script compared all 15
  affected `*ContractFields` / `*Spec` definitions with `git show HEAD:<path>`;
  every definition is byte-for-byte unchanged.
- Time admissibility definitions and request lemma: 10 assertions verified,
  0 errors. Stream definitions/witness/subset/request lemma: 365 assertions
  verified, 0 errors. Region constructors: 2 assertions verified, 0 errors.
- Initial getter verification: 12 verified, 0 errors. Getter output names were
  then made explicit to avoid unnecessary self-calls in their postconditions;
  final getter verification remains required.
- Native/wrapper range: 107 assertions verified, 0 errors across 22 symbols.
- First standalone regression: 340 verified, 0 errors; expanded regression
  additionally checks both public getter guarantees and explicitly rejects
  invalid providers, and is running.
- Supported Echo `make verify` is running (50 declarations). Its initial command
  used relative `PYTHONPATH=src`, and the installed `benchmarks` Python package
  resolves to `/workspace/dafnyutils/src/benchmarks/__init__.py`; its verified
  project and source snapshot are the isolated worktree. Any subsequent
  supported Make command must use the absolute worktree `PYTHONPATH`.

- Expanded observer/rejection regression passed: 17 symbols, 348 verified,
  0 errors. The baseline IO negative control failed at exactly the expected
  two validity postconditions (exit 4). Final getters passed: 10 verified,
  0 errors.
- Independent review requested positive file/probe stage coverage. Added a
  fixed two-inode ghost fixture and five scenarios (success, partial read error,
  complete-data close error, probe success and probe close error). These contain
  no real filesystem fixture or writes; final regression recheck is required.

### Review adjustments and final scope

- Independent review requested success/failure file stages, read-only probes and
  successful stdout/stderr coverage. A custom two-inode fixture introduced
  unnecessary set-image proof obligations, including one 30-second subset
  timeout; leaf and child-name guidance resolved image facts but fixture
  construction remained disproportionate. Parent approved replacing it with
  generic fs/path hypotheses on `ModeledReadFileResultFields` and native path
  resolution. These are source filesystem facts, not the full observed
  relation under test. No verifier limit was increased. The final regression
  has 24 symbols and no filesystem fixture construction. The obsolete failing
  23-symbol run was stopped, and its failed source is not retained.
- Supported Echo verification completed all 50 declarations, including direct
  `RunCore ==> Spec(...)`: `DAFNY_VERIFICATION_OUTCOME=verified phase=verify`,
  total 1888, failed 0. Its project snapshot was unchanged throughout the run.
- The IOContract introductory comment was corrected after Echo completed to
  describe semantic model validity and primitive feasibility accurately; no
  logical definition changed after that utility check.
- Parent also approved a separate current-main integration for its pre-existing
  chunked stdin model. It is recorded in main
  `plan/2026-10-23-stream-contract-integration.md`; the isolated branch deliberately
  does not incorporate that unrelated chunk work. The separate incremental
  patch/evidence lives under
  `/workspace/tmp/leanutils-port/dafny-contract-evidence/`.

## Final validation and handoff

Working tree: isolated `fix/stream-contract-admissibility` based on
`37b35bac3d4cf84cdd8ea02eb3279e8aa49307df`. All commands below ran from
`/workspace/tmp/leanutils-port/dafny-contract-fix` using
`/workspace/dafnyutils/dafny/Binaries/Dafny` version
`4.11.1+5fa47c6e949dad736db25e02b5edad95d0b0be1a`.

The core checks used these exact common arguments:
`verify --allow-external-contracts --verify-included-files --isolate-assertions
--verification-time-limit:30 --boogie=/randomSeed:42 --cores:1`.

| Input and exact additional selection | Outcome |
| --- | --- |
| `bench/core/IOContract.dfy --filter-position=IOContract.dfy:608-630` | 10 assertions verified, 0 errors |
| `bench/core/IOContract.dfy --filter-position=IOContract.dfy:1717-1789` | 365 assertions verified, 0 errors |
| `bench/core/IO.dfy --filter-position=IO.dfy:180-207` | 2 assertions verified, 0 errors |
| `bench/core/IO.dfy --filter-symbol=BenchIO.IO.trusted` (final named-result getters) | 10 verified, 0 errors |
| `bench/core/IO.dfy --filter-position=IO.dfy:529-718 --progress=Symbol` | 107 assertions verified, 0 errors across 22 symbols |

Complete final regression command (no filter and no included-library proof claim):

```sh
/workspace/dafnyutils/dafny/Binaries/Dafny verify tests/core/stream_contract_admissibility.dfy --allow-external-contracts --isolate-assertions --verification-time-limit:30 --boogie=/randomSeed:42 --cores:1 --progress=Symbol
```

Result: all 24 symbols, 898 verified, 0 errors. The seven review-requested
scenarios cover successful file reads, partial `ReadFailed`, complete-data
`CloseFailed`, successful read-only probes, probe close failure, successful
stdout and successful stderr. They rely on ordinary modeled filesystem facts,
not the full observed Spec or validity predicate being tested.

Supported complete utility compatibility command:

```sh
PYTHONPATH=src DAFNY_BENCHMARK=/workspace/dafnyutils/dafny/Binaries/Dafny make -C bench/utils/echo verify
```

Result: 50 declarations, total 1888, failed 0; verified outcome. The installed
Python tooling resolves from the main checkout as noted above; project source
and snapshot were the isolated worktree. No source changed during that run.

The negative control combined `git show HEAD:bench/core/IO.dfy` with the two
new getter-regression lemmas in memory, fed it to `Dafny verify --stdin` from
`bench/core`, and selected `--filter-symbol=ObserverExposesValidity` with the
same proof limits. It failed at exactly the two expected validity postconditions
(exit 4). This expected failure is diagnostic evidence, not a successful proof.

Scoped `Dafny format bench/core/IO.dfy bench/core/IOContract.dfy
tests/core/stream_contract_admissibility.dfy` passed; a before/after comparison
confirmed every stripped source line was unchanged, so formatting preserved
semantics. `git diff --check` passes. Recursive path inspection found no
non-Markdown files in this worktree's `plan/` or `wiki/` trees.

[Reusable boundary record](../wiki/stream-contract-admissibility.md) and
[canonical API guide](../docs/core-api.md) are updated. No benchmark oracle run,
native runtime build or full suite of unrelated utilities was needed for this
model-state change. The proof establishes native contract feasibility and
wrapper compatibility under the existing trusted native boundary; it does not
prove libc/gnulib implementation correctness.

Completed: common baseline repair, proof witnesses, unchanged full primitive
relations, unconditional utility specifications, full focused checks, bounded
regression, Echo closure, independent source review and the requested cohesive
source commit. The required repository hook passed both `dafny format bench`
and `make test-unit`; the hook suppresses successful test output, so no unit
count is claimed. The hook left no unrelated or unstaged source changes.

The separate main integration also passed its complete 26-symbol regression
(968 verified), all new stream definitions (367 assertions), time definitions
(10 assertions), getters (10 checks), and native/wrapper/derived-loop range
(173 assertions). Its exact patch is
`/workspace/tmp/leanutils-port/dafny-contract-evidence/main-compatible.patch`;
`main-tested-state.json` records exact tested main source hashes and results.
Removing only approved additions/replacements reconstructs all three prior dirty
files byte-for-byte, and the patch reverse-check passes. Main is intentionally
unstaged and uncommitted because its chunk model includes unrelated prior work.

No implementation, proof or delivery blocker remains. Parent final reporting is
the only follow-up: use this isolated source commit plus the intentionally
uncommitted, tested main compatibility patch without staging unrelated changes.
