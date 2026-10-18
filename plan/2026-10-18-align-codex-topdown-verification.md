# Align candidate and Top-down verification

Status: done
Owner: Dafnyutils maintenance, not an evaluated run.
Root plan: [integration plan](../../plan/2026-10-18-align-codex-topdown-verification.md).

## Objective and acceptance

Apply the same prospective success policy to public and final candidate verification:
one `measure-complexity --mutations 3 --random-seed 0` command per proof target,
`--isolate-assertions`, 30 seconds per VC per mutation, 100 seconds per target
process. Preserve complete reachable editable proof coverage, including constrained
types and zero-obligation declarations. Reject candidate `timeLimit` and equivalent
overrides without preventing baseline manifest generation or rejecting unchanged
protected support. Publish the policy through generated public rules.

Non-goals: provider branches, model calls, proof/specification changes, datasets,
scoring aggregation, new dependencies, container changes, or paid experiments.
The user authorizes this evaluator-policy change and eventual requested commit;
the parent handles independent verification and landing.

## Evidence, compatibility, risks

Starting revision: `5da26fd4776bc8187bec769fb663e2c44048d991`.
The isolated checkout has only the copied `AGENTS.md` pre-existing modification;
preserve it uncommitted. Read root/owner instructions, original owner plan/wiki
indexes and declaration-analysis/public-verification-runtime knowledge. No further
nested instruction files govern planned Python paths. Shared `verification.py`
currently calls `verify` per file, without outer timeout; public and final reuse
it. `DefinitionInfo.attributes` and native semantic fingerprints already exist.
Top-down's policy is in Cosyn target_validator.py/goal_tool.py and runtime_support/dafny.py;
it runs three internal mutations, not three commands. Native source confirms the
100s budget must be renewed per target. Strict warning, report, source identity,
and existing bodyless-callable rejection remain requirements.

Native coverage investigation identified two protocol risks before implementation:
datatype constructors have verification obligations but belong to their datatype
analysis entry; statement attributes are not present in declaration attributes.
Scope refinement authorized by parent on 2026-10-18: consume a new opt-in
native `--include-verification-facts` analysis field containing actual
`ICanVerify` targets. Do not guess target names or use ambiguous prefixes. Native
implementation belongs to the nested Dafny repository and its separate plan,
coordinated by the parent. Python candidate validation requests facts and fails
closed if absent. Baseline manifest construction remains free of override
rejection. Resolve effective nested attribute behavior before claiming enforcement. Existing authored baseline time limits must
still allow manifest creation. Future formerly single-pass/limit-dependent
candidates can fail intentionally; historical results are unchanged.

## Change table

| File/symbol | Change, necessity, unmet requirement | Validation |
| --- | --- | --- |
| `src/analysis/models.py`, `src/analysis/client.py` | Model and opt in to native verification targets; otherwise constructors and by-method identity require ambiguous guesses | In-memory model/client contract checks, configured static checks |
| `dafny` gitlink | Pin the independently checked opt-in native analysis extension required by the client | Native owner build/tests and independent generic CLI controls |
| `src/verification.py` | Mutation mode and per-target timeout through existing runtime.process.run_process_capture_bytes (process-group cleanup), with full proof surface and existing evidence gate; otherwise success criteria differ | In-memory subprocess/report cases, static checks, final native smoke |
| `src/entry_contract.py` | Candidate-only structured limit rejection and required native target tuple on ValidatedEntryContract; otherwise candidates override policy or coverage is guessed | Fake structured contract cases, baseline construction coverage |
| `src/benchmarks/generated_profile.py` | Public immutable limit and mutation rule; otherwise agents lack policy | Structured profile review |
| `tests/core/test_verification_policy.py` | Fake subprocess/reports/storage; no real directory/process/sync | Narrow serial supported unit target |
| `tests/core/test_verification_limits.py` | In-memory analyzed definitions/contracts | Narrow serial supported unit target |
| `plan/2026-10-18-align-codex-topdown-verification.md`, `plan/INDEX.md` | Ownership, evidence, handoff | Diff/link review |
| `wiki/architecture/verification-policy.md`, `wiki/INDEX.md` | Durable policy and applicability with reciprocal plan link | Markdown-only audit |

Owning repository for every row: Dafnyutils. Affected layers: verifier invocation,
candidate contract enforcement, public policy, prospective evaluator proof pass/fail.
Specification, proof content, dataset, runtime oracle and aggregation layers stay fixed.

## Validation

Working directory for every Python command: this Dafnyutils checkout. Inspect all
selected fixtures and transitive production paths first. Existing checkout contains
historical prohibited temporary-directory tests: do not collect or run them. New
checks fake TemporaryDirectory, subprocess, report parsing and contract storage so
there is no test-created directory, real subprocess or synchronization.

- `PYTHONPATH=src PYTEST_ADDOPTS='tests/core/test_verification_policy.py tests/core/test_verification_limits.py tests/core/test_module_boundaries.py' make test`: serial focused units; expect all pass.
- `ruff format --check src/verification.py src/entry_contract.py src/benchmarks/generated_profile.py tests/core/test_verification_policy.py tests/core/test_verification_limits.py` and corresponding `ruff check`: expect clean. Makefile has no lint target.
- `PYTHONPATH=src pyright -p pyrightconfig.json`: configured source typecheck; expect clean or record pre-existing errors. If interpreter discovery omits installed dependencies, use a scratch config extending this config with the existing Python dist-packages path, without changing dependencies or repository configuration. Makefile has no typecheck target.
- Final integration/native smoke only after unit/static checks settle; parent owns a tiny scratch synthetic command/report smoke with installed `dafny-benchmark` 4.11.1+bc427b21461f258fd8de34232e01bb6be03cee39, no build/copy/provider call.
- `git diff --check`, planned-file diff review, recursive plan/wiki Markdown-only inventory.

Unrun full suites are not passing results. No model-performance, full benchmark
proof, runtime scoring or statistics claim follows from local checks.

## Progress and handoff

Inspected current Python/source-native policy and instruction scope. Next: resolve
native structural gaps, implement, run safe checks, record reusable findings and
hand off to fresh independent verification. No commits or provider calls.

Implementation checkpoint: initial focused 17 fake-boundary units passed. Native opt-in target facts supersede the initial guessed target mapping before final validation. Final aggregate `total>0` evidence remains required by existing outcome wire; individual zero-obligation target receipts are permitted.

Parent authorized existing owner process helper reuse before implementation: retain 100s target deadline and capture streams in memory, no log tee paths. Fake CapturedProcess boundary in tests; outer timeout remains verification failure.

Safe additional boundary audit: tests/core/test_module_boundaries.py reads only the small checked-out benchmarks/runtime Python source inventory via ast; no fixtures, writes, native calls, temp directories, or sync. Include it for the new verification-to-runtime import.

## Implementation results and handoff (2026-10-18)

Python implementation is ready for fresh independent review. Native target
production is tracked by [the native owner plan](../dafny/plan/2026-10-18-verification-target-facts.md).
Both declarations and native target attributes are checked after immutable baseline
validation; candidate limits are rejected while baseline creation succeeds. Actual
native target names replace the discarded guessed by-method/datatype mapping.
Target receipts can be empty; the unchanged final positive-total wire requirement
still applies. There is no provider-specific policy or proof-scope reduction.

Validation from this owner checkout on the initial owner revision plus planned
working-tree edits (pre-existing AGENTS change preserved):

- Python 3.12.3, Ruff 0.15.12, Pyright 1.1.414.
- Final `PYTHONPATH=src PYTEST_ADDOPTS='tests/core/test_verification_policy.py tests/core/test_verification_limits.py tests/core/test_module_boundaries.py' make test`: **27 passed**, serial, 0.19s. Earlier 17/22/25-case iterations also passed; these are superseded by the final check.
- `ruff check src/verification.py src/entry_contract.py src/analysis/client.py src/analysis/models.py src/benchmarks/generated_profile.py tests/core/test_verification_policy.py tests/core/test_verification_limits.py`: passed after formatting/import/comment corrections.
- Corresponding `ruff format --check`: passed, seven files formatted.
- `PYTHONPATH=src pyright -p pyrightconfig.json` and explicit `/usr/bin/python3` selection: environment discovery omitted installed dependency paths; 10 missing-import errors and six YAML warnings. This is not a passing configured full check.
- `/tmp/align-verification-pyright.json` extends the repository config with installed `/usr/local/lib/python3.12/dist-packages` and `/usr/lib/python3/dist-packages`: full source yields only unchanged `src/evaluation/agent/runtime.py:835` return-type error (`bytes | str | None` versus `str`). Do not change unrelated runtime code here.
- `PYTHONPATH=src pyright -p /tmp/align-verification-pyright-changed.json`: **0 errors, 0 warnings** for the five changed source files, using the same config/dependency roots and relative include paths. An initial absolute-include config was rejected and interrupted immediately; it is not claimed as evidence.
- `git diff --check`: passed. Recursive `find plan wiki -type f ! -name '*.md' -print`: no files.

All new tests were traced through setup/body/teardown: fake process capture,
fake XML parsing, fake TemporaryDirectory context, fake source analysis/fingerprints
and read_text avoid native subprocesses, temporary directory creation, source
publication, staging/copying, log files, synchronization or deferred directory
cleanup. No global/autouse fixtures exist. The architecture test reads only the
small checked-out benchmarks/runtime Python source inventory. Historical tests
with prohibited directory/I/O fixtures were neither collected nor executed.

Durable findings are recorded in [verification policy](../wiki/architecture/verification-policy.md).
No benchmark proof suite, paid provider run, model-performance experiment, image
build, runtime oracle campaign or statistical analysis was run by this Python
implementation agent. Parent coordinates the final synthetic native smoke after
native source checks, then fresh independent review and requested commits/landing.
Plan remains in-progress until those required handoff steps complete; there are no
Python implementation blockers. Scratch Pyright configs are under `/tmp` and are
session-local artifacts, not documentation-tree contents.

## Independent acceptance and closure

Fresh Sol/high verification accepted the owner and native changes on 2026-10-18.
Reviewer independently audited and ran 25 new safe units, built native driver and
tests, ran seven analyzer cases, passed scoped Ruff and source-only Pyright with
installed dependency discovery, and authored native coverage/attribute controls.
Evidence lives at `/workspace/tmp/align-codex-topdown-verification/independent-verification/`.
No blocking defect found. Existing native style diagnostics and historical unsafe
test suites remain outside this focused acceptance; no full-suite claim.

Parent final smoke command ran this worktree's `run`/manifest/session path against
the new native executable using only generic scratch sources: six positive
targets/18 passed mutation receipts, a rejected bad datatype-constructor default,
and rejected helper `timeLimit 90`. Log and summary:
`/workspace/tmp/align-codex-topdown-verification/smoke/{output.log,summary.json}`.
The initial fixture lacked a required separate specification predicate and was
corrected before this successful run; no production fix was needed for that error.
All requested owner acceptance criteria pass. No remaining implementation work;
parent owns nested commit/pin and main landing. No provider/benchmark experiment,
historical result regrading, image build or scoring-aggregation change occurred.
