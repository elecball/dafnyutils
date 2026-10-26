# Publish proof-reuse finalization capability

Status: done
Date: 2026-10-26
Owner: Dafnyutils public task contract
Parent: [Cosyn proof-reuse plan](../../cosyn/plan/2026-10-26-topdown-proof-reuse-final-build.md)

## Objective and acceptance

Publish an optional, strict `benchmark.dafny-proof-reuse.v1` capability on the
existing public verification check. It declares canonical proof roots and native
verification options plus explicit proof-scope and compile-only command vectors.
The owner command must describe the complete validated native target scope and a
source/manifest identity as JSON, and must compile only after validating the same
entry-contract identity before and after the build. The ordinary full verifier
and independent evaluator remain unchanged and continue to run all proofs.

Acceptance requires old `PublicCheck` JSON to serialize unchanged when the
capability is absent; strict rejection of unknown versions, malformed roots,
empty commands, invalid/empty scopes, ambiguous targets, forbidden bodyless
declarations, source changes and compile failures; release relocation of all
three public command vectors; and no `_verify_sources` call from compile-only
mode. Scope targets may individually produce zero native obligations, while the
trusted host must still require at least one conclusive obligation across the
complete final scope before reuse can finalize.

## Boundaries, evidence and compatibility

This is repository maintenance, not an evaluated run. The parent plan explicitly
authorizes the owner/wire change, proof reuse, final compile-only behavior and
focused commits. No package, live provider, native proof/analysis, build,
benchmark oracle, evaluator/scoring policy, task input or proof source changes are
in scope. Read-only `--version` and `definition-analysis --help` inspection was
later authorized to distinguish the two installed native revisions and confirm
proof-input support. Dafnyutils HEAD at inspection was
`40a53f1d8def113c4dba24ff6dbbf27189d6e7ba`. Existing changes to `plan/INDEX.md`,
the `dafny` and `coreutils` submodules, and `why-topdown-worklist-is-better.md` are
unrelated and must be preserved. Baseline records are under
`/workspace/tmp/topdown-proof-reuse-final-build/`.

Inspected existing solutions include `PublicCheck`'s strict Pydantic wire model,
`generated_profile._profile_payload`, release `_public_profile`, generated support
scripts, `EntryContractCheckSession.validate`, `individual_targets`, fixed native
options, and `run_full_session`. The validated session already binds the manifest,
project config, candidate sources, immutable support closure and verification
options; the new scope reuses those boundaries rather than creating a parallel
analyzer. The released workspace always supplies `bench/core`, so its declared
canonical options include the existing raw core library flags.

The user subsequently authorized the trusted Cosyn runtime to use its selected
Dafny producer for proof reuse even though it differs from the benchmark owner's
native executable. This is an explicit trust choice, not a claim that the two
binaries or translations are equivalent. The owner continues to validate its
own requested session tool for scope description and compile-only execution and
keeps its ordinary full build-and-verification route unchanged.

## Change table

| Files or symbols | Planned change and necessity | Validation |
| --- | --- | --- |
| `src/benchmarks/task.py` (`PublicCheck`, new proof-reuse DTOs) | Add the strict optional versioned capability, relative proof-root and argv validation, preserving omitted-field serialization for old checks. | Pure schema round trips and malformed payload rejection. |
| `src/benchmarks/generated_profile.py` (`individual_verification_rule`, `_profile_payload`) | Declare the execution source used by the native verifier as the proof root, canonical fixed native options, and explicit describe/compile script argv; update guidance to permit only this trusted-host alternative. | Generated payload assertions and option parity checks. |
| `src/evaluation/task/release.py` (`_public_profile`) | Relocate `describe_argv` and `compile_argv` with the same namespaced support directory as default `argv`. | Pure release-profile test. |
| `src/verification.py` | Share proof-scope validation and emit one strict JSON descriptor using the real validated targets and stable complete source identity. Add pre/post validated compile-only execution without proof verification. Preserve `run_full_session`; retain owner-session tool coherence without imposing cross-owner equality. | Fake session/build tests, malformed/empty/bodyless/ambiguous/change/failure cases, full-route regression. |
| `src/evaluation/task/scripts/verify.sh`, `src/evaluation/task/workspace.py` | Dispatch only explicit `--describe-proof-scope` and `--compile-only` modes and publish their fixed argv; keep no-argument full execution unchanged. | Generated-script and workspace protection assertions; no shell execution. |
| `tests/core/test_individual_verification.py`, `tests/core/test_proof_reuse_protocol.py`, `tests/core/test_verification_policy.py` | Add bounded, in-memory/fake-boundary behavior and wire coverage, including the unchanged full verifier's target order; no temporary directories, real subprocesses, sync, native tools or builds. | Focused serial pytest. |
| `docs/agent-protocol.md` | Document protocol version, exact descriptor/command semantics, trusted-host provenance and unchanged independent full evaluation. | Documentation/source review and diff check. |
| This plan and `plan/INDEX.md` | Record authorization, scope, exact commands, outcomes and handoff without overwriting unrelated index work. | Index consistency and recursive Markdown-only audit. |

## Validation plan

Before running tests, trace each selected test through fixtures and production
boundaries and exclude any path that creates a temporary directory, performs real
disk synchronization, launches native tools/builds or creates bulk files. From
`/workspace/dafnyutils`, run focused memory-only tests for the task schema,
generated profile, release relocation, proof-scope descriptor, compile-only path
and unchanged full dispatch. Then run scoped Ruff format/lint and mypy or the
repository-supported typecheck command if present. Run `make test-unit` only
after auditing its collected paths as safe; do not run integration or native
benchmark suites because this delegated task forbids native builds and the added
coverage uses fake boundaries. Also run `git diff --check`, inspect the exact
owner diff against the saved baseline, and inspect `plan/` and `wiki/`
recursively for non-Markdown files.

## Execution record and handoff

Consumer coordination fixed the exact capability keys as `protocol`,
`proof_roots`, `verification_options`, `describe_argv`, and `compile_argv`; the
scope descriptor keys are `protocol`, `source_identity`, `targets`,
`proof_roots`, and `verification_options`, with each target containing only
`source_path` and `symbol`. The static proof root is the workspace-relative
execution source passed to the native verifier, not the containing utility
directory.

Source and tests are frozen for independent review. The implementation adds the
strict optional DTO, publishes and relocates both explicit command vectors,
shares final scope validation with the full verifier, hashes the complete entry
snapshot, and performs one explicitly no-verify build between matching validated
identities. The no-argument full gate still calls `run_full_session` and its
complete native verification path. The describe route does not create the build
directory or invoke build-server cleanup.

From `/workspace/dafnyutils`, the following bounded checks ran with bytecode and
pytest cache writes disabled:

- `python3 -m pytest -c pytest-dev.ini -q -p no:cacheprovider tests/core/test_proof_reuse_protocol.py tests/core/test_individual_verification.py` — 50 passed.
- `python3 -m pytest -c pytest-dev.ini -q -p no:cacheprovider tests/core/test_verification_policy.py tests/core/test_verification_limits.py tests/evaluation/test_evaluation_oracles.py` — 44 passed.
- The two generated-script cases reran after the final trap placement change — 2 passed.
- Fresh review required compile-only to accept only the owner-generated
  `build --no-verify --output OUTPUT PROJECT [DEPENDENCIES...]` shape, rejecting
  mismatched tools and false, duplicate, compound or trailing option overrides
  before execution. It also required every described native target to pass the
  existing source/symbol suffix ambiguity selector. Nine fake invalid-command
  controls cover dash/colon/equal spellings, legacy slash options and response
  file indirection; a suffix-collision scope control was also added. A follow-up preserved
  the independent full verifier's original target order and acceptance by keeping
  strict selector checks confined to the optional descriptor; its existing test
  now asserts the actual ordered native calls. The final focused run passed 73
  proof-reuse, individual-feedback and full-policy cases, plus 31 remaining
  affected verification-limit and evaluator-command cases.
- Scoped `ruff check --no-cache`, `ruff format --check`, generated `bash -n`, and `git diff --check` passed.
- In the now-superseded exact native-tool revision, 77 focused proof-reuse,
  individual-feedback and full-policy cases passed, followed by the 31 affected
  verification-limit and evaluator-command cases. Scoped Ruff lint and format,
  `git diff --check`, and the recursive Markdown-only audit passed again. The
  native producer itself was inspected only through `--version` and
  `definition-analysis --help`; no proof, compilation or build ran.
- Root final review from `/workspace/dafnyutils` ran
  `PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=/workspace/dafnyutils/src PYTEST_ADDOPTS='-p no:cacheprovider' make test-unit`
  with 194 passed and 21 deselected, then `make test-integration` with 21
  passed and 194 deselected. The integration collection was audited as bounded
  process/fake coverage; it ran no native proof, build or benchmark oracle.
- Independent owner verification accepted that superseded exact-tool implementation with no
  remaining defect. It ran 94 owner-focused cases, 49 Cosyn memory-only
  finalization cases, scoped Ruff lint/format, strict malformed-contract
  matrices in both repositories, and a cross-process owner JSON to Cosyn parse
  and round trip. Diff and Markdown-only audits passed. Independent typing was
  unavailable because that environment could not resolve Pydantic/YAML sources.
- Following the user's explicit authorization for the trusted Cosyn runtime to
  select its own Dafny producer, the mandatory `native_tool` and
  `toolchain_sha256` wire fields, owner proof-input identity probe and temporary
  owner proof-input models were removed. `src/analysis/models.py` returned to
  HEAD. The existing `_validated_session_contract` still binds each owner scope
  or compile-only call to its requested session tool; the ordinary full route is
  unchanged. The reduced wire passed 73 focused cases and 31 affected
  verification-limit/evaluator cases plus scoped Ruff lint/format, staged and
  unstaged diff checks, and the recursive Markdown-only audit. Refreshed
  independent review accepted the reduced wire with no defect: 90 owner cases,
  48 current Cosyn memory-only finalization cases, a separate-process wire round
  trip, and 10/10 strict mutation rejections in each repository passed. The
  reviewer also confirmed `src/analysis/models.py` exactly matches HEAD and that
  the documentation makes no owner/Cosyn Dafny equivalence claim.
- Root's current reduced-wire unit gate passed 190 cases with 21 deselected in
  4.47 seconds. Its final 21 bounded integration cases were still running when
  this owner record closed; the parent record owns their final result.
- Scoped Pyright could not resolve the already installed `pydantic` and `yaml`
  packages in this environment (two import errors and two source warnings), even
  with `--pythonpath /usr/local/bin/python3`; it is not recorded as passing.

The earlier exact-tool revision completed the audited full unit and integration
gates; the reduced revision completed the current unit gate and refreshed
independent slices before this record closed. No native proof, compile, benchmark
oracle, Docker, live-provider or paid run occurred.
`docs/agent-protocol.md` is the durable public record for this wire and trust
boundary, so no separate wiki page is needed. The reduced-wire source, tests,
documentation and this plan are accepted and frozen. The parent owns refreshing
the staged blobs and index together, force-adding this ignored plan document,
recording the final bounded integration result, and creating the requested
focused commit.

Final reduced-wire parent integration gate: from `/workspace/dafnyutils`,
`PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=/workspace/dafnyutils/src
PYTEST_ADDOPTS='-p no:cacheprovider' make test-integration` passed21 cases,
190 deselected, in79.61seconds. This complements the final190-unit pass.
No native proof/build, oracle, provider or toolchain-equivalence result is claimed.
