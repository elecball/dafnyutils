# Provide individual verification to normal Codex

Status: done
Owner: Dafnyutils benchmark feedback and public task delivery.
Related [root plan](../../plan/2026-10-19-codex-individual-verifier.md).

## Objective and acceptance

Provide generated, protected `eval_support/verify-target.sh --list` and
`--source PATH --symbol FULL_NAME` for exact native target discovery and scoped
feedback. Reuse validated entry contracts, native names, fixed mutation/limit
policy, TRX failure handling and source identity checks. Scoped success cannot
satisfy the mandatory full public/final gate. Reject invalid, ambiguous, outside
or protected selectors, missing/failed evidence and policy overrides. Deliver the
helper under root and namespaced support layouts; advertise optional guidance.

Non-goals: change final proof scope, scoring, benchmark inputs, Cosyn, packages,
existing releases, paid providers or deployed images. User authorized patch and
scoped commits; root agent handles commits. Preserve existing dirty owner tests,
pricing, instructions and documentation index entries.

## Inspected evidence and existing solutions

Repository maintenance, not evaluated run. Inspected owner/root instructions,
Makefile, pytest-dev.ini, pyproject, current plan/wiki indexes and verification
policy knowledge. Owner main `63d5f7e`, production files clean; unrelated tests,
AGENTS.md, pricing and plan/wiki indexes already dirty. `src/verification.py`
provides `_verify_target`, verification options and session validation;
`entry_contract` restricts native targets to reachable editable sources and rejects
candidate declaration limit overrides. Workspace script names control generation
and protection. Existing safe policy tests fake storage/process/TRX parsing.

## Change table

| File/symbol | Change and reason | Validation |
| --- | --- | --- |
| `src/verification.py` | Add isolated individual CLI, exact target discovery/selection and scoped receipt using existing runner; detect native suffix collisions and use absolute source filters only for scoped feedback | In-memory selection/policy/failure/source-change and native collision tests |
| `src/evaluation/task/scripts/verify-target.sh` | Add no-build public wrapper with fixed runtime/manifest; source/symbol flags only | Fake generated delivery and bounded shell/native smoke |
| `src/evaluation/task/workspace.py` | Register helper for both generation and immutable protection | Fake specification tests for both layouts |
| `src/benchmarks/generated_profile.py` | Add optional public usage guidance through support-directory-aware rule factory, preserve mandatory full check | Structured public check contract test |
| `src/evaluation/task/release.py` | Bind only individual guidance rule to namespaced release support directory | Fake public-profile/generated-helper coherence test |
| `tests/core/test_individual_verification.py` | Add behavioral units with fake filesystem, process, report and analysis boundaries | Focused serial pytest |
| `plan/2026-10-19-codex-individual-verifier.md`, `plan/INDEX.md` | Record execution/provenance and handoff | Diff/link review |
| `wiki/architecture/individual-verifier.md`, `wiki/INDEX.md` | Durable usage/scope finding; add only own index entry | Markdown/diff audit |

Layers: benchmark-owned feedback and delivery only, no specification, proof,
evaluator final-gate, oracle, dataset or scoring changes. No integration dependency.

## Validation and risks

Working directory `/workspace/dafnyutils`: run
`python3 -m pytest -c pytest-dev.ini -q tests/core/test_individual_verification.py tests/core/test_verification_policy.py tests/core/test_verification_limits.py`
after tracing all boundaries. Run scoped Ruff check/format and Pyright on changed
sources; Makefile has no lint/type target. Owner-wide make test requires reviewing
remaining fixtures before use; do not run prohibited historical I/O tests. Native
tiny synthetic maintenance smoke under `/workspace/tmp/codex-individual-verifier/`
will be performed by root/fresh review, with no benchmark solution/provider.

Primary risks: accepting prefix or protected target, confusing scoped/full wire,
CLI flags changing full checks, lost native names, source changes while proving,
and missing TRX evidence. Tests cover these boundaries. Fresh independent review
and root composition/commit remain root responsibilities.

## Execution and handoff

Ready plan announced before implementation; no blocking question or approval.


### Implementation and local verification

Implemented optional helper and native selector/session/CLI in planned files.
Wrapper strictly accepts list or `--source PATH --symbol FULL_NAME`; candidate
flags cannot override fixed task configuration. Uses a distinct target outcome
wire for success and failure. Zero obligations are explicit non-verified feedback,
not missing-report success. Existing full runner and final scoring are unchanged.

Working tree: owner main `63d5f7ed989d577157704e581ae090fa70b6f6b1` plus this
change and pre-existing unrelated dirty work. Python 3.12.3, Ruff 0.15.12,
Pyright 1.1.414. Commands from `/workspace/dafnyutils`:

- `python3 -m pytest -c pytest-dev.ini -q tests/core/test_individual_verification.py tests/core/test_verification_policy.py tests/core/test_verification_limits.py`: **53 passed** (0.32s); no temporary-directory creation/native subprocesses. All new process/storage/report paths are in-memory fakes. Generation reads five fixed small script templates per layout; configuration/scaffold/analysis are faked. No copy/build/sync cleanup paths run.
- `ruff check --no-cache src/verification.py src/benchmarks/generated_profile.py src/evaluation/task/workspace.py tests/core/test_individual_verification.py`: passed.
- `ruff format --check src/verification.py src/benchmarks/generated_profile.py src/evaluation/task/workspace.py tests/core/test_individual_verification.py`: all four files formatted.
- `pyright src/verification.py src/benchmarks/generated_profile.py src/evaluation/task/workspace.py`: **0 errors, 0 warnings**.
- `git diff --check`: passed.

Initial focused run exposed literal `$@` colliding with the shell template's `@`
delimiter, plus a missing fake profile path. Corrected template to `$@@` and fake
contract; rerun passed. No production fallback or policy change was introduced.

Durable usage/scope knowledge recorded in [individual verifier wiki](../wiki/architecture/individual-verifier.md).
No provider experiment, benchmark suite, image build or proof claim. Owner
Makefile has no static-check target; scoped installed tools used. Full owner
unit/integration validation and native synthetic controls are deferred to root's
fresh independent review/handoff so final integration is run once after source
settles. New tests are serial units with fake external boundaries; no changes to
existing tests or unrelated dirty records.

Remaining: root/fresh verifier runs tiny native positive/negative/unknown target
controls and final checks, inspects generated executable delivery, updates evidence
and final status, then makes scoped owner/root commits. No local commits/staging.

Final owner audit: `find plan wiki -type f ! -name "*.md"` returned no files;
`git diff --check` passed. New plan/wiki pages are ignored by repository patterns
and need explicit scoped force-add if committed; existing index edits preserve
all pre-existing entries.


### Independent review corrections (scope recorded before edits)

Fresh reviewer found native `--filter-symbol=A.Check.` matches both `A.Check`
and `Other.A.Check`: native filter uses a suffix match, not exact identity.
Also relative source suffix filters could include a nested source path. Add a
scoped ambiguity check over the validated native target surface and use an
absolute resolved source filter for scoped checks only. Reject target matches
that would include another same-source suffix name. Keep complete/full runner
filter semantics untouched. Fake regression tests model nested names and paths;
fresh reviewer reruns independent native controls.

The reviewer also found public release packaging namespaces only public check
commands, leaving optional rule guidance rooted incorrectly. Add
`src/evaluation/task/release.py` to scope and expose a support-directory-aware
rule factory in `src/benchmarks/generated_profile.py`; release packaging rebuilds
only the individual guidance rule with its actual support directory. Add a fake
structured coherence check linking that directory to the delivered protected
helper. No schema, benchmark contract, compiler or final-gate behavior change.


### Correction verification and accepted handoff

Implemented both review corrections. Native source-filter override is optional
and used only by the individual path; full runner behavior remains unchanged.
Symbol suffix collisions fail before starting a proof process. Absolute source
suffix ambiguity is also rejected across known analysis/utility/native-target
paths, including protected analysis inputs. Native behavior confirmed by source
inspection at `dafny/Source/DafnyDriver/CliCompilation.cs:349` and `:371`.
Released guidance is rebuilt through `individual_verification_rule` with its
actual support directory; fake structured checks tie that directory to generated
protected helper files and preserve other public rules/check definitions.

Updated local commands in `/workspace/dafnyutils`:

- Focused serial pytest command above: **58 passed** (0.32s); five new regression cases model native symbol/source suffix collisions, unique longer identity, and namespaced guidance coherence. No new real storage/process boundaries.
- Scoped Ruff check and format on `src/verification.py`, `src/benchmarks/generated_profile.py`, `src/evaluation/task/workspace.py`, `src/evaluation/task/release.py`, `tests/core/test_individual_verification.py`: passed.
- `pyright src/verification.py src/benchmarks/generated_profile.py src/evaluation/task/workspace.py src/evaluation/task/release.py`: default environment reports existing direct `pydantic` import unresolved in release.py. Actual installed package is `/usr/local/lib/python3.12/dist-packages/pydantic`; no code/dependency edit needed.
- `pyright --project /workspace/tmp/codex-individual-verifier/pyright-individual.json`: **0 errors, 0 warnings** with explicit existing dependency path and only the four changed source files included. An initial scratch config used unsupported absolute includes, so Pyright ignored them and scanned unrelated scratch files; corrected relative includes give the scoped result above. That discarded invocation establishes no code claim.
- `git diff --check` and recursive plan/wiki non-Markdown inventory: passed/empty.

Fresh independent reviewer accepted the corrected implementation and independently
passed the 58 focused cases. Root reports owner `make test-unit`: **101 passed,
15 deselected**, and root `make test`: **123 passed, 19 deselected**. The first
root eight-control native smoke passed; root's corrected-scaffold rerun remains
pending at this handoff and is not claimed as complete here. Independent native
evidence/final integration and scoped commits are owned by root/reviewer.

Task files for scoped owner commit: `src/verification.py`,
`src/benchmarks/generated_profile.py`, `src/evaluation/task/workspace.py`,
`src/evaluation/task/release.py`, `src/evaluation/task/scripts/verify-target.sh`,
`tests/core/test_individual_verification.py`, this plan,
`wiki/architecture/individual-verifier.md`, and only this task's prepended lines
in `plan/INDEX.md` and `wiki/INDEX.md`. No other edits or local staging/commit.


Final root handoff confirms corrected-scaffold native **8/8 controls passed**
after suffix/source-filter corrections; evidence:
`/workspace/tmp/codex-individual-verifier/native-probe.log` and
`/workspace/tmp/codex-individual-verifier/native/summary.json`. Fresh independent
review ACCEPT, 58 focused units, owner 101 units and scoped source typing/lint
satisfy owner acceptance. Plan is done; root owns remaining integration records
and the authorized scoped owner/root commits. Source changes are settled.
