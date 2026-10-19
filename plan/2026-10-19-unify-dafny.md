# Unify the two native Dafny revisions

Status: done
Date: 2026-10-19
Classification: repository maintenance; no evaluated run or paid provider access.

## Objective and acceptance

Use one native Git commit for `cosyn/dafny` and `dafnyutils/dafny`, preserving Cosyn body-visibility/trusted-source functionality and Dafnyutils verification-target discovery. Both parent gitlinks and the integration gitlinks must record the result. Strict consumer parsing must accept the combined producer. Preserve existing dirty documents, scratch, benchmark specifications, proof obligations, scoring, and isolation.

## Evidence and approach

Inspected native source, CLI flags, wire models, safe tests, Makefiles and applicable AGENTS/CLAUDE instructions. Cosyn starts at `4cd8162e968d8660ee50257671b697b7a4e64c89`; Dafnyutils starts at `4fb94fc9fecc8209e289148c6347a2c313606e6b`; common base is `bc427b21461f258fd8de34232e01bb6be03cee39`. The read-only synthetic merge reported 18 conflicts (3 product, 6 tests, 9 documents). Integrate linearly on the Cosyn native revision, porting the missing verification-target functionality and meaningful logger assertions. Preserve canonical logger API, resource-reporting cleanup and fixture positions. Retain both original native histories through existing refs; historical counterpart documents remain available at the original benchmark commit rather than overwriting canonical records. No merge commit or forced branch rewrite is needed; the benchmark checkout may detach at the common commit.

## Change table

| Owner / exact paths | Change and reason / unmet without it | Validation |
| --- | --- | --- |
| Native `Source/DafnyCore/DefinitionAnalysis.cs`, new `DefinitionAnalysis.VerificationFacts.cs` | Add optional verification target inventory while retaining body visibility and proof inputs; otherwise benchmark flag has no native producer | Fresh build, focused in-memory Core tests, combined CLI JSON |
| Native `Source/DafnyDriver/Commands/DefinitionAnalysisCommand.cs` | Preserve `--include-verification-facts` and compose with existing flags | Fresh Driver build and public synthetic CLI checks |
| Native `Source/DafnyCore.Test/DefinitionVerificationFactsTest.cs`, `Source/DafnyDriver.Test/JsonVerificationLoggerTests.cs` | Preserve benchmark cases against canonical APIs and exercise combined metadata without disk fixtures | Serial filtered native tests; trace setup/teardown first |
| Dafnyutils `src/analysis/models.py`, `tests/core/test_verification_limits.py` | Add local strict optional `bodyVisibility` schema and in-memory compatibility/error cases; otherwise producer JSON is rejected | Affected unit tests, Ruff, canonical Pyright |
| Native `wiki/unified-dafny-runtime.md`, `wiki/INDEX.md`; all owners `plan/2026-10-19-unify-dafny.md`, `plan/INDEX.md` | Record source ownership, integration decisions, actual evidence and preserved history | Diff/link review; Markdown-only trees |
| Cosyn `dafny`, Dafnyutils `dafny`, root `cosyn` and `dafnyutils` gitlinks | Pin the same committed toolchain and updated consumers | Exact native HEAD/gitlink equality; independent final review |
| Root `wiki/architecture/dafny-toolchain-ownership.md`, `wiki/INDEX.md` | Update current same-revision source policy while retaining separate command/isolation ownership and historical image receipts | Current source/pin inspection |

## Layers, risks and non-goals

Only native analysis metadata, associated tests, Python external JSON schema, documentation and Git pins change. No benchmark dataset, Dafny task source, proof specification, oracle, evaluator, scoring, provider policy or container boundary changes. Default trust remains absent; no verification bypass is added. Existing images are not relabeled or silently rebuilt. Fresh local binary/source checks are distinct from image admission and benchmark proof success. No dependency additions, push, paid experiment or full benchmark run is authorized/needed. Earlier local commit authorization applies. Git metadata mutations may require managed execution approval; request only through execution tooling. Existing incomplete plans and their index deltas stay unstaged.

## Validation

Prerequisites: .NET SDK 8.0.131 and existing offline project assets; Python 3.12 with existing dependencies. Logs/artifacts go to `/workspace/tmp/unify-dafny-20261019/`, never plan/wiki. In canonical native cwd, build Core.Test, Driver.Test, TestGeneration.Test sequentially with `dotnet build <project> --no-restore -m:1 -nr:false -p:UseSharedCompilation=false -v:minimal`; build actual CLI project if not referenced. Inspect/run supported `make format`, constrain any follow-up formatting to planned C# paths. Run relevant in-memory Core/Driver/TrustedSources tests with `dotnet test --no-build --no-restore --filter ...` serially and IPC approval if needed. After synchronizing the second checkout, build its `Source/Dafny/Dafny.csproj` with the same offline serial flags so both development command routes use new source. Use both fresh owner CLIs on a tiny public synthetic source for combined metadata and both independent Python parsers; no hidden tasks.

In Dafnyutils run `python3 -m pytest -c pytest-dev.ini -q tests/core/test_verification_limits.py`, then supported `make test-unit` after disk-boundary review. Run Ruff and canonical-source Pyright for affected Python. In root/Cosyn use supported `make lint`, canonical-source typecheck and affected fake units; integration only at final review if affected and safe. A fresh independent agent reviews current source from requirements and runs its own focused checks. Record exact commands, outcomes, scope/skips and current revisions here. Check staged diffs and both native SHA equality before local commits. Recursively inspect every root/submodule plan/wiki for non-Markdown files; preserve pre-existing violations.

## Progress and knowledge

Implementation and required scoped checks are complete. Durable findings are recorded in the native runtime and integration toolchain ownership topics; the closure below states actual source/runtime evidence and limits. No image, benchmark proof or paid experiment success is claimed.

Related plans: [integration](/workspace/plan/2026-10-19-unify-dafny.md), [Cosyn](/workspace/cosyn/plan/2026-10-19-unify-dafny.md), [Dafnyutils](/workspace/dafnyutils/plan/2026-10-19-unify-dafny.md), [native](/workspace/cosyn/dafny/plan/2026-10-19-unify-dafny.md).

### Checkpoints

- Canonical Core.Test and Driver.Test fresh offline serial builds passed, zero warnings/errors (.NET SDK 8.0.131). Initial VSTest launch aborted before tests because local IPC was denied; managed execution retry is used, without bypassing test scope.
- First verification-facts run passed the seven original cases; the new combined metadata case failed because its in-memory parser has no `SourceFiles` for the additional semantic fingerprint request. Remove that unrelated opt-in/assertion while retaining the planned visibility-plus-target-inventory assertion; no production behavior changes.
- Dafnyutils supported `make test-unit` with current source path and bytecode disabled passed 106 tests, 15 integration cases deselected. Root and Cosyn supported `make lint` passed (70 and 199 files). Canonical-source typechecks and remaining native gates are running.

- Root/Cosyn canonical-source Pyright passed with zero errors/warnings (existing source alias/configs from prior commit maintenance); stock editable import discovery is not treated as passing. The schema agent's scoped stock Pyright failed installed-package resolution; canonical mapped check follows. Its focused memory-only model module passed17 tests and Ruff.
- Second combined native test checkpoint exposed existing conservative visibility behavior: modern `@TimeLimit` syntax makes `revealsAllFunctions` conservative, so its precise-closure assertion was invalid. Use the existing legacy timeout syntax in the combined closure case; original modern-attribute inventory cases remain. No native product visibility change.

- Additional operational all-native-flags check passed raw JSON coexistence of semantic facts, proof inputs, target inventory and body visibility. Parsing that all-opt-in document with the benchmark's strict model rejected `sourceFacts.proofInputs`, which its client never requests; this is outside its supported request contract. Keep each consumer's optional request schema: benchmark target-inventory document and Cosyn proof-input document both parse successfully using the same canonical CLI. No `extra` relaxation or unrelated schema expansion.

## Delivery checkpoints

The native common commit is `10dca3ba4a2909c11299176440401fc31413b53d` (one parent, Cosyn original HEAD); its initial unpublished form `102726aeb` was amended only to remove a stale preimplementation status paragraph found by independent review. No product source changed after the native gates. Both native HEADs now match the final commit. The benchmark original `expecto` ref remains `4fb94fc9fecc8209e289148c6347a2c313606e6b`. Native checkout transfer was local-only. Its wiki INDEX merge conflict was resolved over the common committed index while preserving the original user-added overflow entry unstaged; no original work was reset/stashed/removed. The canonical native overflow entry and both untracked overflow plans remain untouched.

Native source was freshly built/tested/formatted; independent source verification passed90 native checks (8inventory,22visibility,21proofinputs,3trigger,12match-trigger,6logger,3internal-error,15trustedsource), no skips. Implementation checks separately passed54; these overlap the independent90 and must not be added as distinct scenarios. Full native/Docker/provider/benchmark suites were not run. Initial local VSTest socket denial was retried through managed execution. Four pre-existing TestGeneration build warnings and formatter workspace-loading warning are retained in the native record. Two combined test-fixture corrections are documented there.

Dafnyutils `PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=/workspace/dafnyutils/src:/usr/local/lib/python3.12/dist-packages make test-unit` passed106, with15integration cases deselected. Focused model module17 passes (also independently). Exact model/test Ruff lint+format and diff checks pass. Canonical-source Pyright passes for the production model; a mistaken initial absolute include selected no files and was corrected before the real gate. Existing test module Pydantic alias typing reports19 errors, reproduced identically on the HEAD baseline, and is not claimed passing. No unrelated alias-helper repair was made.

Root/Cosyn supported `make lint` pass; existing canonical-source Pyright configurations report0errors/0warnings. Root dependency boundary units passed2 (`tests/unit/test_repository_boundaries.py`); Cosyn path/model units passed43 (`tests/common/test_path_models.py`), with source alias, installed dependency paths, bytecode disabled and cacheprovider disabled. No root/Cosyn Python product source changed, so their full earlier suites were not repeated. Final affected process integration consists of the two-owner client smoke rather than unrelated lifecycle suites.

Both Python clients successfully consumed the canonical fresh CLI using a public synthetic source:4definitions,4verification targets (including constructor),2proofinput entries, semantic facts and body visibility. Native all-option raw JSON also composes. Strict consumers keep their supported optional field subsets; an initial default benchmark-route probe before rebuilding it correctly failed the visibility assertion, and the canonical override passed.

Post-commit builds of both owner CLIs passed (0warnings/errors,34.21sCosyn/32.40sDafnyutils) for the intermediate documentation revision. Because CLI version includes Git SHA, final revision-metadata builds are required after the documentation-only amend; those and final default-route smoke are pending. Logs/artifacts: `/workspace/tmp/unify-dafny-20261019/`; no generated artifacts enter plan/wiki.

## Final closure

Both final native HEADs and both parent gitlinks in the accompanying local commits use `10dca3ba4a2909c11299176440401fc31413b53d`. The integration commit records those parent commits. This owner's source/pin work is complete; cross-owner delivery is recorded by the integration plan. No merge commit or push was created. Existing unfinished plans, index entries, coreutils generated scratch, and unrelated root scratch remain unstaged.

Final revision-metadata CLI builds passed from both owners with zero warnings/errors (Cosyn33.79s, Dafnyutils33.59s), same offline serial/deterministic command flags as above. `PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=/workspace/tmp/organize-current-cosyn-commits/source:/workspace/dafnyutils/src:/usr/local/lib/python3.12/dist-packages python3 /workspace/tmp/unify-dafny-20261019/final-smoke.py` passed using both default commands. `dafny --version` and `dafny-benchmark --version` both report `4.11.1+10dca3ba4a2909c11299176440401fc31413b53d`. Each actual route emitted all four metadata families together; native target inventories matched. Cosyn's own proof-input request and benchmark's own verification-target request both passed their strict Python models, including effective opacity/reveal metadata. This is local runtime contract evidence, not a benchmark proof or image receipt. Final summary/raw JSON/log: `final-runtime-smoke.json`, `dafny-combined-native.json`, `dafny-benchmark-combined-native.json`, `final-smoke.log` in task scratch.

Knowledge: [native runtime](/workspace/cosyn/dafny/wiki/unified-dafny-runtime.md), [integration toolchain ownership](/workspace/wiki/architecture/dafny-toolchain-ownership.md#unified-source-revision-2026-10-19). Parents link these owning records instead of duplicating a new wiki topic. Recursive root/owner plan/wiki checks found no non-Markdown artifacts; staged diffs and source-boundary checks pass. Existing image identities are historical and require normal owner image builds for a future evaluated run. No remaining source/pin blocker; next action outside this task is the separately selected work/experiment, with its own image and paid-run gates.
