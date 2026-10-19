# Plans

- [Commit test cleanup and cached-input prices](2026-10-19-commit-test-cleanup-and-cache-prices.md) — done; `ef00dc3` and `ca0e7f1` created locally with exact requested subjects; independent static/configuration checks passed; nested repositories and unrelated records excluded, no push.

- [Provide individual verification to normal Codex](2026-10-19-codex-individual-verifier.md) — done; protected native-target helper; fresh review accepted, 58 focused/101 owner units and 8 native controls pass; [root plan](../../plan/2026-10-19-codex-individual-verifier.md).

- [Add verified cached-input prices to the report price file](2026-10-18-cached-input-prices.md) — done; optional `cached_input_per_1m` for gpt-6-luna/sol/astra in `model-cost.yaml`; [root plan](../../plan/2026-10-18-cache-aware-median-cost.md).

- [Require concise problem/fix commit message bodies](2026-10-16-concise-commit-messages.md) — done (`5da26fd`, local); commit bodies are three to four sentences on the problem and fix and name affected benchmark layers, without validation content; [root plan](../../plan/2026-10-16-concise-commit-messages.md).

- [Remove temporary-directory development tests](2026-10-16-remove-temp-directory-tests.md) — done (fresh independent review accepted); 187 direct/indirect temporary-directory test deletions across 21 modules, including 10 whole-module deletions; 49 unchanged retained test functions; 43 unit and 15 final integration cases pass; corrected pre-existing packaging-module deletion attribution.

- [Remove indirect disk-I/O development tests](2026-10-16-remove-indirect-io-tests.md) — done (independent static review); 50 support-tree-copy/real-sync consumers removed, 236 retained tests unchanged; AST, cache-free lint/format and reference checks pass. No pytest/collection/build execution.

- [Commit the Dafnyutils working tree in logical units](2026-10-15-commit-working-tree.md) — done; D1-D6 `7f8260d..6d30dc3` local, independently verified (73 unit passed; integration 15 passed on the working tree); root pins `6d30dc3`; push deferred; [root plan](../../plan/2026-10-15-commit-working-trees.md).

- [Classify development tests by execution weight](2026-10-15-classify-test-tiers.md) — done (independent static review); separate serial units from explicitly final-only process/native/workflow integrations while preserving `make test TASK=<utility>` benchmark oracle semantics.

- [Ban disk-I/O-bound tests](2026-10-15-ban-io-bound-tests.md) — done; removed 12 bulk-copy, deep-tree, and real compiler/build-tree development tests; added the setup/body/teardown disk-I/O prohibition with tiny-fixture allowance; AST, cache-free Ruff, and whitespace checks passed, while pytest/build/proofs were intentionally not run.

- [Preserve results across transient IPC metadata handoff](2026-10-15-handoff-transient-ipc.md) — done; native .NET FIFO trigger and child-only no-open skip independently accepted. Local22 and independent22 focused cases, independent real-FIFO guards, scoped Ruff/Pyright pass; exact old r02 child remains unobserved. Image admission is integration-owned.

- [Remove stopped-agent read-only control projections](2026-10-14-shared-control-cleanup.md) — done;89fresh source controls and actual immutable-image normal/forced gates pass automatic readonly control cleanup, with zero inference/manual cleanup. Unchanged typing limitation is retained; task/scoring/model and paid settings remain fixed.

- [Declare trusted harness execution identity](2026-10-14-shared-harness-execution-identity.md) — done; explicit controller capability and bounded post-stop handoff/capture; independent74owner/35root checks and immutable-image normal/forced-stop admission passed without intervention; algorithm results owned by integration.

- [Align container Z3 with the current native Dafny toolchain](2026-10-13-update-z3-containers.md) — done; task/evaluator and standalone devcontainer images independently accepted with Z3 4.16.0, owner-local startup/scratch behavior verified.

- [Audit Dafny declaration coverage](2026-10-07-declaration-analysis-audit.md) — done; latest expecto fetched, parser/AST inventory and native/public-source fixes; 4 native and 195 Python checks, all 47 releases/restorations and 1,641 Paste proofs passed; original alias restored.

- [Repair Paste public task type resolution](2026-10-06-paste-release-type-alias.md) — historical inline workaround superseded by the 2026-10-07 native declaration audit; original evidence retained.

- [Disable tac and remove the tac-specific file read mode](2026-10-06-disable-tac-seek-read.md) — done; tac deleted (backup in /workspace/tmp/disable-tac) and demoted to a candidate, `ReadFile(path)` without mode, fold proof guidance; core and 14 utilities verified independently.

- [Rebase-only branch integration](2026-10-04-rebase-only-integration.md) — done; two-sentence rebase-only rule in CONTRIBUTING.md and AGENTS.md (shortened at user request); enforcement via GitHub settings not included.

- [Unify protected workspace permissions](2026-10-04-unify-protected-workspace-permissions.md) — done; direct protected preparation independently reviewed, 284 non-benchmark checks and static gates passed.

- [Count-only agent result wire](2026-10-04-count-only-agent-result.md) — done; current v7 count-only with no compatibility reader; fresh independent owner checks passed.

- [Use run-scoped /tmp and declare only protected release files](2026-10-04-allow-tmp-protected-files.md) — done; workaround removed, protected-only classification identical for 47 tasks, native cold .NET and public build pass.

- [Remove Vero-derived structured-task and public-check support](2026-10-04-remove-vero-derived-support.md) — done; fresh independent 90 focused/286 full checks and static gates pass, exact public-runtime/scaffold source inventory retained, Vero symbols removed; concurrent documentation and coreutils evidence limits disclosed.

- [Editable specification-free task scaffolds](2026-10-03-editable-scaffolds.md) — done; source-derived editing scopes verified by 352 owner and fresh independent release/mount/archive checks.

- [Candidate public verification runtime](2026-10-02-public-verification-runtime.md) — done; mounted write grants, authentic initialization and workspace temporary storage passed native and independent checks.

- [Trusted public-check diagnostics](2026-10-02-public-check-diagnostics.md) — superseded (2026-10-04, reverted; ownership moved to vero-dafny); historical evidence retained.

- [Structured library public tasks](2026-10-01-structured-public-tasks.md) — superseded (2026-10-04, reverted; ownership moved to vero-dafny); historical evidence retained.

- [Remove unused audit tests](2026-09-30-remove-unused-audit.md) — done.

- [Remove unused bench tests](2026-09-30-remove-unused-bench-tests.md) — done; later complete owner gate resolved the previous clock-observer blocker.

- [Flatten benchmark support](2026-09-30-flatten-benchmark-support.md) — done; helper flattened, algorithm runtime testcase evaluation removed by explicit authorization, owner and independent checks passed.

- [Restore task-level upstream marker checks](2026-09-30-task-upstream-markers.md) — done; selected task preflight and independent checks pass, with 25 existing module annotation failures recorded for separate repair.

- [Align candidate and Top-down verification](2026-10-18-align-codex-topdown-verification.md) — done; shared mutation/limit policy, native coverage and candidate override enforcement accepted by local and fresh independent checks; parent owns commit/landing.

- [Commit existing native changes in logical units](2026-10-19-commit-native-working-trees.md) — done; local commit maintenance, no push.

- [Unify native Dafny revisions](2026-10-19-unify-dafny.md) — done; both native pins and default commands use10dca3ba4a29; strict consumers and independent90-case native gate accepted.
