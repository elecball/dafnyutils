# Knowledge index

- [Individual public verification feedback](architecture/individual-verifier.md) — exact native list/check helper, fixed policy and scoped receipts; 58 focused/101 owner units, static checks and 8 native controls pass; fresh independent review accepted ([plan](../plan/2026-10-19-codex-individual-verifier.md)).

- [Development test I/O and execution tiers](development-test-io.md) — current strict temporary-directory cleanup independently accepted; removes 187 functions/10 whole modules and retains 49 unchanged functions; 43 unit/15 integration cases pass; no live Docker tests remain ([current plan](../plan/2026-10-16-remove-temp-directory-tests.md)). Earlier static-only cleanup removed 50 support-tree-copy/forced-sync consumers ([follow-up](../plan/2026-10-16-remove-indirect-io-tests.md), [earlier I/O plan](../plan/2026-10-15-ban-io-bound-tests.md), [tier plan](../plan/2026-10-15-classify-test-tiers.md)).

- [Dafny declaration coverage and source extraction](architecture/declaration-analysis.md) — verified 2026-10-07; parser/AST inventory, aliases/types/containers/fields/exports, clone identity, source groups, public extraction and proof boundaries; all 47 releases/restorations and Paste proofs passed.

- [Public verification runtime](architecture/public-verification-runtime.md) — protected `.codex` mountpoint preparation verified 2026-10-05 (native startup, five permission boundaries, independent 39 focused tests); direct protected preparation independently verified (2026-10-04), earlier write grants and temp-storage workaround historical.

- [Utility upstream test provenance](upstream-test-provenance.md) — task-scoped GNU marker contract, selected trusted module, local and independent validation, and current metadata failures.

- [Shared IO API consolidation](io-api-consolidation.md) — `ReadFile(path)` without read mode since 2026-10-06; canonical file, standard-stream and directory interfaces; approved native observation migration; all 36 complete proof closures, native/runtime checks and independent review pass.

- [GNU LS output column populations](architecture/ls-output-columns.md) — numeric alignment, failed rows, exact dirent kinds, raw-dot order and lexical operand paths; owner and independent full closures, six direct surfaces, and runtime gates pass.

- [Fuzzer fixture symlink aliases](architecture/fuzzer-fixture-topology.md) — root confinement and relative target resolution for hardlink aliases of symlinks, with local Rust validation evidence.

- [Paste diagnostic quoting](architecture/paste-diagnostic-quoting.md) — historical backslash correction verified 2026-09-26; current broader rendering is documented in GNU diagnostic quoting.

- [Fuzzer failure input evidence](architecture/fuzzer-failure-inputs.md) — verified locally 2026-09-26; private input bundles for case execution errors.

- [Utility test boundary](architecture/utility-test-boundary.md) — verified locally 2026-09-25; evaluator cases depend on observable contracts, not private helpers.

- [Public task release resource contract](architecture/public-release-resources.md) — Paste inline-type workaround superseded by the native declaration audit (2026-10-07); historical release/proof evidence retained. Release mutability declared only by protected files (2026-10-04); structured-publication section and removed mv-test evidence historical.

- [Agent protocol ownership](architecture/agent-protocol.md) — current v2/v7 wire and candidate lifecycle; controller identity, post-stop handoff, bounded capture and readonly cleanup independently checked2026-10-14. Child FIFO/socket no-open handling independently accepted2026-10-15 with22focused cases and real-FIFO guard probes; exact historical r02 object remains unknown. Historical Vero sections remain stale.

- [Candidate verification policy](architecture/verification-policy.md) — prospective shared mutation/limit gate, native target coverage and declaration-limit enforcement; local and fresh independent checks accepted, with native synthetic evaluator smoke ([plan](../plan/2026-10-18-align-codex-topdown-verification.md)).
