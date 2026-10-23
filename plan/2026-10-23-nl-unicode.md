# Correct nl separator UTF-8 semantics

Status: done for the isolated Dafny implementation and proof scope. Date: 2026-10-23. Maintenance, not an evaluated run.

## Authorization and acceptance

The user explicitly authorizes fixing the nl Unicode separator issue in both
Dafnyutils and Leanutils. Preserve the complete separator text domain; encode
text using the existing UTF-8 helper rather than narrowing to byte characters.
Numbered output uses the encoded separator bytes. Unnumbered output uses six
number-field spaces plus the encoded separator byte count. Preserve body bytes,
numbering, delimiters, modes, native errors and frames.

Inspect GNU source: coreutils/src/nl.c prints separator_str at line 300 and
computes unnumbered width with lineno_width + strlen(separator_str) at 618-621.
Thus under the model's external UTF-8 text semantics the relevant width is byte
length, not character count. No upstream build or oracle dataset is required.

## Design and change table

| Owning repository / files | Change and reason | Validation |
| --- | --- | --- |
| Dafny bench/utils/nl/NlSpec.dfy | LineNumberText encodes separator with existing Utf8.Encode; BlankPrefix uses encoded byte length | Focused function checks, complete supported nl verification |
| Dafny NlCore/NlProof if actually needed | Retain existing reuse of Spec.LinePrefix; add only necessary proof guidance | Direct RunCore ==> Spec closure, no new trust/skip |
| Dafny bench/utils/nl/nl.md | State UTF-8 separator bytes and unnumbered six-plus-byte-count width in existing utility scope | Documentation/source comparison |
| Dafny tests/core/nl_utf8_separator.dfy | Tiny ghost regressions for observable prefix bytes and blank widths | Whole regression file verified |
| Lean Nl/Spec/Contract.lean | Exact UTF-8 output relation replaces impossible raw-character witness; byte-count blank width | Focused elaboration and general witness theorem |
| Lean Nl/Impl/Run.lean | Encode separator; preserve state monad and existing algorithm | Concrete numbered/unnumbered rendering checks |
| Lean Nl/Proof/** | Prove corrected prefix relation for arbitrary text; bounded empty/ASCII/Latin/CJK/non-BMP/mixed cases | Kernel checked supporting proofs, no new holes |
| Lean status.csv and current docs/wiki | Remove the resolved representability obstacle, retain pending full run_correct honestly | make check including source and compiled axiom audit |
| Dafny wiki/nl-utf8-separator.md and wiki/INDEX.md | Record reusable GNU byte-width semantics and proof scope | Link/content checks and Markdown-only audit |
| Both plan/index records | Source version, scope, commands, evidence, preservation and delivery | Markdown-only audit and final diff review |

No new dependency, fuzzer, evaluator, dataset, scoring, shared runtime policy,
CLI domain restriction or trust annotation. Full Lean nl correctness remains
pending if not easy; the Unicode-specific gap must be discharged without holes.
Do not change AGENTS.md. The existing user-authorized Proof-only hole exception
continues to apply to existing hard main correctness obligations.

## Source state and preservation

Dafny main is 09309b7 with extensive pre-existing dirty work, but nl source files
and core Utf8 are clean. Use an independent source worktree based on that commit,
then apply only the reviewed nl changes to main and fast-forward the resulting
commit while retaining all other working-tree bytes. The prior source ghost
provider repair/chunk adaptation must remain intact. Lean main starts at
f1104d7, clean and synchronized with origin/main.

Read root/repository instructions, DAFNYSTYLE, bench rules, relevant specs/core,
existing UTF-8 helpers and supported Make targets. No evaluated-run material,
private oracle/reference tests or evaluator-only sources are permitted.

## Verification

Dafny 4.11.1 existing official project binary, supported nl Make verify target
with absolute isolated-worktree PYTHONPATH. Verify corrected functions, bounded
ghost examples and RunCore's original Spec postcondition. No new packages or
native rebuilds. Lean 4.35.0/pinned Mathlib; serialize Lake/probes with
/workspace/tmp/leanutils-port/utility-implementation/lake-build.lock.
Run focused nl builds and bounded checks, then supported make check and relevant
in-memory tooling checks if the status tooling changes. Use fresh independent
review of both implementations/specifications. No broad repeated checks after a
passing result without a new relevant change.

Scratch/logs: /workspace/tmp/leanutils-port/nl-unicode/. Experiments run in tmux;
record command, source state, versions, outcome and exact proof scope. Required
Git hooks apply to source commits; create them in the clean isolated source
worktree so formatting cannot affect unrelated main changes.

## Progress

Dafny implementation, bounded regression, complete supported closure verification,
parent source review and scoped documentation are complete. The owning task
handles Lean and main-worktree integration. The mandatory commit hook gates the
authorized source commit; its actual output and exit status are retained outside
the repository at the artifact path below.

## Isolated Dafny implementation scope

Worktree: `/workspace/tmp/leanutils-port/nl-unicode-dafny`; branch
`fix/nl-utf8-separator`, baseline `09309b7d078f555ea57060d781fd70f7e25c457f`.
This worktree implements only the two NlSpec functions, the tiny Dafny regression,
and scoped plan/wiki documentation. Root task owns Lean and final integration.
The existing `/workspace/dafnyutils/dafny/Binaries/Dafny` tool reports
`4.11.1+5fa47c6e949dad736db25e02b5edad95d0b0be1a`.

Planned commands from this worktree: `dafny-benchmark verify
tests/core/nl_utf8_separator.dfy --standard-libraries:false --library:bench/core
--allow-warnings --isolate-assertions --verification-time-limit:30
--boogie=/randomSeed:42`, then `PYTHONPATH=<absolute-worktree>/src
make -C bench/utils/nl verify`. Both run in tmux and preserve logs/status beneath
`/workspace/tmp/leanutils-port/nl-unicode/`. The supported target checks the
original direct RunCore postcondition and all its candidate closure.

## Dafny verification progress

The two corrected functions passed the focused source-line check: 2 assertions
verified, 0 errors; exit 0 (`dafny-spec2.log`). The first comma-separated symbol
filter selected zero obligations and is not verification evidence (`dafny-spec.log`).
The ghost regression initially failed concrete constant folding while its
arbitrary-text lemma passed. Bounded local function fuel for `RepeatChar` and
`Encode` resolves finite constant expansion; an invalid equal-low/high fuel
attempt was rejected before verification. The mixed case additionally uses local
assertions naming exact encoded bytes and the number field. No time limit, core
contract, trusted assumption, or verification scope changed. All failed attempts
remain available in numbered `dafny-focused*.log` files beneath the artifact path.
The complete supported verification is running in session
`nl-dafny-full-20261023`; no passing result is claimed yet.

Focused regression pass: `dafny-focused4.log`, exit 0, 226 verified and 0 errors.
No Core or Proof file changes were necessary. The source entry `Nl.RunCore`
passed its existing direct `NS.Spec` postcondition during supported target step
6/40; the remaining closure targets are still running. The regression was then
formatted with `dafny-benchmark format tests/core/nl_utf8_separator.dfy` (format
only; no changed proof obligations). Reusable semantics are recorded in
[the scoped wiki page](../wiki/nl-utf8-separator.md).

Scope update: the owning task explicitly requested updating the existing nl scope
bullets to name UTF-8 encoding and blank byte width. The source code design has
passed the parent review; no Core/Proof adjustment is required. Conditional commit
authorization is granted after all 40 supported verification targets pass; run the
required repository hook and commit all scoped source/docs/plan/wiki files.

## Final source result and handoff

Completed files: `bench/utils/nl/NlSpec.dfy`, `bench/utils/nl/nl.md`,
`tests/core/nl_utf8_separator.dfy`, this plan, both plan/wiki indexes and
`wiki/nl-utf8-separator.md`. The production change is exactly two expressions.
The source main checkout and all its pre-existing changes remain untouched.
The parent independently reviewed the complete regression and the two-function
design and reported no findings; its requested helper comment is present.

From `/workspace/tmp/leanutils-port/nl-unicode-dafny`, the supported command
`PYTHONPATH=/workspace/tmp/leanutils-port/nl-unicode-dafny/src make -C bench/utils/nl verify`
completed all 40 declarations: `DAFNY_VERIFICATION_OUTCOME=verified phase=verify`,
`DAFNY_VERIFICATION_RESULT total=1010 failed=0`, exit 0. Session:
`nl-dafny-full-20261023`; artifacts: `dafny-full.log` and `dafny-full.exit` in
`/workspace/tmp/leanutils-port/nl-unicode/`. The scope includes the original
`Nl.NlBenchmarkItem.RunCore ==> NlSpec.Spec` obligation and all entry-reachable
Core/Proof declarations selected by the supported verifier. The existing core
library and external native contracts remain the explicit trusted boundary.
Existing `decreases *` means this proves correctness on return, not termination.
No library assumptions, annotations, skips, input restriction or limits changed.

Focused changed-function command used the same options as the regression with
`bench/utils/nl/NlSpec.dfy --filter-position=NlSpec.dfy:189-199`; it verified
2 assertions with 0 errors. The complete regression verified 226 assertions,
0 errors. `dafny-benchmark format --check bench/utils/nl/NlSpec.dfy
tests/core/nl_utf8_separator.dfy`, `git diff --check`, and recursive plan/wiki
non-Markdown audits pass. The last regression changes after its passing proof
were formatter whitespace and the requested one-sentence helper comment only.

The authorized commit invokes the existing mandatory hook unchanged: `dafny format
bench` and serial `make test-unit`. Its authoritative command output and exit
status are `dafny-commit.log` and `dafny-commit.exit` at the same artifact path;
a failed hook must block delivery. No separate native build, runtime differential
campaign or fuzzing was run: this bounded maintenance change uses primary GNU
source evidence, ghost regression and the complete supported proof closure.
No restricted evaluator/oracle inputs were accessed.

Remaining source action: deliver the successful commit ID and exact seven paths
to the owning task for fast-forward main integration while preserving its dirty
working-tree bytes. Do not push. No proof blocker remains.
