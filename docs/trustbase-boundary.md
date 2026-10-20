# Keep utility algorithms in their benchmark item

`bench/core` defines system values, native observations, primitive effects and
their mathematical contracts. Utility algorithms and their derived proofs
belong in the item's editable Core and Proof sources. A shared implementation
must not discharge the computation that the benchmark asks its candidate to
implement and prove.

Native failure results, partial effects, state validity and resource ownership
remain part of the primitive contract. Removing a convenience lemma does not
remove those guarantees. Internal consistency proofs needed to construct a
valid model value are separate from a proof of utility behavior.

## Candidate ownership

A moved file is a candidate obligation only when all of these hold:

- It is outside the fixed specification and CLI dependency closure.
- It is not copied as support or supplied as a support resource.
- Its source is editable and collected with the item's submitted outputs.
- The generated workspace supplies its module placeholder instead of a solved body.
- Its reachable definitions are selected by the real local and evaluated proof gates.

The evaluator fixes whole specification/support source files. A filename ending
in `Core` or a directory-wide editable mount cannot override that classification.
Keep mathematical relations in Spec files and implementations/proofs in separate
files. Never let a fixed decoder import an implementation-owned helper: that
would make the helper's entire file immutable.

Path trimming demonstrates this distinction. `cp`, `mv`, `rm` and `rmdir` own
their runtime path algorithms and connecting proofs. Cp's fixed decoder keeps
its original normalization in `CpSchema.TrimForDecode`; runtime CpPathCore never
calls that routine. The fixed command-line mapping and the candidate's runtime
proof are preserved independently.

## Fixed command-line protocol

Every item uses the same CLI-to-RunCore layout. Each task's `CliSupport.dfy`
contains its parser and process runner; only protocol data types remain in the
shared core. The input mapping, parser configuration, early-exit behavior and
stream error handling remain fixed scaffolding, as they were before this split.
CLI parsing remains outside the principal `RunCore ==> Spec` proof boundary.
Task-local protocol code is explicitly fixed support, not a candidate-owned
utility implementation or a native API.

The runner's codec is private to its module and has no public export. It cannot
be called as an encoding API from Core. Unused parser proof lemmas are removed,
and the old module-wide verification skips are removed from the local protocol
and shared data types. Contributor scaffolds use the same files as existing
items.

## Shared algorithm supply

Map, filter, scan and fold implementations and their proofs are no longer
automatically supplied by profiles or recommended as a solved support resource.
The unused shared Functional module is removed. Tasks implement any such
algorithms themselves.

Runtime path/backup helpers, UTF-8 encoding, byte quoting, dynamic diagnostics,
numeric formatting, mode parsing and time formatting are task-owned wherever
they implement utility behavior. Core imports the item's implementations; the
fixed specification imports only mathematical relations and protocol data.
Each owned encoder proves its agreement with the ghost encoding model and any
width or length facts it needs. Those properties are not supplied as completed
shared encoder proofs.

The mathematical `Utf8Semantics` and `StringEscaping` definitions are ghost.
World path transformations and contract-side filesystem transformations are
also mathematical definitions. They cannot be executed by a candidate as a
ready-made implementation. The remaining shared proof surface establishes
representation validity required by primitive contracts. Kernel lookup,
removal and rename proof internals are private to `IOContract`; they do not
export utility correctness lemmas. Task-specific lookup, mutation and metadata
proofs are in the corresponding editable task closure.

The native boundary is unchanged by this split. Approved libc/gnulib operation
contracts remain trusted, including their failures and partial effects. The
existing `QuoteArgument` and `QuoteafPath` adapters remain compatibility
primitives implemented by managed code; they are not newly claimed to be
native gnulib calls. Their limitation is recorded in [core-api.md](core-api.md).

## String and byte boundaries

Raw command arguments remain Unicode strings. Files and standard streams use
byte sequences. Moving encoders into candidate-owned code exposed several
previously ill-formed diagnostic models: six utility errno messages and
Expand's errno message concatenated unrestricted error text directly into a
raw-byte result. Both the model and execution now UTF-8 encode that error text.
ASCII diagnostics retain their previous values; the general model also has a
well-defined value for Unicode error text.

Expand's produced tab diagnostics are bytes throughout its internal parser.
Already quoted byte strings are concatenated directly, without encoding them
again. Its raw command datatype and accepted raw strings are unchanged. Factor
proves that tokens split from stdin are bytes before passing them to its byte
diagnostic renderer; argv tokens remain unrestricted strings. The new internal
preconditions are derived from the existing input-token relation. A refinement
lemma preserves the old token-result formula for every produced token.

Short-option diagnostics in Unlink and Touch assemble text using an explicitly
string-typed prefix before encoding. This avoids inferring a byte constraint
on an arbitrary Unicode option character. It changes neither the input domain
nor the diagnostic value.

## Maintenance evidence

This is repository maintenance, not an evaluated agent run. Task 1 completed at
`b693b10f0779fd9fa2452e696888a30f0369ce39`; task 2 completed at
`260ff29ed4844dadec7b22bc82a374fdc502f8f9`. Task 3 began after task 1 completed,
in `/workspace/tmp/trustbase-cli-20261020/trustbase`, initially based on the
task-2 code revision `61565b1e80c7974700d7144ef459a4aa3b98c784`. The final
task-2 amendment changed its validation document only. The historical task-1
results in [trustbase-failures.md](trustbase-failures.md) are retained; this
document describes the current implementation-ownership boundary.

The artifacts below are local to `/workspace/tmp/trustbase-cli-20261020/`;
they are maintenance records, not benchmark resources. They preserve commands,
source/configuration hashes, logs, actual exits and TRX reports. Worktree
commands use `PYTHONPATH=$PWD/src`. Versions are Python 3.12.3, Dafny
4.11.1+10dca3ba, tmux 3.4 and .NET SDK 8.0.131. Formal checks retain seed 42,
isolated assertions, a 30-second VC limit and a 100-second target limit.
`DOTNET_PROCESSOR_COUNT=8` and bounded target pools control concurrency without
changing those limits. Focused utility checks use the existing native target
contracts and `_verify_target` engine, including its source/symbol filters,
warning, TRX and exit validation.

The actual generated-profile/workspace audit passed a complete 52-item source
pin: **159 candidate-owned helper files and 1,009 matching local/evaluated
native helper targets**, with no missing/stale profile or source change during
the join. Every helper is an editable module placeholder, absent from fixed
formal/support/read-only sources and collected with task outputs. Every public
RunCore directly ensures its principal Spec. The audit constructs real profile
and workspace specifications in memory; it publishes no workspace.
`task3-ownership-cohorts/final-union2/result.json` records the final source
pin, including the last Ls proof extraction. The earlier `final-union1/` receipt
is retained as historical evidence. `task3-ownership-audit.md` and
`task3-ownership-cohorts/README.md` explain the classification and exact-source
refresh rules. Target membership establishes ownership; proof counts are
recorded separately below.

The following completed scopes overlap. They must not be summed into a unique
repository total or described as a monolithic whole-utility proof run.

| Formal scope | Completed result | Artifact path |
| --- | --- | --- |
| Intrinsic core/native consistency and moved utility proof closure | 69 nonzero declarations, 1,798 VCs, 0 failures | `task3-proof-boundary/focused-first/`, `task3-core-audit.md` |
| Exact 95 World/IOContract ghost-annotation declarations | 62 nonzero declarations, 356 VCs; 33 zero-obligation declarations excluded | `task3-model-ghost-proposal/direct-model-proof/` |
| Final shared UTF-8 and quoting mathematical models | 17 nonzero declarations, 120 VCs; 9 zero-obligation declarations excluded | `task3-codec-model-direct/README.md` |
| Owned Cp/Mv/Rm/Rmdir Path implementation/proof closure | 44 nonzero targets, 900 VCs, 0 failures | `task3-path/pure-checks-ghost/result.json` |
| Owned World-path runtime helpers | 11 nonzero targets, 91 VCs, 0 failures | `task3-world-path/focus-ghost-proposal/result.json` |
| Owned Ln path algorithms and affected callers | 6 nonzero targets, 464 VCs, 0 failures | `task3-ln-path-split/README.md`, `task3-ln-path-callers-guided/` |
| Cat/Head/Tail encoders, quoting, text and affected entry closure | 91 nonzero targets, 1,404 VCs, 0 failures | `task3-stream-codecs/check-first/result.json` |
| Actual text/codec callers and Core/public entries for 15 root utilities | 97 nonzero targets, 4,159 VCs, 0 failures | `task3-root15/final-union/result.json` |
| Three Chmod bridges after removing forbidden 60-second overrides | 3 nonzero targets, 482 VCs at the canonical 30/100 limits, 0 failures | `task3-chmod-limits/check/result.json` |
| Original codec/renderer helper and caller manifest | 266 nonzero jobs, 12,479 VCs, 0 failures; 6 zero-obligation jobs excluded | `codec-split/final-manifest.json` |
| Final Ls recursive traversal and extracted ghost helpers | Walk 423 VCs; prefix 86, close 19 and child update 62 VCs; 0 failures | `task3-ls-walk-close-extraction/final-receipt.json` |

Other owned codec, renderer, byte-typing and caller slices are documented in
`codec-split/README.md`, `checks/task3-parent-union2.json`,
`task3-factor-byte-typing/` and `task3-chmod-ghost-final-wf/`. These receipts
include the actual nonzero/zero classification, source pins and repair history;
they do not turn the table into a full-repository count. Direct mathematical
core checks retain the existing 16 IOContract indentation warnings in their
logs; they are not presented as warning-free utility runs. Methods with
`decreases *` establish their contracts on return, not termination.

The initial 15-utility caller queue had three timeouts in Wc, Paste and Nl.
Those failures are preserved. Local ghost-only guidance retained their runtime,
headers, invariants, domains and mathematical obligations. Every selected
target in all three changed projects was rerun; the final union uses current
complete source hashes, preserves the original 96 targets and adds the new
Paste prefix lemma. It retains only the exact-source passing cohort from the
other 12 tasks. See `task3-root15/README.md` and `task3-wc-prepare/README.md`.
The original Chmod ownership rejection is also preserved; removing only the
three time-limit attributes tightened acceptance rather than relaxing the
engine.

| Repository/protocol check | Actual outcome | Artifact path |
| --- | --- | --- |
| `make test-final` | 113 unit tests and 16 integration tests passed; exit 0, 91.63s | `checks/task3-development-final.{json,log}` |
| `python3 -m ruff check src tests tools` | exit 0 | `checks/task3-ruff-check.{json,log}` |
| `python3 -m ruff format --check src tests tools` | exit 0; 93 files already formatted | `checks/task3-ruff-format.{json,log}` |
| `python3 -m benchmarks validate <task>` for all 52 items | initial exit 0, 181.89s; final all-52 union passed on current sources, exit 0, 20.34s for the last Ls refresh | `checks/task3-layout-union-final.json`, `final-layouts-union.json`, `final-layouts-source-refresh/` |
| Original-public/private-codec resolver controls for 12 fixed CLI modules | all 24 positive/negative controls matched; exit 0, 51.48s | `checks/task3-private-final.json`, `private-cli-exports-final2/` |

The first CLI export probe exposed missing exported module imports, and a
parallel Path check observed obsolete support registrations. Both were repaired
and their failed records retained. The final private-codec controls require
original public members to resolve and private `ProtocolEncode` access to fail;
a negative probe's expected rejection is not counted as a successful Dafny
proof. `checks/task3-doc-tree-audit.json` records no non-Markdown artifact in any
of the five inspected worktrees' plan/wiki trees. No package, dataset, oracle
expectation or verification skip was introduced.

Native continuity used one supported build each for Unlink, Expand, Factor and
Ls: `make build TASK=<utility>` with the existing build configuration and
`BUILD_DIR=/workspace/tmp/trustbase-cli-20261020/task3-native-build`. All four
builds exited 0. The existing GNU 9.10.13-2cf49 reference binaries were neither
rebuilt nor modified. Under the C locale, **35 of 36 bounded supported-scope
comparisons matched stdout, stderr and exit code exactly**: Unlink 7/7, Expand
9/10, Factor 10/10 and Ls 9/9. The sole mismatch is Expand's pre-existing
abbreviated `--help`; `expand-help-baseline.json` proves its fixed help text is
unchanged from the task-3 base. That divergence is reported, not counted as a
pass. The initial Ls probe selected unsupported flags; its parser rejections
remain preserved and are excluded from these comparison counts. Corrected Ls
probes reused the same DLL. Exact build/source/DLL/reference hashes, commands
and bounded probes are in `task3-native-continuity/` and
`task3-native-continuity-ls/`. These results are bounded continuity evidence,
not a new full GNU oracle-suite claim.

The final codec manifest closes all original 272 job slots: 266 nonzero jobs
verified 12,479 obligations with no failure, and 6 zero-obligation selections
are excluded from proof counts. Supplemental helpers have separate receipts;
their counts overlap other cohorts and are not added to that total. The final
361-source delta audit classifies all 19 changed sources. The mathematical
retention audit classifies all 17 recorded differences without an unknown
exception. Its preserved evidence distinguishes unchanged definitions from the
documented byte-model corrections and refinements.

The final Ls Walk passed 423 obligations in 93.06 seconds under the unchanged
100-second target limit. Its prefix helper passed 86 obligations; unchanged
close and child-update declarations retain their 19- and 62-obligation checks.
`task3-ls-walk-close-extraction/final-preservation.json` reconstructs the prior
Core byte-for-byte by reversing only the ghost proof extraction. It preserves
the runtime statements, public contracts and loop invariants, and connects
104 unchanged declarations, including Render and Snoc, to their current
source/dependency hashes. The failed intermediate cycle-invariant attempts and
the earlier fragile 99.30-second pass remain preserved in the same artifact tree.

The final changed-item layout union, final ownership union and proof manifests
all use the frozen Ls Core hash
`235bc41be33f0944be7aef375e486e0ef57235ce4662b56648d854e0b1299581`.
`final-source-state.json` identifies the tested code independently of the commit
hash: 470 changed-or-critical source records, with 456 present files totaling
5,367,035 bytes and 14 removals. Its SHA-256 is
`a6765754a2c97a5174449a3eb264a55a705d6bbabccb4423fbf480c535099005`.
Markdown is excluded from this code snapshot. `checks/task3-final-review.json`
and `final-review.json` record the final path, stale-reference, trust-annotation
and whitespace audit. The shared IO execution sources and repository
instructions are byte-identical to the task-2 integration target.
