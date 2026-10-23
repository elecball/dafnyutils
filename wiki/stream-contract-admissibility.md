# Stream and time contract admissibility

Status: verified; independent source review passed.
Verified source baseline: `37b35bac3d4cf84cdd8ea02eb3279e8aa49307df` plus the
isolated `fix/stream-contract-admissibility` working tree, 2026-10-23.
Origin: [maintenance plan](../plan/2026-10-23-stream-contract-admissibility.md).

The native stream/time contracts need a semantic invariant on the ghost provider.
A raw stream provider can return the wrong result constructor for a request; a
raw time map can record success with nanoseconds -1. Their original full
operation relations then have no outcome. Unconditionally promising those
relations for arbitrary providers is inconsistent.

`bench/core/IOContract.dfy` defines `ValidStreamObservation` using the existing
full relations, and `ValidStreamObservations` validates every request. The
constructive `StreamFailureWitness` shows the state space is inhabited without
adding an axiom. `ValidTimeParseObservations` requires normalization only for
successful stored observations; an empty map is a constructive witness.
`StreamObservationAdmitsRequest` and `TimeParseObservationAdmitsRequest` expose
original-contract outcomes from each validated provider.

`bench/core/IO.dfy` stores validated providers internally. Public
`trustedStreams()` and `trustedTimeParses()` retain their raw return types and
explicitly guarantee validity. Raw request/result datatypes and original
primitive and utility specifications stay unchanged. Malformed raw providers
remain available for counterexample proofs, but cannot inhabit actual IO ghost
state. This is a semantic model-state correction, not an assumption that IO
succeeds. Successful reads, partial progress, empty-write errors, failed parses
with arbitrary result fields and missing parse requests remain admitted.

Focused proofs establish the invariant's inhabitance and unchanged primitive
feasibility; they do not prove libc/gnulib correctness or repair occurrence-key
limitations of the observation model. The original IO initializer's `requires
false` is unchanged and is not evidence of native model-state initialization.
See [the canonical API guide](../docs/core-api.md) for the supported runtime
boundary, and the plan for exact commands, scope, negative controls and results.

Evidence: 365 new stream-provider assertions, 10 time-provider assertions,
2 region-constructor assertions, 10 final getter checks, 107 native/wrapper
assertions, all 24 regression symbols (898 verified), and the full 50-declaration
Echo closure (1888 verified) passed with seed 42 and unchanged 30-second limits.
The old IO source fails exactly the two new getter-validity regressions. All 15
affected original primitive predicate definitions remain byte-for-byte unchanged.

Delivery validation: the required repository pre-commit hook passed its full
benchmark formatting and serial `make test-unit` steps. The successful hook
suppresses test output, so no unit count is inferred. The isolated source commit
contains only the eight owned source, regression and Markdown records. The
separate main checkout adaptation preserves its pre-existing chunk model and
all prior dirty source bytes; it passed 968 regression and 173 native/wrapper/
derived-loop checks and remains deliberately uncommitted. Exact source hashes,
prior-byte snapshots and the incremental patch are under
`/workspace/tmp/leanutils-port/dafny-contract-evidence/` as recorded in the plan.
