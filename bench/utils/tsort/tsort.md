# tsort NL Specification

Source:
- `coreutils/doc/coreutils.texi`
- `@node tsort invocation`
- Source line range: 5954-6075
- Implementation: `coreutils/src/tsort.c` at submodule commit
  `2cf491412c199e2211880ec3f4ba387026638a33`
- License: GPL-3.0-or-later

This file summarizes the upstream GNU `tsort` behavior relevant to the benchmark.

## `tsort`: Topological sort

`tsort` reads pairs of names describing a partial ordering. Each pair `a b`
requires `a` to appear before `b`. It writes one name per line in an ordering
consistent with those pairs when the input has no cycles.

```text
tsort [OPTION] [FILE]
```

With no file operand, or with `-`, input comes from standard input. One other
operand names the input file. More than one file operand is an error.
Input `a b b c`, for example, produces `a`, `b`, `c` on separate lines.

The command accepts `--help`, `--version`, GNU long-option abbreviations, and
`--` to end option processing. The pinned GNU version also accepts and ignores
`-w`, as documented for POSIX.1-2024 compatibility. An older installed `tsort`
may reject `-w`; the benchmark reference is the pinned build, not that binary.

### Benchmark-Supported Behavior

Only space, tab and newline separate tokens. Pairs can cross line boundaries.
Carriage return, vertical tab and form feed remain part of a name. Names use
unsigned-byte lexicographic order. A token's name ends at its first NUL byte,
matching the C implementation.

Every distinct name becomes one vertex. A self-pair such as `a a` registers
`a` without adding an edge. Repeated non-self pairs remain separate edge
occurrences. Successors are stored in reverse input-pair order.

The first queue contains zero-indegree vertices in byte order. Processing a
vertex removes its outgoing edges in successor order; newly zero-indegree
vertices join the tail. This is not a priority queue: input `a b a z` produces
`a`, `z`, `b`. An arbitrary valid topological ordering is not sufficient.

If the queue empties while vertices remain, the command identifies the same
cycle as GNU, writes the input name and selected cycle to standard error,
cuts one selected edge occurrence, and resumes ordering. Further cycles
produce further diagnostics. Cyclic input can produce both normal output and
diagnostics, with final exit status 1.

Empty input succeeds without output. An odd number of tokens is rejected
before any vertex is emitted. Open and read failures produce GNU diagnostics.
File-close failures are reported after normal processing, unless an earlier
fatal odd-token error takes precedence. Output failures retain committed
prefixes and force failure, including failure to write a diagnostic.

No GNU `tsort` options are excluded due to missing `IO.dfy` support.

### Scope and model

- **Input and environment:** Finite arguments and input bytes, one file or
  stdin, Linux filesystem observations and C-locale diagnostics. The parity
  environment uses UTC0, TERM=dumb and NO_COLOR=1.
- **Observation:** Exact stdout/stderr bytes, diagnostic order, exit status
  and modeled stdin consumption. The filesystem is read-only. Frames restrict
  stream changes; no successful IO result is assumed.
- **Trusted API:** Shared CLI parser; `ReadStdin`, `ReadFile`, `WriteStdout`,
  `WriteStderr`, argument/path quoting and C-locale errno text from `bench/core`
  at tested repository revision `16f27781c087ba716e9b5b8fddab254cab4eeb49`.
  Read-stage and partial-write observations come from the supplied contracts.
  The stdin API does not expose a separate close-stdin failure.
- **Proof:** `Tsort.TsortBenchmarkItem.RunCore` directly ensures
  `TsortSpec.Spec`. Utility algorithms terminate on finite input. Whole-process
  termination is not proved: the shared CLI entry and `PlanParseFailure`
  retain `decreases *`. The proof assumes the native contracts; it does not
  prove libc, GNU or the operating system.

### Implementation and proof idea

`TsortGraphBuildCore` tokenizes input and constructs the graph.
`TsortSortCore` insertion-sorts vertices, computes indegrees and builds the initial
queue. `TsortStepCore` updates a `TsortState.SortState` containing the queue,
visited map and indegrees. Step requires a nonempty queue with an unvisited
head, updates the state, and returns no value. The caller proves this
precondition; Step's return value is not used to detect cycles.
`TsortCycleCore` finds and cuts a stalled cycle.
`TsortCore` connects these operations to input handling and emission. Each
stage has corresponding Spec and Proof modules.

Tokenization proofs belong to `TsortGraphBuildProof`. Shared execution records,
transitions and emission facts belong to `TsortStepProof`; byte-order, release
and queue-order facts to `TsortSortProof`; cycle search, cuts and selection
transport to `TsortCycleProof`. `TsortProof` keeps final certificate assembly
and output correspondence. Input-result
handling shares one close-error path in Core, using the Spec's existing
odd-token-error precedence instead of separate result wrappers.

Graph contracts relate successor occurrences to original token pairs.
Degree invariants count active incoming occurrences, including duplicate
edges. Queue and visited invariants establish that each accepted step emits
one ready, previously unvisited vertex.

The final specification uses an existential certificate of vertex ranks,
edge-removal ranks, release order and selected cycles. These mathematical
relations fix GNU's output and diagnostic order. Proof-only execution
witnesses connect the implementation to the certificate. A lexicographic
measure decreases either the number of unprinted vertices or the remaining
edge count. Stream contracts relate planned output to committed bytes and
the final exit status.

### Contribution validation

The [contribution guide](../../../CONTRIBUTING.md) and
[PR template](../../../.github/pull_request_template.md) define the required
build, GNU comparison, generated fuzzing and Dafny verification checks.
Report exact commands, tested source, environment, stdout, stderr and exit
codes in the PR. Keep run-specific evidence outside this public task
specification.

### Exit Status

The command exits with status 0 after successful acyclic processing or a
successful help/version request. Invalid options, extra operands, odd token
counts, cycles and reported IO failures exit with status 1.
