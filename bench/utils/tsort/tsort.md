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
`--` to end option processing. The pinned GNU version accepts and ignores
`-w` for POSIX.1-2024 compatibility.

### Benchmark-Supported Behavior

The benchmark handles zero or one file/stdin operand, plus `-w`, `--help`,
`--version`, `--`, GNU long-option abbreviations, and operand, option, input,
cycle, and output errors.

Only space, tab and newline separate tokens, and pairs can cross line
boundaries. Carriage return, vertical tab and form feed remain part of a name.
Names use unsigned-byte lexicographic order and end at their first NUL byte,
matching the C implementation.

Every distinct name becomes one vertex. A self-pair such as `a a` registers
`a` without adding an edge. Repeated non-self pairs remain separate edge
occurrences. Successors are stored in reverse input-pair order.

The initial zero-indegree vertices are processed in byte order. Processing a
vertex removes its outgoing edges in successor order, and newly zero-indegree
vertices join a FIFO queue. Input `a b a z`, for example, produces `a`, `z`,
`b`. The specification requires GNU's exact ordering.

If no vertex is ready while vertices remain, the command selects the same
cycle as GNU, reports the input name and cycle on stderr, removes one selected
edge occurrence, and resumes ordering. Further cycles produce further
diagnostics. Cyclic input can produce both stdout and stderr, with exit status 1.

Empty input succeeds without output. An odd number of tokens is rejected
before any vertex is emitted. Open and read failures produce GNU diagnostics.
File-close failures are reported after normal processing, unless an earlier
fatal odd-token error takes precedence. Output failures retain committed
prefixes and force failure, including failure to write a diagnostic.

No GNU `tsort` options are excluded due to missing `IO.dfy` support.

### Scope and model

- **Input and environment:** Finite arguments and input bytes, one file or
  stdin, Linux filesystem, current user permissions, and C-locale diagnostics;
  the parity environment uses UTC0, TERM=dumb and NO_COLOR=1.
- **Observation:** Exact stdout/stderr bytes, diagnostic order, exit status
  and modeled stdin consumption. The command leaves the filesystem unchanged.
  Input consumption and committed output prefixes follow the supplied stream
  observations, including failures.
- **Trusted API:** Shared CLI parser; `ReadStdin`, `ReadFile`, `WriteStdout`,
  `WriteStderr`, argument/path quoting and C-locale errno text from `bench/core`
  at tested repository revision `16f27781c087ba716e9b5b8fddab254cab4eeb49`.
  Read-stage and partial-write observations come from the supplied contracts.
  The stdin API does not expose a separate close-stdin failure.
- **Proof:** `Tsort.TsortBenchmarkItem.RunCore` directly ensures
  `TsortSpec.Spec`. Mathematical relations over token boundaries, vertex ranks,
  edge-removal ranks, release order and selected cycles determine output and
  diagnostics. Utility algorithms terminate on finite input; whole-process
  termination is not proved because the shared CLI entry and
  `PlanParseFailure` retain `decreases *`. Native IO contracts are trusted.

### Exit Status

The command exits with status 0 after successful acyclic processing or a
successful help/version request. Invalid options, extra operands, odd token
counts, cycles and reported IO failures exit with status 1.
