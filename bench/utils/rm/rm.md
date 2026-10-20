# rm

## Scope

Reference: GNU coreutils `src/rm.c`, `src/remove.c`, `gnulib/lib/fts.c` and
`gl/lib/root-dev-ino.h` at `2cf491412c199e2211880ec3f4ba387026638a33`,
GPL-3.0-or-later. This is a repository maintenance contribution based on
`1ed3144e6b092f50ce99b0450d242a43309e1bd4`, using the maintainer-supplied
inode filesystem and native removal contracts in `bench/core/IO.dfy` and
`IOContract.dfy` from this change set.

Allowed input: finite file operand sequences; ordinary files, hard links,
symbolic links including dangling links, special nodes represented by the
shared inode model, and finite directory hierarchies. Implements `-f/--force`,
`-v/--verbose`, `-d/--dir`, `-r/-R/--recursive`, `--one-file-system`,
`--preserve-root[=all]`, `--no-preserve-root`, and
`--interactive=never/no/none` including unambiguous value abbreviations.
Once-only interaction (`-I` or `--interactive=once`) is also supported when
at most three operands are supplied without recursion, so GNU performs no prompt.
GNU option permutation, option bundles, long abbreviations, `--`, help,
version, missing operands and malformed uses of these options are included.
The full, exact `--no-preserve-root` spelling is required, as in GNU.

Environment profile: Linux, C locale, `TZ=UTC0`, nonterminal standard input,
fixed process credentials and a finite stable filesystem during the command.
Paths use the shared text-path ABI. The APIs use whole path strings rather
than descriptor-relative operations, so recursive traversal requiring paths
beyond total `PATH_MAX`, and concurrent renames or namespace replacement,
are outside this model. Ordinary overlong-component `NAME_MAX` failures stay
in scope: although metadata queries map native `ENAMETOOLONG` to `ENOENT`,
the subsequent required removal attempt retains the native path-length error.
It is not ignored by `-f`. Fixtures never request removal of host root or mounts.
Different-device safeguards are specified through the supplied native device
and inode identities; ordinary oracle fixtures stay within one device.
GNU's filesystem-type-dependent inode ordering above 10,000 entries in one
directory is outside exact traversal-order parity. `gnulib/lib/fts.c` uses
`fstatfs` to choose that optimization, while IO.dfy exposes directory inode
numbers but has no filesystem-type query. This boundary follows GNU's actual
optimization threshold; recursive execution uses finite identity sets at every
depth.

Observations: exact stdout and stderr bytes, exit status 0 or 1, directory
handle restoration, and the complete modeled filesystem. Removal uses the
request-bound native effect relations: one namespace entry disappears;
surviving hard links, content, modes, owners, storage, identity and metadata
are preserved exactly to the extent required by those shared contracts.
Permitted native timestamp and traversal effects remain explicit in those
contracts. Verbose lines follow successful removal only. Missing-path force
handling covers GNU's ENOENT, ENOTDIR, EINVAL and Linux EILSEQ cases, without
suppressing permission, symlink-loop or path-length errors. An operand failure
does not stop later operands. A failed descendant suppresses removal of its
ancestor directory while successful sibling effects survive.

Trusted operations: `GetFileTimes`, `OpenDir`, `ReadDir`, `CloseDir`,
`UnlinkPath`, `RemoveDirectory`, `QuoteafPath`, `QuoteArgument`,
`GetCLocaleErrnoText`, and standard-output/error writes. These are existing
shared interfaces. Utility code implements option policies, traversal,
termination, safeguards, error continuation and message ordering. Output and diagnostics are buffered until every filesystem operation has
finished, then written with `ReturnError`. Exact native committed prefixes,
stdout write-error diagnostics, stderr receipts and the final status are
part of `StreamResults`; a failed verbose flush preserves all removals.

GNU's missing-operand check precedes prompting, including `-i`, recursive
once-only flags and the simulated-terminal switch with no operands.
Effective prompting with nonempty operand sequences remains outside IO.dfy: `-i`, once-only interaction
when its prompt is required, `--interactive[=always/once/yes]`, and terminal
write-protection prompts enabled by the internal `---presume-input-tty` switch.
An effective `-f` or `--interactive=never` suppresses those prompts in either
option order and is supported even with the simulated-terminal switch. The model has neither `isatty` nor a
line-at-a-time answer input operation preserving the unconsumed input suffix.
`ReadStdin` consumes an entire stream and cannot implement GNU `yesno()`'s
incremental consumption or terminal-dependent write-protection prompts.
Explicitly forced commands and nonterminal, noninteractive invocations remain
within scope. The schema recognizes these forms so later `-f` or a never
setting can cancel interaction; an effective interactive command is outside
the modeled contract's GNU parity population and reports a scope diagnostic.

## Specification and proof

Specification entry: `RmSpec.Spec`. Atomic removals use the existing
`IOContract.UnlinkPathSpec` and `RemoveDirectorySpec` relations. An inductive
`RemoveJudgment` combines atomic judgments with a native directory listing,
existential sibling filesystem states, exact output partitions and failure
flags. `OperandsJudgment` relates each operand to its intermediate filesystem
and output states. The specification is a declarative derivation relation;
Core owns native iteration and recursive execution. `CommandPath` and
`StatusPath` are declarative path/value relations using the shared
`PathWithoutTrailingSlashes` relation, with explicit empty and root cases.
Command operands retain one trailing slash; metadata lookups remove trailing
slashes except for root. Core uses the shared `PathCore.TrimTrailingSlashes`
algorithm, and Proof connects its summary to both relations.

Frame: filesystem, stdout, stderr and directory handles. Directory handles
are restored after each completed listing and each removal invocation. No
input, credentials, process context, time provider or status-observation
cursor changes are permitted.

Termination: recursive calls strictly decrease the finite set of initial
filesystem host identities minus ancestor identities. Atomic removal cannot
introduce a host identity. Repeated ancestor identities are rejected as cycles.
Directory iteration decreases the remaining native entry set, and operand
and sibling loops decrease their remaining finite sequence lengths. There is
no depth budget or termination skip in the Core removal implementation.

CLI boundary: the existing shared parser is trusted. The process entry uses
`BenchmarkItemTwostate`; both `RmCore.RunCore` and the utility entry
`RmBenchmarkItem.RunCore` directly ensure `RmSpec.Spec`. Help/version stop at
the first corresponding option, including ahead of later malformed options.
All fixed user-facing text is defined in Spec.

## Validation

The integrated `make check TASK=rm` passes on unchanged before/after source
manifests with the approved shared error-domain contract: compilation, all 60
strict GNU oracle cases, the mandatory 20-case campaign, all 41 declarations and
1147 verification conditions, and the four default Spec/Core/Proof/Entry module
checks. `RunCore` directly ensures the principal specification. Verification
retains seed 42, included-file checking, isolated assertions, the 30-second VC
limit and the 100-second declaration limit.

`ReadDirContractFields` now requires `0 <= err`, as explicitly approved by the
user after review of the Linux/glibc native return paths. The utility's existing
nonnegative listing-error requirement, allowed inputs and native behavior are
unchanged. The complete shared-library check independently passes 598
declarations and 3640 conditions. Before approval, the canonical utility gate
stopped at declaration 20 of 41 and the default Core check reported one errno
range error; those historical failures remain recorded as failures.

The refactored frozen executable matches all 3,000 requested cases across seeds
1, 7 and 19, with zero mismatches, timeouts or other errors. Exact stderr,
stdout, status and filesystem comparison, the 16-option discovery pool and
filesystem bounds are unchanged. Later edits affect only ghost proof guidance
and the approved shared contract; executable utility logic, native IO,
generators and the comparator are unchanged. The final contribution gate
rebuilds and reruns all strict oracle cases and its short campaign. The earlier
bounded no-file CLI review also matched 1,342 cases and six invalid-byte probes.

This maintenance change starts from
`1ed3144e6b092f50ce99b0450d242a43309e1bd4`. Integrated commands run from
`/workspace/tmp/fs-benchmarks-20261020/integration` with
`PYTHONPATH="$PWD/src:$PWD"`. Current-workspace artifacts are outside public task
resources under `/workspace/tmp/fs-benchmarks-20261020/evidence/`:
`final-gates-approved-v1/` contains the full utility gate and source manifests;
`runtime-boundary-rm-final/rm/` contains the rebuilt oracles and three campaigns;
`core-approved-closure-v5/` contains the shared-library proof results; `rm/`
preserves earlier focused checks and failed approaches. Profile and development
checks are recorded separately from utility proof and runtime success.

Tools are Dafny 4.11.1+10dca3ba4a2909c11299176440401fc31413b53d, Z3 4.16.0,
.NET SDK 8.0.131, Python 3.12.3, pytest 9.1.1 and Rust/Cargo 1.94.0. Docker uses
`dafnyutils-coreutils-fuzzer:latest`, image
`sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76`,
uid/gid 1000 and a 10-second command timeout. `Tests.py` is a benchmark
oracle/scoring fixture; no development temporary-directory test was added.
