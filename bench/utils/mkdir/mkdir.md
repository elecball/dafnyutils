# mkdir

## Scope

This benchmark creates one directory per operand, in command-line order, and
supports `-v` / `--verbose`, option bundles, unique long-option abbreviations,
`--`, `--help`, `--version`, and GNU parsing diagnostics. A failed operand does
not roll back earlier directories or prevent later operands from being tried.
An existing directory is an error without `--parents`.

- Reference: GNU coreutils `src/mkdir.c`, `lib/mkdir-p.c`, and public upstream
  tests at `2cf491412c199e2211880ec3f4ba387026638a33`; GPL-3.0-or-later,
  <https://www.gnu.org/software/coreutils/>.
- Model/API baseline: repository revision `1ed3144e6b092f50ce99b0450d242a43309e1bd4`; shared `bench/core/IO.dfy` and
  `IOContract.dfy` are the trusted native boundary. This combined contribution
  refines their filesystem effect relations and verifies the Dafny wrappers
  separately; the native C/C# implementation remains trusted.
- AllowedInput: finite sequences of Linux paths representable as UTF-8 strings,
  including empty operands, repeated paths, relative/absolute paths, trailing
  separators, `.` / `..`, missing parents, and symlink traversal. Embedded NUL
  is outside the native argv domain. Unsupported options listed below are
  outside this contribution's accepted command domain.
- EnvironmentProfile: Linux, C locale, `TZ=UTC0`, filesystem and process context
  supplied by the shared IO model, including credentials and the existing umask.
  Native directory mode, ownership, storage, timestamps and link counts remain
  request-bound trusted observations: `DirectoryCreationEffectFields` guarantees
  namespace/preservation properties rather than simulating the POSIX policy.
- Observation: exact stdout/stderr bytes and exit status, resulting directory
  namespace, inode metadata and partial filesystem effects, under the supplied
  contracts. Standard input is not consumed. Stream-write
  committed prefixes and their terminal errno are modeled with `ReturnError`.
  Stdout failure appends GNU's `write error` diagnostic after operand errors;
  either stream failure yields exit 1. Help/version and parse-error early exits
  retain the shared runner's separate `ThrowOnError` boundary.
- TrustedOperations: single `CreateDirectory` calls with mode `0777`, GNU path
  quoting, C-locale errno formatting, and stream writes. Operand iteration,
  diagnostic selection, output order, committed stream prefixes and the overall
  exit policy are proved.

## Options left out due to IO.dfy

| Option | Missing API support and source evidence |
| --- | --- |
| `-p`, `--parents` | `src/mkdir.c` computes an ancestor umask with owner write/search bits cleared and temporarily sets it for ancestor creation. `IO.dfy` provides `GetUmask`, but no operation to set the process umask. With an owner-restrictive umask, primitive creation cannot make traversable GNU ancestors. Creating then chmodding adds a new failure and partial-effect point that GNU does not have, so it is not a faithful replacement. |
| `-m`, `--mode` | `src/mkdir.c` calls `umask(0)` and sets an adjusted mask so explicit mode bits survive the original umask. The current `CreateDirectory` always uses the actual process umask and there is no setter. Post-creation chmod likewise adds a non-GNU error point. Numeric and symbolic modes are both left out. |
| `-Z`, `--context[=CTX]` | There is no SELinux/SMACK enablement, label, default-creation-context or restoration operation in the IO model. The kernel-dependent warnings and label effects cannot be specified faithfully. |

These are model limits, not approximated behavior. Informational help retains
the pinned GNU program's complete text. The generator restricts option pools to
the supported contribution domain.

## Specification and proof

- SpecificationEntry: `MkdirSpec.Spec` relates each ordered operand to its
  trusted directory-creation effect. Existential intermediate filesystems retain
  all effects; index properties and byte partitions determine exact stdout and
  stderr without a second execution algorithm in the specification.
- Frame: `RunCore` modifies only `fsRegion`, `stdoutRegion`, and `stderrRegion`;
  its specification also reads `nowRegion`, `umaskRegion`, and
  `trustedFilesystemRegion` and `trustedStreamsRegion`. Other IO regions are
  outside its frame.
- TerminationPolicy: the directory-processing loop terminates for every finite
  operand sequence. The shared CLI runner and parser have the existing
  nontermination/trusted boundary; CLI termination is not established.
- CLI boundary: help/version and missing-operand requests use early-exit plans;
  parsing remains the shared trusted boundary. `RunCore` directly ensures
  `Spec(raw, io, exit)` for nonempty decoded directory commands.
- Normal/error behavior: successful requests produce exactly one directory
  creation and, in verbose mode, one GNU-quoted announcement. Every failed
  request contributes one GNU-quoted diagnostic with its actual errno. Stream
  observations determine the exact committed prefixes. Exit is exactly 0 iff
  every creation and both stream writes succeed, and exactly 1 otherwise.

For example, `mkdir -v result-dir` creates a previously absent directory and
exits 0:

```text
mkdir: created directory 'result-dir'
```

The specification rejects a success result for an existing directory, reordered
messages, rollback of earlier successes, and stopping before a later operand
after an error.

## Validation

The integrated build and 63 strict GNU oracle cases pass. Three Docker campaigns
with seeds 1, 7 and 19 each completed 1000 matches with no mismatches, timeouts
or other errors. They include the corrected native shell quoting for positional
`#`, `~`, `@` and apostrophes; stdout, stderr, exit status and filesystem state
are compared without relaxing the comparator.

The integrated `make check TASK=mkdir` passes on its recorded unchanged source
manifest: all 17 declarations and 360 verification conditions, the four default
Spec/Core/Proof/Entry module checks, 63 runtime oracles, and the mandatory short
fuzz campaign. The complete shared library is checked separately; this utility
gate treats the declared `bench/core` contracts as its library boundary.

This maintenance change starts from
`1ed3144e6b092f50ce99b0450d242a43309e1bd4`. Integrated commands run from
`/workspace/tmp/fs-benchmarks-20261020/integration` with
`PYTHONPATH="$PWD/src:$PWD"`. Current-workspace evidence is outside public task
resources under `/workspace/tmp/fs-benchmarks-20261020/evidence/`:
`quoting-runtime-v2/mkdir/` contains the rebuilt oracle and three campaigns;
`final-gates-approved-v1/mkdir.log` and its unchanged before/after source
manifests record the final contribution gate with the approved nonnegative
`ReadDirContractFields` error domain. `core-approved-closure-v5/` records
separate shared-library success: 598 declarations and 3640 conditions. The
3,000-case campaigns precede that ghost contract refinement; utility execution,
native IO, generators and the comparator are unchanged, and the final gate
rebuilds and checks all strict oracles and its short campaign. `mkdir-integration/check-v4.log` and failed proof
attempts in `mkdir/` retain earlier evidence; failures are not passing checks.

Dafny is 4.11.1+10dca3ba4a2909c11299176440401fc31413b53d, .NET SDK 8.0.131,
Python 3.12.3, pytest 9.1.1, Ruff 0.15.12 and Rust/Cargo 1.94.0. Docker uses
`dafnyutils-coreutils-fuzzer:latest`, image
`sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76`,
uid/gid 1000, 10-second command timeouts and bounded generated filesystems.
Proofs use the existing 30-second VC limit, isolated assertions, seed 42 and
100-second declaration limit. Benchmark oracle fixtures are separate from the
development tests. Profile review, final shared-core verification and final
development checks are tracked separately as integration acceptance work.
