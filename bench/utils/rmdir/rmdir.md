# rmdir

## Scope

- Reference: GNU coreutils `src/rmdir.c`, pinned revision
  `2cf491412c199e2211880ec3f4ba387026638a33`, GPL-3.0-or-later. Public scenarios
  come from `tests/rmdir/{t-slash,ignore,symlink-errors,fail-perm}.sh`.
- Model/API revision: base `1ed3144e6b092f50ce99b0450d242a43309e1bd4`
  plus the maintained filesystem-removal and directory-enumeration contracts.
- AllowedInput: finite argv text and filesystem states accepted by `IO.dfy`;
  ordered operands; `-p`/`--parents`, deprecated `--path`, `-v`/`--verbose`,
  `--ignore-fail-on-non-empty`; bundles, long abbreviations, `--`, help, version,
  missing operands, invalid options, and unexpected option values.
- EnvironmentProfile: Linux, C locale, UTC0, native process credentials and
  filesystem permissions. Fixtures stay inside bounded benchmark workspaces.
- Observation: exact stdout/stderr bytes and exit status 0/1; the full modeled
  filesystem after ordered operands, including retained earlier removals,
  inode aliases, permissions, ownership, contents, and link topology. Output
  failures retain filesystem effects, commit exactly the modeled byte prefix,
  report stdout write errors, and force exit 1. Input is not consumed. Time
  updates remain native observations under shared contracts.
- TrustedOperations: `RemoveDirectory`, metadata tests, `OpenDir`/`ReadDir`/
  `CloseDir`, quoting, errno strings, and output writes. The implementation owns
  parent-chain traversal, stopping conditions, failure suppression, diagnostics,
  operand order, and CLI compatibility. `IsSymlink` before enumeration implements
  GNU `directory_status`'s terminal `O_NOFOLLOW` check using existing operations.
- OptionsLeftOut: none. The supplied operations express every rmdir option.
  As with other utilities, the shared entry API abstracts libc stdout buffering
  and does not expose GNU `close_stdout`'s separate flush/close observation.
  The World API has no signal-delivery or signal-termination operation; exits
  caused by signals are outside this model.

## Specification and proof

`RmdirSpec.Spec` constrains successful returns. A finite sequence of removal
records describes one operand's parent chain. Relations fix each removal through
`IOContract.RemoveDirectorySpec`, connect adjacent filesystem states, require
successful predecessor removals and mathematical dirname ancestry, and require
the final chain element to fail or exhaust the requested ancestors. Byte
partitions fix exact output order without a second execution algorithm.
`BatchEffect` connects these chains in operand order through existential
intermediate filesystems. One unignored failure fixes the exit status to 1.

Verbose records describe attempts, including failures, before the primitive
removal. Nonempty failures `ENOTEMPTY`/`EEXIST` are directly ignorable. Access,
permission, read-only-filesystem, and busy errors are suppressed only after a
successful observation of a nonempty directory; unreadable empty directories
still fail. The terminal-symlink/trailing-slash diagnostic follows GNU's stat
condition and distinguishes symlinks to directories, missing targets, and files.
Parent `ENOTDIR` uses `failed to remove`, while other parent failures use
`failed to remove directory`.

Core and entry `RunCore` directly ensure `Spec`. Their conditional frames modify
stdout/stderr for information requests and missing operands, and filesystem,
stdout/stderr plus temporary directory handles for actual removals. Removal
helpers modify only the filesystem and temporary directory handles; output is
assembled in attempt order and committed through the existing stream contracts.
All other IO invariance follows from the frames. Finite-input termination uses operand
count and strictly shorter lexical parent paths; no depth budget is used.
The CLI parser remains the repository's trusted boundary; the utility normalizes
GNU's identical-value `--path`/`--parents` abbreviations before parsing and retains
original tokens for diagnostics.

## Validation

Integrated `make check TASK=rmdir` passes on its unchanged before/after source
manifest. It includes compilation, 61 strict runtime oracle cases, the mandatory
short fuzz campaign, all 31 declarations and 746 verification conditions, and
the four marked Spec/Core/Proof/Entry module checks. Runtime comparisons require
exact stdout, stderr, exit status and complete normalized filesystem state;
they are separate from Dafny proof results.

The final gate uses the approved nonnegative `ReadDirContractFields` error
domain and local proof guidance for a previous module timeout. Specifications,
input scope, executable behavior and verifier limits are unchanged.

The rebuilt native quoting version also passes seeds 1, 7 and 19 with 1000
cases per seed, with no mismatches, timeouts or other errors. Commands run from
`/workspace/tmp/fs-benchmarks-20261020/integration` with
`PYTHONPATH="$PWD/src:$PWD"`; the full campaign command is
`python3 tools/coreutils_fuzzer/run.py fuzz rmdir --seeds 1,7,19 --iterations 1000`
with its recorded metrics output. The existing comparator is unchanged. The
3,000-case campaigns precede the later ghost contract and proof refinements;
utility execution, native IO, generators and comparison rules are unchanged.
The final contribution gate rebuilds and reruns all strict oracle cases and
its mandatory short campaign.

Current-workspace evidence is outside public task resources under
`/workspace/tmp/fs-benchmarks-20261020/evidence/`:
`final-gate-rmdir-approved-v4/rmdir.log`, its source manifests and exit records contain
the final gate; `quoting-runtime-v2/rmdir/` contains the three campaigns; `rmdir/`
retains local checks and earlier failed approaches. `rmdir-proof-final/` records
the proof refinement and its failed attempts. The separate approved shared-core
closure in `core-approved-closure-v5/` passes 598 declarations and 3640
conditions with unchanged sources. Public-profile and development checks are
recorded separately from utility proof and runtime results.

Canonical verification uses Dafny 4.11.1+10dca3ba4a2909c11299176440401fc31413b53d, seed 42,
isolated assertions, the existing 30-second VC limit and 100-second declaration
bound. The marked module tests retain their existing helper defaults.
Runtime tools are .NET SDK 8.0.131, Python 3.12.3, pytest 9.1.1 and
Rust/Cargo 1.94.0. Docker uses `dafnyutils-coreutils-fuzzer:latest`, image
`sha256:de0f320f6e639a6d4ad09ecea7513a8b2bdeedd6137f15abc1e3ef843f94be76`,
uid/gid 1000 and the pinned GNU revision above. `Tests.py` belongs to the
benchmark oracle/scoring tier; no development temporary-directory tests were
added.
