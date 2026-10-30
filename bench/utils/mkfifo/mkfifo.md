# mkfifo

## NL specification

Source:
- `coreutils/doc/coreutils.texi`, `@node mkfifo invocation`, lines 10848-10886
- Implementation: `coreutils/src/mkfifo.c` at submodule commit
  `2cf491412c199e2211880ec3f4ba387026638a33`
- License: GPL-3.0-or-later

`mkfifo` creates a FIFO, also called a named pipe, for each NAME. A FIFO is a
special file: one process opens it for writing and another for reading, and
data then flows between them as through an anonymous pipe.

```text
mkfifo [OPTION]... NAME...
```

- `-m MODE`, `--mode=MODE`: set the permission bits of each created FIFO to
  MODE. MODE is octal or symbolic as in `chmod`, starts from `a=rw`, and must
  specify only file permission bits.
- `-Z`, `--context[=CTX]`: set an SELinux or SMACK security context. These
  are outside this benchmark (see below).
- `--help`, `--version`: print information and exit.

Without `-m`, a FIFO gets `a=rw` minus the process umask. The exit status is
0 when every FIFO was created and, with `-m`, received its permissions; it is
1 after any failed operand, an option error, a missing operand or a rejected
MODE.

## Scope

This benchmark creates one FIFO per operand, in command-line order. It supports
`-m MODE` / `--mode=MODE` with octal and symbolic modes, unique long-option
abbreviations, options after operands, `--`, `--help`, `--version`, and GNU
parsing diagnostics. A failed operand does not roll back earlier FIFOs or
prevent later operands from being tried.

- Reference: GNU coreutils `src/mkfifo.c` at
  `2cf491412c199e2211880ec3f4ba387026638a33` and gnulib `lib/modechange.c`
  (`mode_compile`, `mode_adjust`) at `83730551b451b43577531986a5c4300e0166c42f`;
  upstream test `tests/misc/mknod.sh` (its `mkfifo -m 734` and
  `mkfifo --mode='ug+rw,o+r'` cases); GPL-3.0-or-later,
  <https://www.gnu.org/software/coreutils/>.
- Model/API revision: repository revision
  `3c704ee78884a4e764354431bb72b27771c02980`; shared `bench/core/IO.dfy` and
  `IOContract.dfy` are the trusted native boundary.
- AllowedInput: finite sequences of Linux paths representable as UTF-8 strings,
  including empty operands, repeated paths, relative/absolute paths, trailing
  separators, missing parents, existing names and dangling symlinks. Embedded
  NUL is outside the native argv domain. `-m` may appear before or after
  operands and more than once; the last one is used. Any MODE string is
  accepted as input; whether it is valid is defined in [MODE](#mode).
- EnvironmentProfile: Linux, C locale, `TZ=UTC0`, and the filesystem,
  credentials and umask supplied by the shared IO model. The mode, ownership,
  timestamps and storage of a created FIFO are request-bound trusted
  observations of `CreateSpecialNode`, not a simulation of the POSIX policy.
- Observation: exact stdout/stderr bytes and exit status, the resulting
  namespace and FIFO inode metadata, and partial effects: a FIFO whose
  permission change failed stays in place. Standard input is not consumed.
  Standard output is written only by `--help` and `--version`.
- TrustedOperations: one `CreateSpecialNode(path, FIFO, mode, 0, 0)` call per
  operand, where `mode` is `0666` without `-m` and the computed MODE result with
  `-m` (the native call applies the process umask); after each successful
  creation, and only when `-m` is given, one `SetFileMode(path, false, mode)`
  call, which is GNU's `lchmod`; `GetUmask`; GNU path quoting; C-locale errno
  text; and stream writes. MODE parsing and evaluation, operand iteration,
  diagnostic order and the exit policy are implemented and proved.
- OptionsLeftOut: `-Z`, `--context[=CTX]` (see below).

## Options left out due to IO.dfy

| Option | Missing API support and source evidence |
| --- | --- |
| `-Z`, `--context[=CTX]` | `src/mkfifo.c` checks whether SMACK or SELinux is enabled and then calls `selabel_open`/`defaultcon`, `setfscreatecon` or `smack_set_label_for_self`. `IO.dfy` has no operation for the kernel's security-module state, file labels or the default creation context. On a kernel without SELinux/SMACK, GNU ignores `-Z` and `--context` and warns for `--context=CTX`, but that depends on kernel state the model cannot observe. This matches the `mkdir` decision. |

These are model limits, not approximated behavior. Informational help keeps the
pinned GNU program's complete text. The generator restricts option pools to the
supported domain.

## MODE

MODE is evaluated once, before any operand is processed, starting from `a=rw`
(`0666`).

- Octal: the whole string is octal digits with a value of at most `07777`. The
  result is exactly that value; the umask does not apply, because GNU sets the
  permissions again with `lchmod` after creation.
- Symbolic: one or more clauses separated by `,`. A clause is `[ugoa]*` followed
  by one or more actions. An action is `+`, `-` or `=`, followed by `[rwxXst]*`
  (possibly empty), by one of `u`, `g`, `o` (copy that class's current bits), or
  by octal digits. Octal digits are allowed only when the clause has no `ugoa`
  letters and the action is the last one in its clause; such an action affects
  every mode bit. Actions apply from left to right. Without `ugoa` letters, the
  umask limits the change. `X` adds execute bits only if an execute bit is
  already set, because a FIFO is never a directory.
- Invalid MODE: if no expression of this grammar spells the string, mkfifo
  writes `mkfifo: invalid mode`, exits 1 and creates nothing.
- Special bits: if the result has a set-user-ID, set-group-ID or sticky bit,
  mkfifo writes `mkfifo: mode must specify only file permission bits`, exits 1
  and creates nothing.
- Both MODE errors are reported only after at least one operand is present;
  `mkfifo -m bad` reports the missing operand instead.

Examples with umask `022`:

| MODE | Result |
| --- | --- |
| `0644`, `00000000644` | `0644` |
| `=rw,+x` | `0755` |
| `-w` | `0466` |
| `+644,u+x` | `0766` |
| `+X` / `u+x,+X` | `0666` / `0777` |
| `o+s`, `g+t` | `0666` (no effect) |
| `+s`, `u+s`, `+t`, `7777` | special-bits error |
| `10000`, `8`, empty, `u`, `+ur`, `u+644`, `+644u`, `u+r,`, `,u+r` | `invalid mode` |

## Specification and proof

- SpecificationEntry: `MkfifoSpec.Spec` relates each ordered operand to its
  trusted creation effect and, when `-m` is given and creation succeeded, its
  permission-change effect. Existential intermediate filesystems retain all
  effects; byte partitions determine exact stderr. The MODE relation is stated
  as abstract syntax, a `Render` function and a `Meaning` function, without a
  parsing algorithm: a string is valid iff a well-formed expression renders to
  it, and the result is that expression's meaning.
- Proof of MODE: Core's parser is proved to invert `Render`
  (`Parse(Render(e)) == Some(e)` for every well-formed `e`, and a successful
  parse renders back to its input). This makes the `invalid mode` decision exact
  and shows that a valid string has one meaning. At run time the parser and
  `Meaning` are computed by loops over string indices (`ParseMode`'s
  `by method` and `ComputeMeaning`), proved equal to the recursive definitions,
  so the call depth does not grow with the length of MODE.
- Frame: `RunCore` modifies only `fsRegion` and `stderrRegion`. Its
  specification also reads `nowRegion`, `umaskRegion` (the umask the native
  creation applies), `propsRegion` (the umask value `GetUmask` returns, used to
  evaluate MODE), `trustedFilesystemRegion`, `trustedNativeFailuresRegion` and
  `trustedStreamsRegion`. The specification states that standard output is
  unchanged; mkfifo writes it only for help and version, which exit early.
- TerminationPolicy: MODE parsing and the operand loop terminate for every
  finite input. The shared CLI runner and parser keep their existing
  nontermination/trusted boundary; CLI termination is not established.
- CLI boundary: help/version, parse errors and missing-operand requests use
  early-exit plans; parsing remains the shared trusted boundary. `RunCore`
  directly ensures `Spec(raw, io, exit)` for every decoded command with at
  least one operand, including both MODE errors.
- Normal/error behavior: a successful operand writes nothing. A failed creation
  writes `mkfifo: cannot create fifo <name>: <errno text>`; a failed permission
  change writes `mkfifo: cannot set permissions of <name>: <errno text>` and
  leaves the FIFO in place. `<name>` uses GNU quoting. Later operands are still
  tried. Exit is 0 iff every operand succeeded and the stream writes succeeded,
  and 1 otherwise.

For example, with umask `022`, `mkfifo -m 600 pipe` creates a previously absent
FIFO `pipe` with mode `0600`, writes nothing and exits 0.

The specification rejects success for an existing name, a creation request with
a different mode, a missing or extra permission change, a permission change
after a failed creation or one that follows a symlink, reordered or missing
diagnostics, rollback of earlier FIFOs, stopping before a later operand after an
error, and creating anything after an invalid MODE.

## Contribution and review evidence

The pull request records the tested commit, the artifact hashes, the fuzzer
image and the full outputs. The results below were measured from base revision
`3c704ee78884a4e764354431bb72b27771c02980` in the contributor container on
Linux x86-64: Dafny 4.11.1+10dca3ba4a2909c11299176440401fc31413b53d, .NET SDK
8.0.132, Python 3.12.3, pytest 9.1.1, Ruff 0.15.12, Rust/Cargo 1.94.0, Z3 4.16.0.

- Tests: `make -C bench/utils/mkfifo test` passes 153 runtime cases against the
  pinned GNU build, comparing stdout, stderr, exit status and the resulting
  filesystem, including the two `mkfifo` cases of `tests/misc/mknod.sh` and
  MODE strings of 100,000 characters.
- Fuzzing: `python3 tools/coreutils_fuzzer/run.py fuzz mkfifo --seeds 1,7,19
  --iterations 1000` completed 1000 matches per seed with no mismatch, timeout
  or other error; option coverage was 4/4 singles and 6/6 pairs for each seed.
- Verification: `make -C bench/utils/mkfifo verify` verified every declaration
  with no failure, using the repository's isolated assertions, 30-second
  condition limit and 100-second declaration limit. Termination of MODE parsing
  and the operand loop is proved.
- Final gate: `python3 -m benchmarks validate mkfifo` reports `mkfifo: valid`, and
  `make check TASK=mkfifo` reports `mkfifo: checks passed`.

The fuzzer's filesystem snapshot previously rejected FIFO nodes; this
contribution records them from metadata only. A failed permission change after
a successful creation is specified and proved but cannot be produced by the
current fixtures. A maintainer still decides whether the specification is
accepted.
