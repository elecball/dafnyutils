# Trusted API failure modeling

This is repository maintenance from `db4886a`, not an evaluated benchmark run.
No evaluator-only records, hidden tests, or reference solutions were used.
Implementation, proof, native, and oracle results are recorded separately below.
The typed directory core and completed Pwd/Readlink/Chmod/Ls callers are applied
in the isolated worktree. Their final verification and native records follow.
Historical path-only cwd proposals are superseded and are not the final API
design; no user authorization decision is pending.

## Stream boundary

`StreamErrorPolicy` and both policy constructors have been removed.
`ReadStdin()`, `WriteStdout(bytes)`, and `WriteStderr(bytes)` always return an
`IOResult` with a native errno and the consumed or committed prefix. The native
adapter does not throw to bypass a modeled stream failure. A stdin read exposes
its exact unread suffix. Public results are `Ok` exactly when their errno is zero.

Utility implementations and proofs retain their algorithms and final
`RunCore ==> Spec(...)` obligation. A utility-owned output finalizer checks both
write results. Its principal relation binds each actual request to the immutable
stream observation, preserves the committed prefix, specifies the utility's GNU
write-error diagnostic, and fixes the exit status even when stderr fails.
Fixed diagnostic text remains in Spec. Pinned `gnulib/lib/closeout.c` explains the
ordinary GNU deferred-write policy; output planning is not a trusted primitive.
The shared `CliEarlyExit` shell also checks both results and appends the named
GNU write-error diagnostic after its planned diagnostics when stdout fails.

## Native API audit

`trustedNativeFailures()` selects an exact errno for an operation and its prior
modeled state and operands. The selected errno must satisfy that operation's
finite domain. A model-resolvable input can therefore encounter a real access,
I/O, allocation, descriptor, or storage fault. Success retains the exact target,
metadata, filesystem effect, and resource transition. Membership in an allowed
error set alone cannot justify a utility failure: its principal relation must
retain the actual observed request.

| Boundary | Result and preserved semantics |
| --- | --- |
| `GetCwd` | `IOResult<Path>` from libc `getcwd(NULL, 0)`, with immediate saved errno and `free` on success. No `"."` substitute. The typed directory request binds the real position and occurrence; an unnamed position cannot produce a successful pathname. |
| `GetFileMode`, `IsDirectory`, `IsSymlink` | Exact native errno per query; successful mode/type remains exact. |
| `GetFileStatus` | Exact native error plus the existing ordered time observation. Path status advances its cursor even on failure. |
| `GetOpenDirectoryStatus` | Descriptor-specific native error; successful identity/status unchanged. Its legacy success-only status-cursor policy remains explicit. |
| `ReadLink`, `ResolvePathIdentity` | Exact error and successful target/identity. Embedded NUL is rejected before the ABI; an ordinary-file readlink retains EINVAL. |
| `CreateSymlink`, `DeletePath`, `SetFileMode`, `RenamePath`, stdout timestamps | Exact request-bound error, strong successful effects, and failure frames. Unsupported symlink chmod remains EOPNOTSUPP; immediate native errno is retained. |
| `OpenDir`, `ReadDir`, `CloseDir` | Exact operation/handle-state errors. Close returns `IOResult<Unit>` and consumes an owned handle on both outcomes. Invalid legacy handles return EINVAL. |
| Cwd-relative and descriptor-relative status, mode, readlink, open | Exact raw operands, authenticated starting position or owned parent, and operation ordinal. Success refers to the actual target record, including unnamed live objects. |
| Live opened-directory status | The actual libc `statx` result, including ENOSYS if libc returns that error. It advances both context and status ordinals on either outcome. |
| `Now`, environment, umask | Supplied process-context observations. POSIX umask is observed and restored; no new failure algebra is invented for these immutable supplied values. |
| Formatting and legacy path adapters | Invalid environment keys are rejected, a wide errno formats numerically, NUL paths are rejected, and metadata preserves ENAMETOOLONG. |

`ReadFile`, `ProbeReadFile`, stdin, standard-output writes, and rich filesystem
write/append operations already carry explicit errors and partial results.
Write and close failure preserve the committed prefix and any creation,
truncation, or append effect. `WriteFileSpec`/`AppendFileSpec` bind the full
receipt and resulting filesystem to the exact request. Their existential lower
projections cannot replace those bound relations in a principal specification;
Tee and Csplit now retain the rich write and cleanup observations.

GNU cleanup policy does not report every cleanup error. Pinned
`gnulib/lib/fts.c`'s `closedir_and_clear` ignores the cleanup result, while
`src/system.h`'s `directory_status` saves the readdir errno before closing.
Rm/Rmdir retain the exact close result and consumed handle while preserving the
GNU primary decision. Rmdir's pre-existing IsSymlink-plus-following-open
approximation of `O_NOFOLLOW` remains documented: a failed preliminary query
can precede a following open. Its failure is explicit; no fallback heuristic is
added.

## Authenticated directory state and cwd recovery

The old filesystem still requires namespace-reachable inodes. An additive
`LiveDirectoryTopology` carries full records for live unnamed objects and a
`DirectoryPosition` token distinct from host inode identity, so separate live
positions need not collapse when their host keys agree. A named node has a genuine canonical namespace path; an unnamed node
has no executable pathname substitute. Raw `d_ino` observations may be zero and
need not equal a mounted child's stat inode. Optional dot observations are
modeled separately.

`DirHandlesRegion` contains one validated `DirectoryResources` value: the exact
legacy handle map, authenticated opening snapshots, and live directory state.
Legacy and live keys are disjoint, without a sign restriction on the abstract
handle type. Every arbitrary legacy map has a constructive initial resource
witness. The native legacy allocator uses unbounded positive `BigInteger` keys,
and the independent live registry uses decreasing keys; real libc descriptors
remain `int`. The model does not infer ownership from the sign of a key.

`cwdContext()` exposes the actual topology, current position, operation ordinal,
live capabilities, and exact legacy handle/origin maps. Its `hint` field is the
unchanged historical `cwd()` observation and is never a runtime fallback.
Read-only relative operations advance only the context ordinal. Mode changes
update the selected host object's mode and change time in both visible records
and live topology, including detached objects. Opens capture authenticated
anchors and entry sets; closing consumes only the selected capability.
Resource constructors and state-transition witnesses are proved rather than
asserted as native postconditions.

Relative resolution starts at the authenticated cwd or held parent directory.
It does not recheck unrelated ancestors or re-follow an alias prefix, which
matters after GNU chmod changes directory permissions in preorder. A successful
target is a `CwdTarget`; its optional named path is present only when the object
is genuinely namespace-reachable. Raw operands and symlink components are not
lexically normalized. New descriptor operations require an authenticated current
anchor for an owned relative parent; old API and CLI domains are unchanged.

`GetCwd` is a raw fallible primitive. GNU pwd recovery remains utility-owned:
status of root/current directory, parent open, dirfd, fchdir or the source's
chdir fallback, fstat/lstat, ordered entry search, and checked close. The exact
receipt chain preserves earlier readdir errno over close errno, conditional
lstat for zero/cross-device raw inode, memory-error precedence, and the real
cwd movement. Ls, Readlink and Chmod avoid their unnecessary cwd pathname query
through the relative primitives instead of inventing a cwd error diagnostic.

Live directory reads have an occurrence ordinal and an exact observed
`remainingAfterReadError` subset. They admit entry advancement on readdir
failure, including EOVERFLOW, while retaining real errno. This replaces the
legacy error-state abstraction for the new clients; it is not a claim that the
legacy `ReadDir` API itself gained temporal retry semantics.

## Model boundaries

Observation providers are functions: identical request keys select the same
result. New typed cwd/directory operations carry an occurrence ordinal and old
path status calls carry their status ordinal. Legacy mode/readlink/mutation and
zero-commit stream retries can repeat a key and therefore cannot independently
change a transient result. The old opened-directory status cursor advances only
on success. No general per-syscall or live-kernel temporal completeness is claimed.

The legacy metadata/readlink/mode/open contracts accept arbitrary paths but
project relative spellings from the model namespace root; their native adapters
use the process cwd. New authenticated APIs fix their explicit clients, not all
legacy relative-path correspondence, particularly after cwd movement. The source
inventory and native identity experiment are retained in
`cwd-relative-api-proposal/legacy-relative-audit.md` and its JSON/log companions.
No old input domain or precondition was narrowed to conceal that inherited limit.
The new typed mode/open effects also prove their before/after context transport.
Arbitrary legacy filesystem mutations do not gain a general token-identity
transport theorem between the model's FS-indexed directory views. The four
affected utility closures read the filesystem or use the typed mode operation.

Primitive contracts describe library operations. They do not require a raw ABI,
descriptor-state, or syscall-order witness. Whole-stdin reads do not implement
Head's bounded read protocol; utility output plans do not reproduce every stdio
flush phase or Tee's read/write interleaving. Public standard-stream operations
do not close the standard capability or return a separate close receipt.
These are model boundaries, not outstanding approval questions or claims of full
libc parity. Existing file `CloseFailed` receipts do require exact partial-data
and diagnostic handling, and the concrete omissions below were repaired.

GNU Base64 decoding had a concrete partial-read parity gap. Pinned
`coreutils/src/basenc.c` lines 248 and 1582–1613 fill a 4096-byte encoded-input
buffer and check `ferror` before decoding that buffer. Previously completed
buffers can already have produced output. The decoder carries incomplete
quartets between buffers (`gnulib/lib/base64.c`, lines 452–460 and 466–549),
and `--ignore-garbage` filters bytes before deciding whether a buffer is full.
The former whole-read path transformed every returned partial byte as though
that partial data ended at EOF. Actual EIO injection after eight encoded bytes
produced `abcd` in the candidate while GNU emitted no output; an invalid partial
buffer also added an invalid-input diagnostic that GNU never reached. The former
file-error branch separately discarded `ReadFailure.partial`: with
EIO after reading an existing 524-byte source operand, GNU encoded 710 output
bytes and the candidate encoded none. The narrow file-input correction now
preserves that actual prefix using `ReadFailureData`; all seven affected proof
scopes pass, the supported native rebuild passes, and the repeated encoder EIO
comparison now matches GNU exactly.

The applied decoder correction relates the returned input to its maximal prefix
of complete 4096-byte buffers, after garbage filtering when requested. On
`ReadFailed`, it decodes only complete quartets in that prefix, preserving output
from earlier buffers and carrying quartets across buffer boundaries without an
EOF flush. `CloseFailed` still decodes the complete input and its final partial
quartet. An invalid decoded quartet takes diagnostic precedence over later read
or close errors. The independent Core and Spec relations retain the valid one-
or two-byte prefix before an invalid third or fourth character, respectively.
These are source-derived buffer and decoder semantics, rather than an arbitrary
input-length cutoff. Twenty bounded normal/error comparisons and the unchanged
registered GNU oracle pass; the final supported full Dafny gate passed 1891
obligations across 104 selected declarations with zero failures.
The last focused partition checks establish 35 obligations across five nonzero
declarations; two zero-target selections are excluded. Broader ordering and
standard-stream finalization remain separate model boundaries.

The native whole-stream helpers retry `EINTR` internally
(`IOExtern.ReadAllFromFdWithOutcome` and `WriteAllToFdWithOutcome`), while the
existing raw capability operations preserve individual native results. This is
a source-derived abstraction boundary, not a confirmed interruption-parity test;
no additional EINTR fault experiment was run. Ordered native observations must
state which layer owns retries before claiming complete interruption behavior.

Standard-stream finalization is another source-level boundary. Public whole-stream operations expose read and write
results, but neither close the standard capability nor return a close receipt;
`IOExtern.Exit` calls `Environment.Exit`. The raw native `CloseCapability`
operation has no corresponding public Dafny operation. GNU Base64 explicitly
closes input (`basenc.c`, lines 1469–1481), and `closeout.c` closes stdout and
stderr. A successful read or write followed by a close failure is therefore not
currently a public modeled event for these streams. No extra close-fault probe
or new primitive was added, and no complete finalization-parity claim is made.

Base64's existing file-read API does expose `CloseFailed`. A bounded native
close-EIO probe on the same 524-byte source operand initially confirmed equal
710-byte output and exit one, but GNU printed the operand name where the
candidate printed `read error` (`base64-production-probes/file-close-fault.*`,
exit one). The applied formatter correction distinguishes that existing stage;
the rebuilt close-EIO and read-EIO cases both match GNU exactly. Standard-input
close is not an event in the current public whole-stream API.

Head and Tail also discarded file data retained by an existing `CloseFailed`
receipt. Pinned `head.c`, lines 878–898, reports `failed to close`; `tail.c`,
lines 2078–2088, reports `error reading`. Current-source supported builds first
confirmed both candidates lost the verbose header and selected 16 bytes from an
existing 524-byte operand. The narrow correction preserves those exact bytes
and header on that stage, retaining the nonzero status and each utility's
source-derived diagnostic. Matching declarative relations and proof branches
are updated. Supported rebuilds and one exact close-EIO comparison per utility
now pass (`head-tail-close-probes/{head,tail}-after.*`), with pre-fix failures
retained as `*-before.*`. All 20 affected nonzero declarations passed focused
checks. Supported complete gates then passed Head 1149 obligations across 82
declarations and Tail 1192 obligations across 70 declarations, both zero errors
(`head-supported-close-stage.log`, `tail-supported-close-stage.log`, exit zero). The unchanged supported oracle suites
passed 48 Head and 58 Tail cases, each with one pre-existing deferred-host-effects
skip and five `dafny_verify` deselections (`head-tail-close-probes/*-oracle.*`).
Their conditional build fixture reused the existing pinned GNU binary and
current supported candidate build through documented overrides. General
read-error selection and standard-stream close
are not silently changed by this stage correction.


## Validation record before the joint directory context

Working directory: `/workspace/tmp/trustbase-cli-20261020/failure`, isolated branch
`agent/trustbase-cli-20261020/failure`, based on `db4886a`. Python commands use
`PYTHONPATH` pointing at that worktree's `src`, because the installed editable
package otherwise resolves the root checkout. Relevant environment versions:
Python 3.12.3 and `dafny-benchmark`
`4.11.1+10dca3ba4a2909c11299176440401fc31413b53d`; experiments use tmux 3.4,
.NET SDK 8.0.131 and strace 6.8. The read-only GNU build reports
`9.10.13-2cf49`; source HEADs are coreutils
`2cf491412c199e2211880ec3f4ba387026638a33` and its gnulib
`83730551b451b43577531986a5c4300e0166c42f`. The root checkout's pre-existing
untracked `m4/extern-inline.m4` was preserved; no GNU source was modified.

Evidence is outside the repository in
`/workspace/tmp/trustbase-cli-20261020/` and is available in this workspace.

- Focused no-policy stream wrapper verification:
  `dafny-benchmark verify --standard-libraries:false --cores:2
  --filter-symbol:BenchIO.IO.<method>. bench/core/IO.dfy` for `ReadStdin`,
  `WriteStdout`, and `WriteStderr`: each passed with two verified obligations and
  zero errors. Logs are `core-ReadStdin.log`, `core-WriteStdout.log`, and
  `core-WriteStderr.log`, with matching `.exit` files.
- A direct pre-directory-composition core queue checked 107 changed declarations without treating
  core as a library (`checks/core-current-*.json` and matching logs). It selected
  67 nonzero targets and reported 812 verified obligations; 40 zero-target
  selections are explicitly excluded. Sixty-four nonzero declarations passed.
  `GetFileMode`, `IsDirectory`, and `IsSymlink` retained postcondition timeouts
  under the unchanged 30-second limits, so the queue is not an all-core pass.
  Scratch body guidance subsequently passed their exact declarations with
  unchanged headers. The nine local proof lines were then applied during a
  snapshot-free window; production checks passed GetFileMode four, IsDirectory
  three and IsSymlink three obligations without `--library`. The frozen IO
  source SHA256 is
  `c91f4496c5aa12b812af923d72db7117a813c8b6bc1e608c947c670bc74e990f`.
  The original timeouts remain recorded. This evidence is separate from utility
  verification, where core is passed as `--library`.
- Supported `make -C bench/utils/pwd verify` subsequently passed all 304
  obligations across 27 declarations (`pwd-supported-current.log`, exit zero).
  The supported `make build TASK=pwd
  BUILD_DIR=/workspace/tmp/trustbase-cli-20261020/pwd-native-build` passed. Three
  fixed-path native comparisons with the pinned GNU binary passed: ordinary
  output, stdout redirected to `/dev/full`, and stderr redirected to `/dev/full`
  with an ignored operand. They compare exact bytes and status; they do not
  establish Dafny verification of the native adapter.
- All eight owned utility finalizers (`pwd`, `stat`, `du`, `readlink`, `ls`,
  `link`, `unlink`, `touch`) passed focused checks. Link and Unlink now use
  suffix plans with exact named prepared read regions; their repaired wrappers
  passed 38 obligations each. The Ls suffix-plan wrapper passed 39 obligations
  before ownership transferred to the metadata migration agent.
- Reviewed mode binding proposal: canonical seed 42, isolated assertions, 30s
  limits; GetFileMode passed 46 obligations and its NUL probe passed three.
  Native build and run passed with EINVAL 22. The exact applied patch hash was
  `04c978685ef290de72eb5686a220566f77bd391570a3587ac4e7752e1d80c09b`.
- Reviewed metadata/close proposal: GetFileStatus 53, IsDirectory 46,
  IsSymlink 46, CloseDir 47, GetOpenDirectoryStatus 60, provider 78, projection
  lemmas 5/14/29/44, probe Main 16 and InvalidClose seven obligations all passed
  with the same canonical options. Native build/run passed and printed
  `22,22,22,22`. The exact applied patch hash was
  `f4fc175a788a172d79b8d61d0309417d5c1501a4afd636a5272e4d65dc8e4049`.
  A namespace-only probe filter selected zero obligations; that run is excluded
  from verification evidence and was replaced by exact method filters.
- Reviewed path proposal: ResolvePathIdentity passed 51 obligations and the
  NUL-path probe passed seven. Native build/run passed and printed `22,22,22`,
  including readlink of an ordinary file. The exact applied patch hash was
  `40d7bd64484b256d6b05caae50807b5c7b5eb6f0399fe84d2ade4aae9d2ffc08`.
  The pure result helper has no verification obligations; its zero-target output
  is not counted as a proof result.
- Reviewed mutation/stdout-time proposal: CreateSymlink seven obligations;
  DeletePath, SetFileMode, RenamePath and each of four stdout setters six each;
  provider 78, filesystem failure witness 235 and NUL probe 21 all passed with
  the canonical options. Native build/run passed with five EINVAL 22 results.
  Exact applied patch:
  `0c87846447b1b9189ceea8a9924bbaa958cd56df1529e46685f00114330d138b`.
- Reviewed directory proposal: OpenDir eight, ReadDir 62, probe Main eight and
  InvalidRead six obligations passed. Native build/run passed with EINVAL
  `22,22`. Exact applied patch:
  `47264d379da38ee64fdc693141fc13617fb879197996432462acd085a338f094`.
- Reviewed process-context adapter proposal: invalid-key lemma three and probe
  Main 25 obligations passed. Native build/run passed: both invalid keys return
  Err, repeated umask observations agree, and the wide errno formats as
  `Unknown error 9223372036854775808`. Exact applied patch:
  `a4d1dd671c709105906a23efab9173d3666cd38eac487b7976005c00f1fcc5e1`.
- Reviewed stdout errno-capture correction: the focused probe passed six
  obligations, and native compilation succeeded. Injecting EBADF into the actual
  `utimensat` call produced native errno nine; an overflowing timestamp returned
  EINVAL 22. A startup-closed descriptor probe was excluded because the CLR could
  reuse that descriptor before the call. Exact applied patch:
  `2e9c04148843a1733e830103408c0be1907469cd2440f18730653e21fd667637`.
- Exact native errno correction removed five task1-added zero-to-EIO
  manufactures in ReadLinkTarget, SetPathTimes, CreateSymlink, DeletePath and
  CloseDir. The applied patch SHA256 is
  `6a7b0de6cdbfe52f5c48f3d4fe145ca7c21cadc3658283e3128133688b3c9371`;
  production C# bytes equal the compiled/probed proposal. Native compilation
  passed and five actual syscall EIO injections preserved errno five, with
  each other result unchanged (`exact-errno-proposal/native-build-v2.*` and
  `native-faults.*`). The initial standalone-probe parse failure is retained
  separately. Pre-existing normalizations are outside this five-line correction;
  no Dafny contract or fixture changed, and no formal snapshot was invalidated.
- Base64's last independent wrapping bridge needed proof-helper triggers that
  cover arithmetic bounds as well as chunk equality. Its Core and Spec wrapping
  definitions remain separate and unchanged. The line projection passed 22,
  raw-field assembler 18 and final independent witness bridge 32 obligations;
  complete field visibility is needed when folding the Spec relation. The
  failed broad-hide and earlier chunk-only trigger attempts remain in scratch
  logs. The supported 95-declaration gate passed all 1804 obligations
  (`base64-supported-wrapping.log`, exit zero), including 35 obligations in the
  final wrapping bridge. This historical gate predates the decoder correction and does not establish
  the repaired partial-decoder behavior described above.
  Supported native Make build passed, and the unchanged supported Make oracle
  passed 46 cases with one existing skip for broader basenc alphabet and
  bounded-memory coverage, plus five existing `dafny_verify` deselections
  (`base64-native-supported.*`, `base64-oracle.*`, both exit zero). Documented
  current-DLL and pinned-GNU overrides avoided rebuilding the root checkout.
  A separate four-case native EIO probe passed the two encoder cases and failed
  both partial-decoder cases (`base64-production-probes/read-faults.log`, exit
  one). Each retained strace log confirms exactly one injected fd-zero read;
  these bounded inputs do not change oracle fixtures or benchmark datasets.
  Four additional buffer/context cases passed one and failed three
  (`read-buffers.log`, exit one; inputs at most 4100 bytes), demonstrating both
  surviving completed-buffer output and filtered-buffer boundaries. The single
  existing-file encoder case also failed (`read-file-fault.log`, exit one).
  The resulting three-line correction preserves the actual file-read prefix in
  Core and Spec using the existing result helper. ProcessInput 29, input bridge
  18, Prepare 103, prepared bridge 47, Core RunCore 80, final bridge 48 and public
  RunCore 15 obligations pass (`base64-file-prefix-*`). The supported native
  rebuild passes (`base64-native-file-prefix.*`), and the separately named
  encoder EIO rerun exactly matches GNU (`read-file-fault-repaired.*`, exit zero).
  The supported full gate after the file-prefix correction passed all 1804
  obligations across 95 declarations (`base64-supported-file-prefix.log`, exit
  zero) on the frozen core. The subsequent single-formatter close-stage
  correction retains both results and its final supported full gate passed all
  1804 obligations across 95 declarations (`base64-supported-close-stage.log`,
  exit zero). Its supported rebuild passed;
  both close-EIO and read-EIO reruns pass with exact GNU output, diagnostic and
  status (`file-close-fault-repaired.*`, `file-read-after-close.*`).
- Ls's reviewed handle-binding patch uses the actual initial handle map and
  one finite open/read/status/close receipt sequence. It preserves distinct
  entry observations, ordering, rendered output and the consumed handle frame.
  Native directory diagnostics now use the display operand; the serious-error
  flag is projected from the actual command-line directory operation results,
  retaining minor entry errors and serious recursive cycles. Six real syscall
  EIO injections match GNU exactly, including terminal read and close failures
  after names were collected; nine ordinary/descriptor checks also passed.
  Exact applied patch:
  `f6b8dfde601e9dbb26f06200f6ace1310b04d579ce8d88150dde6cc1b65e4aae`.
  Evidence is in `ls-bound-trace-proposal/`, with versioned
  `native-*-callhelpers.log` files. The first fault run reported two of six matches
  and exposed the path/severity mismatch. The rerun replaced that initial raw
  log; the earlier mismatch results are retained in the agent record, not
  presented as a separate surviving log. Focused traversal 350, operand 167,
  preparation 107, prepared bridge 35, Core RunCore 39, final bridge 27 and public
  RunCore 16 obligations all passed. The first supported production full gate
  passed declarations 1–71, then found a missing `dirHandlesRegion` read at
  `PreparedSummary` (`ls-supported-bound.log`, exit two). Adding that required
  footprint leaves its body and runtime unchanged; its exact declaration now
  passes 41 obligations (`ls-prepared-frame.log`). The second supported full
  gate passed declarations 1–21, then timed out in the collector's source
  assembly (233 verified, one timeout; `ls-supported-bound-frame.log`). Local
  membership/kind facts and short definition reveals confined to that assembly
  now pass all 241 collector obligations (`ls-collector-scoped.log`); a failed
  attempt with facts exposed to the whole loop is retained separately. A new
  final full gate passed all 3707 obligations across 168 declarations
  (`ls-supported-corefreeze.log`, exit zero) after the shared core source freeze. The supported native build passed. The unchanged supported Make
  oracle passed 266 runtime cases, with six existing `dafny_verify` cases
  deselected by the supported runtime selection (`ls-oracle-bound.log`, exit
  zero). Its conditional fixture reused the pinned GNU binary and the current
  external DLL through documented `EVAL_COREUTILS_BIN`/`EVAL_BENCH_DLL` overrides;
  the build override invokes the real supported Make build if the DLL is stale.
  Fixed oracle data, fixture code and scoring were not changed.
- Rmdir's exact directory/query trace passed its focused runtime and bridge
  checks before application of
  `08f81b680f2f6e21e0a03eb43d662902be9bd11418eb664d2951e7450e6011ae`.
  The subsequent GNU formatter correction passed supported full verification:
  785 obligations, zero errors (`rmdir-supported-formatter.log`). Its supported
  native build passed, and three fixed protected-path comparisons matched GNU,
  including `/dev/full` (`rmdir-native-formatter-parity.log`).
- Rm's applied exact directory trace was
  `73fcfcb73449ff2269f3abad4d673147fccbaa65acec27c138e2af539d03316d`.
  Focused ReadDirectory 152, hierarchy 169, Prepare 183 and RunCore 20 obligations
  passed. Native compilation exposed the C# backend's 16-argument arrow limit;
  a utility-owned immutable removal-scope record packages the same three values
  without changing a judgment. The corrected native build and four protected
  missing-operand GNU comparisons passed. Earlier one-worker full runs hit the
  Prepare wall-clock cap; local trace-only visibility guidance passed 183 focused
  obligations. The final supported gate with eight supplied processors passed
  all 1227 obligations (`rm-supported-processors8.log`); neither the public
  relation nor the limits changed.
- Touch's stronger principal trace removes the success-only projected alternative
  and binds stdout timestamp faults to the native request. Exact applied patch:
  `30353ad13c239de4e45033da5552658d473e0f7294a490159df2a7af1235ec20`.
  Focused Prepare 132, step bridge six, resolved bridge 73, prepared bridge 29,
  final bridge 35, Core RunCore nine and public RunCore 16 obligations passed.
  The final supported gate passed all 884 obligations (`touch-supported-bridge8.log`),
  including the date-source and inductive state-trace bridges. `make build TASK=touch` has an
  unconditional coreutils bootstrap prerequisite in this unpopulated worktree;
  the root's existing parser helper is read-only. A separately recorded direct
  native compiler invocation passed using that existing helper rather than
  mutating or rebuilding the root checkout; it is not reported as Make success.
  Nine bounded GNU comparisons passed, including four actual `utimensat` EIO
  injections for current/access/modify/fixed stdout timestamps. The initial
  absolute-argv0 usage-path difference is preserved separately; the final run
  passes GNU argv0 `touch`, with no output normalization. Logs are
  `touch-native-direct-build.log`, `touch-native-bounded-parity.log` and the
  corresponding `touch-*-utimens.trace` files.
- Native proposal artifacts and exact command scripts are in
  `native-failure-proposal/` under the external evidence directory. Production
  application followed exact patch inspection and proof/native evidence after
  earlier automatic approval review rejected broader unvalidated migrations.
  No rejected mutation was applied indirectly or split to bypass that review.
- The exploratory whole-core command `dafny-benchmark verify
  --standard-libraries:false bench/core/IO.dfy` reported two `ReadFile`
  assertions and nine timeouts. This is not a successful whole-core
  verification result; no timeout limit or proof coverage was changed.
- Parent-recorded baseline on unchanged revision `db4886a`: `pwd` supported
  verification passed; `stat` encountered a pre-existing timeout. Baseline and
  current results must remain separate. Later original Stat/Ls/Readlink runs also
  timed out; original Chmod failed its outer RunCore check. Those are not passes.

The following supported gates passed before the joint directory-context
replacement. They remain evidence for those recorded source snapshots; changed
Pwd, Readlink, Ls and Chmod callers require their new complete gates. All use the repository's declaration enumeration and final public
RunCore obligation, seed 42, isolated assertions and the unchanged 30-second VC
and 100-second target limits. Later reruns set `DOTNET_PROCESSOR_COUNT=2` to bound
solver concurrency; final Rm/Touch reruns supply eight processors (Dafny's default
four workers) after observing the aggregate one-worker bottleneck. Earlier timeout
and diagnostic failure logs remain available.

| Utility | Verified obligations | Evidence log |
| --- | ---: | --- |
| Pwd | 304 | `pwd-supported-final.log` |
| Link | 262 | `link-supported-final.log` |
| Unlink | 247 | `unlink-supported-final.log` |
| Mkdir | 360 | `mkdir-supported-resources.log` |
| Du | 594 | `du-supported-resources.log` |
| Readlink | 509 | `readlink-supported-guided.log` |
| Rmdir | 785 | `rmdir-supported-formatter.log` |
| Stat | 812 | `stat-supported-guided.log` |
| Rm | 1227 | `rm-supported-processors8.log` |
| Touch | 884 | `touch-supported-bridge8.log` |
| Base64 | 1891 | `checks/base64-buffer-full.log` |
| Head | 1149 | `head-supported-close-stage.log` |
| Tail | 1192 | `tail-supported-close-stage.log` |
| Ls | 3707 | `ls-supported-corefreeze.log` |

The separate cwd-relative Ls proposal also passed its supported Make gate across
168 declarations and 3765 obligations (`ls-cwd-full-proposal/supported-full-first.log`).
That exact source-only snapshot excludes scratch proof files. Its supported
native build and unchanged GNU oracle passed 266 cases. This unapplied proposal
uses the earlier AtCwd context and does not establish the forthcoming shared
identity/context correction; the final affected gates must use that final source.

Parent-recorded supported gates also passed with the same stable core and
unchanged limits: Factor 2209, Truncate 654, Tee 454, Expr 1571, False 228,
Printenv 556, Dirname 687, Nl 1100, Comm 2090 and Uniq 1425 obligations, all with
zero failures. Evidence is in the task's `checks/` directory, including
`factor-make-verify-repair1.log`, `truncate-make-verify-guided.log`,
`tee-make-verify-writebinding.log`, `expr-make-verify.log`,
`false-make-verify.log`, and the stable-core Printenv/Dirname logs. Parent-recorded
development units passed 106 tests with 15 deselected
(`checks/task1-units-current.log`); this is test success, separate from the
Dafny proof counts. Tr's supported native rebuild and six mixed-error PTY
comparisons passed (`checks/tr-native-mixed-error.log`).

Active and completed experiment commands are retained in the external scripts.
Relevant tmux sessions include `trustbase-failure-stat-errno2`
(`check_stat_failure_guided.sh`), `trustbase-failure-rm-local-guidance`
(`check_rm_prepare_local.sh`), `trustbase-failure-touch-supported`
(`check_touch_supported_full.sh`) and `trustbase-failure-touch-native-argv0`
(`check_touch_native_argv0.sh`). Native Touch uses the exact compiler command
`dafny-benchmark build --no-verify --output <external>/bench/touch_bench.dll
bench/utils/touch/dfyconfig.toml bench/core/IOExtern.cs`, with external MSBuild
outputs and the existing parser selected by `DAFNYUTILS_TOUCH_TIME_PARSER`.
Fault injection adds `strace -qq -f -e trace=utimensat -e
inject=utimensat:error=EIO:when=1`; each retained trace records the injected call.

The initial fixed-path native comparison batch passed 17 of 19 cases
(`owned-native-readonly.log`). Rmdir's affected three cases subsequently all
passed after its formatter correction; the shared Mkdir early-exit diagnostic
was subsequently corrected by the separately validated shared-entry patch. These manual checks use bounded memory, existing
read-only/protected operands and `/dev/full`; they create no temporary fixture
trees. They do not replace the original benchmark oracle suite. Several fixed
oracle modules unconditionally build GNU coreutils in this empty-submodule
worktree; that prerequisite is not bypassed or monkeypatched. Conditional oracle
helpers allow an existing GNU binary and candidate DLL, but no claim that their
whole suite was run follows from the manual comparisons.


## Joint-core validation checkpoint

The immutable direct-check source is `cwd-core-final-checkpoint/`; its
`source-state.json` records the 23 Dafny files and native adapter. The applied
six-file patch is `cwd-core-composition-proposal/joint-core-final.patch`, SHA256
`6f8a1002a3370d2061060e9ceb1d147a7d5889d20091e9841b85bd0435ee0284`.
`closed-core-callers-applied.json` confirms exact patch hashes and all six core
and 20 Pwd before/after source hashes. Readlink's reviewed patch was applied in
the same coordinated step, preserving all other changes. Pwd was subsequently
renamed to the required substantive `PwdCore`, `PwdSpec`, and `PwdProof` files
and modules. The canonical rename audit confirms normalized source equivalence.
The renamed production sources passed the complete supported Make gate again:
49 declarations and 1517 obligations with zero errors, followed by a successful
build and 19 unchanged GNU oracle cases (`checks/pwd-canonical-full.*`).

The complete changed-declaration union selected 235 declarations: 177 nonzero
scopes passed 5243 obligations with zero remaining errors or timeouts; 58
zero-target selections are excluded. Commands use no core `--library`,
`DOTNET_PROCESSOR_COUNT=8`, four solver workers, seed 42, isolated assertions,
30-second per-VC and 100-second outer limits. Sixty completed results were
preserved when switching the runner from two to four workers; two interrupted
logs are retained and excluded. The original immutable queue recorded two
30-second proof timeouts. Exact same-header local guidance then passed
`DirectoryStateAtSnapshotFields` ten and `ModeChangedRecordFacts` thirteen
obligations on the final combined source. Only those two proof bodies changed;
no contract, return expression, native behavior, or allowed input changed.
The final union, corrected excluded Errnos constant selectors, commands, and
source hashes are in `cwd-core-composition-proposal/final-proof-coverage.json`.
The original failed records remain available.

The supported native Make build of that public API closure passed. One offline
net8 public-wrapper probe compiled against the generated supported-Make source
and current adapter, with only two inherited nullable warnings. Eight scenarios
passed: 56 ordinary assertions plus seven actual syscall EIO cases for cwd,
relative status, mode, opened statx, open, read and close. They include detached
cwd ENOENT without a fallback, detached relative success, exact errno, consumed
close handles and legacy/live isolation. The 14 traces total 164383 bytes; the
four compiled source hashes are unchanged (`cwd-core-validation/public-native/`).
The separate native registry probe passed ten scenarios, including 33 handle
checks across Int32.MaxValue and eight EIO phases; its artifacts are in
`stream-callers/directory-native-composition-proposal/`. Native success does not
prove the adapter's Dafny contracts. An additional optional statx ENOSYS probe
initially expected Err38 and failed that expectation. The retained follow-up
trace shows libc's successful fstatat fallback and public success, which is
correct for this library-level boundary (`enosys-library-result.json`). No
adapter change or syscall-level error guarantee was introduced.

Readlink's ordered typed-context caller has completed the supported full gate:
39 selected declarations, 36 nonzero, 614 obligations and zero errors. Its
supported build passed, the unchanged GNU oracle passed 39 with one existing
skip and three deselections, and four actual repeated-read/empty-skip/output-full
checks passed. Source hashes stayed unchanged (`readlink-context-proposal/`).
Pwd's typed-context supported gate also passed all 49 selected declarations,
1517 obligations and zero errors on its recorded pinned source. Ls's final
typed-context closure is recorded below.
The final Chmod read-only retention audit confirmed all 108 original proof
headers unchanged and the original external domain unchanged. Its public entry
directly ensures `ChmodDescriptorPrincipalSpec.Spec` without a precondition.
Semantic entry analysis found no trust shortcuts in 682 utility definitions;
the exact reachable specification occupies 19 source files. The principal
always constrains actual fault receipts and effects; successful compatible
connected executions additionally satisfy the retained original mathematical
relation. This structural audit is separate from the running complete proof
gate (`chmod-final-readonly-audit/`).
Applied-core/example checks passed all ten commands and 298 obligations:
eight direct core declarations passed 217, contributor `StreamCopy` passed 17,
and the supported `example/copy` Make target passed 64. All 23 production core
source hashes stayed unchanged before and after the checks
(`final-applied-checks/results.json`). Core, Pwd and Readlink application is
complete. The final Ls closure follows below. A started process, syntax
resolution, runtime comparison,
or a utility gate using core as `--library` is not a direct proof of changed
core declarations.

## Final Chmod closure

The frozen Chmod source closure completed all 374 supported verification targets:
300 nonzero targets passed 6148 obligations with zero errors, and 74 zero-target
selections are excluded. The supported serial Make run completed 14 targets
before an intentional controlled stop; its actual exit one is preserved. The
remaining 360 targets, including the interrupted target, used the existing
`verification._verify_target` engine with four independent workers. Seed42,
isolated assertions, 30-second VC and 100-second outer limits, source/config
hashes, warning checks and result checks were unchanged. Preserved prefix TRX
receipts and all continuation reports cover the same complete target contract;
the continuation exited zero in 1651.81 seconds including setup. This is not
reported as a serial Make exit-zero result (`chmod-supported-parallel1/`).

The original runtime module also contained one pure identity-substitution lemma.
Its complete declaration is preserved byte for byte in the utility-owned
`ChmodRecursiveRuntimeProof.dfy`. An initial final-target audit found that an
unreferenced authored file does not enter the CLI's reachable verification
closure. One include in `ChmodRecursiveProof.dfy` now retains this original proof
scope. Removing only that declared include reproduces every one of the frozen
57 source/config/native hashes. The final supported contract contains exactly
the original 374 target identities plus the retained lemma. The same official
engine verified that additional target on the final production worktree:
eight obligations, zero errors, unchanged sources, exit zero in 33.59 seconds
including analysis. The complete final union is therefore 375 targets, 301
nonzero and 6156 obligations, with 74 zero-target selections excluded
(`checks/chmod-production-retained-lemma-connected-receipt.json`). No original
declaration header, proof body or executable statement changed in this include
delta. The first failed target-count audit remains available separately.

The exact utility patch `36b02304...` is applied to the failure worktree, followed
by the retained pure lemma and its include. The all-file original-declaration
audit retains 446 declarations, separately preserves the one pure lemma, and
identifies 18 replaced IO methods; no pure declaration is missing. All 108
original proof headers and 382 reviewed retained/restored mathematical spans
remain intact. The public `RunCore` directly ensures the native principal
relation without an input precondition. The existing entry-contract regression
now checks that principal and its exact 19 specification source files; its
focused integration run passed on unchanged sources.

Native validation remains separate. One supported Make build passed; its same
DLL passed all 193 fixed GNU oracle cases, with ten proof-test deselections.
All 26 bounded stream/fault comparisons and two detached-cwd cases also passed.
The six added symlink-mode EIO cases comprise five explicit nofollow `fchmodat2`
cases and one implicit recursive follow-mode case. Every injection checks the
intended operand and exact GNU stdout, stderr, exit status and mode effects.
The 72 retained traces total 181662 bytes. Native evidence, source/proof retention
tables, the include-delta review and commands are under
`stream-callers/chmod-production-proposal/` and its referenced task artifacts.

## Final applied development checks

After applying the final Chmod and frozen Ls bundles in the failure worktree,
the supported `make test-final` passed 106 serial unit tests and 15 integration
tests without skips. The actual command exited zero in 53.42 seconds. Only the
test child's soft descriptor limit was set to 2048 so the existing high-file-
descriptor test ran; the hard limit, host and tmux-server limits were unchanged.
This run precedes the final Ls ghost-proof repairs and is not relabeled as
consuming those later proof bodies. It does not establish Dafny verification.

Ruff passed for all four changed Python files. The supported
`python3 -m benchmarks validate ls chmod pwd readlink` command also passed all
four layouts, with actual exit zero in 51.56 seconds. Exact working directories,
commands, logs, elapsed times and actual child exits are retained in
`checks/task1-final-{development,ruff,layout}.{json,log}` under the artifact root
above. Final Ls proof results are recorded separately from these development
and structural checks.

## Final Ls closure

The original frozen Ls contract selected 203 declarations. Its supported Make
run completed six targets before an intentional controlled stop; Make's actual
exit two is preserved. The existing official verification engine then completed
the identical 203-target contract with those six checked TRX receipts and four
independent scheduling workers. This attempt retained 199 passing targets:
188 nonzero scopes passed 4631 obligations, and 11 zero-target selections are
excluded. Four declarations failed. Source/configuration and all five engine
hashes stayed unchanged; this attempt's actual exit one is retained rather
than reported as a successful Make gate (`ls-supported-parallel1/`).

Two private summary helpers needed constructor-before-destructor ordering and
local proof guidance. The recursive helper also lacked an exact native-call
link on failed opens. Its added private premise is already a conjunct of the
unconditional summary returned by the real recursive walk; its sole caller now
derives that fact in one local ghost assertion. Public inputs and principal
specifications remain unchanged. A third failure came from an unapplied proof
patch: Git had silently skipped its paths in a scratch directory outside the
worktree. Exact source/declaration hashes exposed that omission. The fourth
failure was an observation-rendering invariant timeout, resolved by local
hide/reveal guidance and a proof of the empty fragment relation. All original
failed records and the corrected exact patches are retained.

The actual production worktree then passed all five affected or added targets
through the unchanged official engine: flat summary four obligations, recursive
summary three, operand observation 142, rendering 102, and the added selected-
result lemma 17. All 268 obligations passed; the command exited zero and all
47 source/configuration/native records and five engine hashes stayed unchanged
(`ls-final-proof82/five/`). Seed 42, isolated assertions, 30-second per-VC and
100-second outer limits were preserved. The original recursive walk separately
passed 492 obligations in the full contract in 98.34 seconds, close to the
existing outer limit; no stronger stability claim is made.

The final modular union contains 204 target identities: the original 203 plus
the one selected-result lemma. It retains 196 passing declarations and checks
the four changed declarations, that addition and three original frame lemmas
on production, for
193 nonzero scopes and 4899 obligations with zero remaining errors. Eleven
zero-target selections are excluded. The operand method's native-generated
batch count changed from 371 to 142 after one ghost assertion and the private
callee repair. Independent exact-source and TRX audits confirm the same header,
runtime branches, calls, existing assertions, symbol filter, public entry and
verification options. The internal batching mechanism was not established;
these counts are not a measure of declaration coverage or input domain
(`stream-callers/ls-142-independent-audit.md`).

The reuse audit also compares declaration, contract, body, direct-reference and
header-dependency fingerprints. Its first literal comparison of transitive
body-visibility metadata failed. The analyzer recursively includes private
callee proof bodies: six unchanged declarations gained only the verified
selected-result lemma and its existing module alias, or the two local rendering
reveals. No prior referenced or revealed name was removed, and both opacity
flags stayed identical. The corrected audit records every actual difference
and permits only those exact reviewed additions; the other fingerprint checks
remain unchanged (`ls-final-proof82/visibility-diagnostic/`). This metadata
failure is retained separately from the successful Dafny results.

A subsequent direct-reference comparison found one inferred `CwdContext`
reference missing from `RenderFrame` metadata after the new result-module
import. Its authored declaration, contract, body and header dependencies stayed
identical. The supported engine conservatively rechecked all three original
frame lemmas from that file on the final production source: three, eleven and
seven obligations, all passing with actual exit zero in 56.29 seconds. Sources
and engine stayed unchanged (`ls-production-import-frames/`,
`checks/ls-production-import-frames.*`). These 21 obligations replace their
original records in the 196-plus-eight final union; they are not counted twice.
The completed audit confirms all 204 identities, all report hashes, source and
engine stability, and no failed or missing target in
`ls-final-proof82/union-final/completion.json`; its command exited zero.

Native validation is separate. One supported Make build's DLL passed all 266
fixed GNU oracle cases, six actual EIO comparisons and four output-failure
comparisons. A final translate-only check of production confirms identical
executable C# and adapter hashes after removing only embedded Dafny source
metadata and syntactically empty proof namespaces. The fixed GNU test body is
also identical; only Dafny verification selectors were added. This continuity
ties the final ghost-proof repairs to the tested executable without claiming a
new oracle run (`ls-final-proof82/native.log`, `ls-final-native82/`).
