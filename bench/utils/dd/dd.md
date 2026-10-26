# dd stream benchmark

This contributor-maintenance implementation targets GNU coreutils `dd` at
`2cf491412c199e2211880ec3f4ba387026638a33`, `coreutils/src/dd.c`, licensed
GPL-3.0-or-later. It is based on Dafnyutils `37b35bac3d4cf84cdd8ea02eb3279e8aa49307df`.

The implementation covers finite captured standard input to standard output,
explicit `status=none`, `iflag=fullblock`, `bs=N`, plain copying, and the valid
combinations of `conv=lcase`, `conv=ucase`, and `conv=swab`. It also supports
`ibs=N`, `obs=N`, `count=N`, `iflag=count_bytes`, GNU multiplicative size/count
suffixes and `conv=sync`. `cbs=N` is validated; conversions that use it remain
outside scope. The GNU `INTMAX_MAX` count sentinel means unlimited copying. GNU's `bs` overrides both `ibs` and `obs` regardless of their order.
Repeated conversion and input-flag operands accumulate; repeated sizes/counts
use their last value. A missing conversion block size makes `conv=block` and
`conv=unblock` ineffective in GNU, but record conversion is not in this initial
scope. Informational requests and malformed forms of supported operands retain
GNU's exact diagnostics and exit statuses. Fixed text lives in `DdSpec.dfy`.

Inputs use Linux x86-64, the C locale, UTC0, stable finite captured bytes,
managed-representable sequences and sufficient memory. Case conversion changes ASCII letters only and preserves every other
byte. `swab` exchanges global adjacent pairs, carrying an odd byte across input
reads and leaving a final unpaired byte unchanged (`swab_buffer`, lines 1737ff).
`sync` pads each positive short input record to the configured input block size
with NULs before translation. `fullblock` accumulates successful short reads
locally; a read error discards that incomplete input record as GNU does.

The observable contract covers exact output/error bytes and status, the consumed
input prefix, partial output on write failure, the read error, and the point at
which further input stops being consumed. The specification uses byte-index
relations and mathematical input/output partitions; Core owns the block loops,
case conversion, pair swapping, padding and record counts. The entry `RunCore`
directly ensures `DdSpec.Spec`.

The existing whole-input API cannot express bounded input consumption or input
records. The sole new trusted primitive is `ReadStdinChunk(limit)`, one
noninterrupted bounded native read with the exact observed prefix, remaining
input and errno. Its generic adapter retries interrupted (`EINTR`) calls,
matching GNU `iread`; it performs no block accumulation. The contract allows
short reads, does not pad/convert/count blocks, and supplies no dd-specific
conclusion. `ReadBlock` and every derived operation are local verified code.
Existing stream operations/contracts remain intact. Stream writes,
errno text and C-locale argument quoting use the existing `bench/core` boundary.
Native libc/kernel and C# adapter correctness are trusted separately from the
Dafny proof.

File operands and descriptor flags are excluded: dd opens/truncates output before
copying, retains descriptors across reads, and can seek them. Whole-file
`ReadFile`/`WriteFile` calls cannot express that failure ordering. Also excluded
are `skip`/`seek` and aliases, record/character-set conversions, sparse output,
`noerror`, physical synchronization and descriptor cache/permission flags. They
need additional operations or independent transformation/proof work; supported
conversion flags are not silently treated as successful no-ops. Valid GNU
operands outside scope produce the explicitly labeled benchmark-scope diagnostic;
that diagnostic does not claim GNU parity for the excluded invocation.

The default transfer statistics and `status=progress` use elapsed/high-resolution
clock values absent from IO.dfy; runtime copying here therefore requires explicit
`status=none`. `status=noxfer` is outside the initial scope pending exact record
count reporting. Help/version and parse errors do not require `status=none`.
Interactive/infinite/device input, injected asynchronous/late failures, concurrent
changes, forced resource exhaustion and signal-driven statistics are excluded
under the repository stream environment rules. `/dev/full` output is covered.

GNU evidence comes from `tests/dd/conv-case.sh`, `misc.sh`, `reblock.sh`,
`bytes.sh`, and the `dd.c` parsing/copying routines. Fixed runtime tests adapt
individual upstream stream scenarios; generated campaigns use both valid inputs
and malformed supported operands. Mandatory validation is the supported local
build/test/verify targets, `make check TASK=dd`, and full-comparison seeds
`1,7,19` with 1,000 matches each. These are requirements, not completed results.

Contributor validation results and retained failure evidence are recorded
separately in `maintenance.md`, outside the public task resources. Generated
logs and mismatch bundles remain in
`/workspace/tmp/coreutils-four-20261022/evidence/dd/`.
