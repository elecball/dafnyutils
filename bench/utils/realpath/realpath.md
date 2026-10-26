# GNU realpath

This benchmark implements GNU `realpath` default physical traversal, `-P`,
logical traversal `-L`, and lexical strip mode `-s` / `--strip` /
`--no-symlinks`. The three existence policies are default/all-but-last `-E`,
existing-only `-e`, and missing-permitted `-m`. The pinned source is
`coreutils/src/realpath.c`, `coreutils/lib/canonicalize.c`, `file-set.c` and
`hashcode-named-file.c` at `2cf491412c199e2211880ec3f4ba387026638a33`,
GPL-3.0-or-later. Upstream scenarios include `tests/misc/realpath.sh`.

## Accepted inputs and observations

All GNU option forms, permutation, short clusters, unambiguous long prefixes,
`--`, option overrides, multiple paths and empty operands are included.
`-q` suppresses operand diagnostics, `-z` uses NUL output delimiters, and
`--relative-to` / `--relative-base` use whole-component prefix rules.
Help, version, malformed options, missing arguments and GNU early informational
exits determine exact output bytes and exit status. Relative-directory
preparation occurs before operands and its failures remain diagnostic with `-q`.
Operands continue after ordinary failures; a fatal allocation failure aborts
preparation or the remaining operand sequence while preserving earlier output.

Physical traversal expands symbolic links as encountered, including before
`..`. Logical traversal first performs strip canonicalization and then physical
canonicalization, following GNU's two-pass rule. Strip mode retains link
spellings. Native lookups retain their existing per-system-call forty-link
limit; the utility's own traversal has no forty-link cap. After twenty link
expansions, GNU records the pair of parent-directory device/inode identity and
the entire raw remaining spelling. A repeated key reports ELOOP for `-E`/`-e`;
`-m` retains that component and continues. Different suffixes are different keys,
and directory aliases share their native identity. Missing paths, nondirectory
prefixes, trailing separators and dot components follow GNU's existence policy.

The environment is a stable finite local64-bit Linux tree, C locale and UTC0.
Files, directories, symbolic/hard links, permission-denied paths, dangling links
and cycles are included. Namespace mutation, forced early memory exhaustion,
ACLs, labels, alternate mount roots and injected asynchronous faults remain
outside the existing environment. Stream failures, including `/dev/full`, and
modeled partial writes remain covered. Filesystem access is read-only.

## Mathematical specification and total proof

The specification gives inductive denotations of directory-anchored path syntax,
with exact spelling, parent-directory and native-observation premises. Physical
link rules bind each `ReadLink` result and each ordinal-sensitive parent
`GetFileStatus` result. Component-prefix maxima determine relative output;
partitions determine operand order, exact bytes and status-observation ordinals.
The specification imports no Core, Proof or CLI implementation.

Every newly recorded cycle key retains one native `F_triple` until `hash_free`.
On the pinned ABI its size is24 bytes and nonnull native addressable storage is
bounded by `SIZE_MAX=18446744073709551615`. Consequently no execution can retain
more than768614336404564650 distinct records. The implementation makes the
unavoidable native representability failure explicit only when a novel record
would exceed this source-derived bound, after GNU's parent lookup and duplicate
check. This is a conservative physical upper bound, not a traversal budget or a
prediction of the earlier allocation failure on a real host. It reports GNU's
fatal `realpath: memory exhausted` outcome, distinct from an operand errno.
No early allocation success/failure timing is claimed outside the enough-memory
boundary, and no arbitrary link cap or input-length restriction is imposed.

Utility-local finite-cardinality and structural measures establish termination,
including repeated keys under `-m` and indefinitely growing link spellings.
All path construction, link traversal, relative output, diagnostics and exit
selection are implemented and proved locally. `Realpath.RunCore` directly
ensures `RealpathSpec.Spec`. Existing cwd, readlink, metadata, stream, C-locale
errno, UTF-8 and quoting contracts form the native boundary; no new trusted
primitive or assumption is added. The fixed CLI protocol and process runner
retain their existing boundary. No GNU realpath option is excluded for missing
IO support.
