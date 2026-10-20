# chmod benchmark

The public `ChmodDescriptorPrincipalSpec.Spec` relation covers numeric and symbolic
modes, ordered operands, reference-mode capture before mutation, `-c`/`-v`/`-f`,
recursive `-H`/`-L`/`-P` traversal, root preservation, ancestry cycles, and exact
filesystem, output, diagnostic, and exit effects. The public `RunCore` directly
ensures this relation for recursive and nonrecursive commands.

Native operations are bound to their actual request inputs and ordered results.
The finite observations include status ordinals, complete current-directory
contexts, authenticated targets, directory reads and cleanup results. Relative
operands use the actual current directory or an owned directory descriptor.
Detached targets retain their inode records without receiving a synthetic path.
Mode changes update the matching live object and any visible filesystem inode.
Earlier successful changes and output remain observable after a later failure.

The runtime retries an initial top-level status failure once, following GNU's
`FTS_AGAIN` handling. It attempts the actual nofollow mode operation on a symlink;
an observed `EOPNOTSUPP` is treated as not applied, while other errors retain GNU's
diagnostic and exit behavior. The source-derived dangling-symlink metadata case
recovers its observed raw target. A failed post-change status query preserves the
already changed filesystem. Directory cleanup consumes its owned handle on either
result; the exact close result is recorded and follows GNU's cleanup policy.
A first directory-read failure uses the cannot-read-directory diagnostic. A read
failure after returned entries uses the path-and-errno diagnostic and retains all
visited child effects. Error reasons are encoded as UTF-8, preserving the original
ASCII errno messages byte for byte.

The implementation prepares output and diagnostics while applying these effects,
then emits them through explicit stream-result APIs. The contract records the
committed prefix and errno of every performed write. A failed stdout write adds
GNU's write-error diagnostic to the planned stderr text. Failure of either stream
produces exit status 1. Empty output does not create an additional write request.

The original `ChmodSpec` and `ChmodRecursiveSpec` mathematical relations, mode
algorithms, and proof obligations remain utility-owned. The native relation adds
the unchanged nonrecursive batch relation and recursive visit-schedule relation
when the relevant observations succeed and connected targets agree with the
original path resolver. These compatibility conditions matter for detached
objects and descriptor-relative traversal after ancestor permission changes;
the general native relation still covers those cases. Implementation and proof
modules do not enter the specification's import closure.

Dafny verification and comparison with the pinned GNU executable are separate
validation layers. Specification fuzzing, executable certificates, and parser
witnesses are not correctness assumptions.
