# tee

`tee` copies standard input to standard output and to each named output file.
This benchmark slice supports:

- `-a` and `--append`, appending to existing regular files and creating missing outputs.
- `-i` and `--ignore-interrupts` as parsed no-op options.
- `--help` and `--version`.
- Any number of regular output path operands representable by `BenchWorld`.

Deferred GNU behavior:

- Signal handling for `-i` is outside the current `World` model.
- Signal delivery and the optional `--output-error` policies remain outside
  this slice.

The policy-free `ReadStdin()` result records a successfully read prefix and the
remaining modeled input even when reading fails. Both ordinary and append file
writes are bound to the exact `trustedFilesystem` request, including the
committed prefix and open, write, or close failure stage. Creation, truncation,
and append effects are retained on errors. Diagnostics use the C locale errno
text supplied by the native boundary.

Standard output and error writes are unbuffered. Their specifications retain
exactly the committed prefix and include write failures in the exit status;
the ordinary stdout diagnostic names `'standard output'`. A host device need
not be represented as a filesystem node to exercise a standard descriptor
write failure, for example by redirecting stdout to `/dev/full`.
