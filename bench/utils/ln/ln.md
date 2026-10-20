# ln NL Specification

Source:
- `coreutils/doc/coreutils.texi`
- `@node ln invocation`
- Source line range: 10530-10755

This file summarizes the upstream GNU `ln` behavior relevant to the benchmark.

## `ln`: Make links between files

`ln` makes links between files. By default it makes hard links; with
`-s` or `--symbolic`, it makes symbolic links.

```text
ln [option]... [-T] target linkname
ln [option]... target
ln [option]... target... directory
ln [option]... -t directory target...
```

When two file names are given, `ln` creates a link to the first name from
the second name. When one target is given, GNU `ln` creates a link to that
target in the current directory. With `--target-directory` or a directory
as the final operand, it creates links for each target inside that directory.

Normally `ln` does not replace existing files. GNU options such as
`--force`, `--interactive`, and `--backup` control replacement or backup
behavior.

Hard links are additional names for an existing file and are constrained by
filesystem rules. Symbolic links are separate filesystem entries containing
the target path string; the target may be relative, absolute, or dangling.

Relevant options include:

- `-s`, `--symbolic`: make symbolic links instead of hard links.
- `-f`, `--force`: remove existing destination files.
- `-i`, `--interactive`: prompt before removing an existing destination.
- `-L`, `--logical`: for hard links, dereference a symbolic source.
- `-P`, `--physical`: for hard links, link the symbolic source itself.
- `-n`, `--no-dereference`: treat a symlink-to-directory destination as a file.
- `-r`, `--relative`: make symbolic links relative to the link location.
- `-t`, `--target-directory=directory`: place links in the given directory.
- `-T`, `--no-target-directory`: always treat the destination as a normal file.
- `-v`, `--verbose`: print each linked file after success.
- `-b`, `--backup`, `-S`, `--suffix`: control backup files.

### Benchmark-Supported Behavior

The current benchmark supports hard links and symbolic links:

- `ln -s SOURCE LINK_NAME`
- `ln --symbolic SOURCE LINK_NAME`
- `ln SOURCE LINK_NAME`
- one-source implicit link-name mode and two-operand directory destinations
- multiple sources with a final target-directory operand
- `--help` and `--version`
- parse diagnostics for unknown options
- missing operand and target-directory diagnostics
- existing destination and host failures through the shared creation models

The symbolic link stores the raw `SOURCE` string as its target. Hard-link
creation uses the exact filesystem request and preserves inode identity.
Directory classification and source status are bound to their ordered native
observations, so a host metadata error on an existing path remains an explicit
error. A failed destination-directory probe in the two-operand form falls
through to the link-name interpretation, matching the existing command flow;
the multi-source form diagnoses the failed target probe.

The final specification records the number of metadata requests and the actual
creation outcome. Diagnostics use C locale errno text. Standard descriptor
writes retain their committed prefixes, and a failed stdout or stderr write
makes the command fail.
