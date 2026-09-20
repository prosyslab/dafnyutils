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

The current benchmark implements a deliberately small symbolic-link slice:

- `ln -s SOURCE LINK_NAME`
- `ln --symbolic SOURCE LINK_NAME`
- `--help` and `--version`
- parse diagnostics for unknown options
- missing operand diagnostics for the supported two-operand form
- one-target implicit link-name mode, multi-source target-directory mode, and
  two-operand directory destinations: reject with a benchmark diagnostic
- existing destination failures through the shared `CreateSymlink(path, target)` IO model

The formal spec models symbolic-link creation as a `World` transition using
`IOContract.CreateSymlinkContract`. The symbolic link stores the raw `SOURCE`
string as its target.
