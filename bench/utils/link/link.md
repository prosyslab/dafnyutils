# link NL Specification

Source:
- `coreutils/doc/coreutils.texi`
- `@node link invocation`
- Source line range: 10491-10528
- Implementation: `coreutils/src/link.c` at submodule commit
  `2cf491412c199e2211880ec3f4ba387026638a33`
- License: GPL-3.0-or-later

This file summarizes the upstream GNU `link` behavior relevant to the benchmark.

## `link`: Make a hard link

`link` creates one hard link by calling the system's `link` operation. It is a
smaller interface than `ln`: it accepts exactly one existing source name and
one new link name, without replacement, target-directory, or interactive
options.

```text
link filename linkname
```

`filename` must name an existing filesystem object, and `linkname` must not
already exist. The directory containing `linkname` must exist. On success, the
two names refer to the same filesystem object, so changes made through either
name are visible through the other.

If `filename` is a symbolic link, GNU documents whether the new hard link
refers to the symbolic link itself or to its target as unspecified. Use `ln -P`
or `ln -L` when that distinction must be selected explicitly.

The command accepts `--help` and `--version`. To use an operand beginning with
`-`, place it after `--` or prefix it with a pathname component such as `./`.

### Benchmark-Supported Behavior

The benchmark handles exactly two pathnames, plus `--help`, `--version`, `--`,
GNU long-option abbreviations, and operand, option, and hard-link creation
errors. Zero operands, one operand, and more than two operands produce distinct
GNU-compatible diagnostics without changing the modeled filesystem.

For ordinary execution, the first pathname is the existing source and the
second is the new target name. The filesystem effect is represented by the
shared `CreateHardLink` operation. Successful creation makes the target an
alias of the source and produces no output. Failures quote the target and
source in GNU's `cannot create link TARGET to SOURCE` diagnostic.

No GNU `link` options are excluded due to missing `IO.dfy` support. A symbolic
link used as the source is not assigned behavior beyond the platform result,
because GNU documents whether `link` follows it as unspecified.

### Scope and model

- **Input and environment:** Finite arguments, GNU long-option handling, Linux
  filesystem, current user permissions, and C-locale diagnostics; stdin is
  unused.
- **Observation:** Output streams, exit status, and modeled filesystem. Help,
  version, parsing, and operand-count errors leave the filesystem unchanged.
  Successful creation adds `linkname` as an alias of `filename`. A failed
  `CreateHardLinkSpec` uses the trusted filesystem observation and does not by
  itself guarantee filesystem preservation; maintainer review is pending.
- **Trusted API:** Shared parser, `CreateHardLinkSpec`, errno text,
  argument/path quoting, and stream append contracts in `bench/core` revision
  `3699f93aa58aadf89ae69d822312371a98eeca2c`.
- **Proof:** `Link.RunCore` ensures `LinkSpec.Spec` through `LinkProof`.
  `Decode` and `LinkCore.RunCore` terminate; whole-process termination is not
  proved because the shared CLI entry uses `decreases *`.

### Validation evidence

The implementation was checked against GNU coreutils built from the pinned
submodule revision. Differential cases cover missing and extra operands,
argument and path quoting, successful hard-link identity, missing sources,
existing targets, missing target parents, option parsing and precedence, and
pathnames beginning with `-`.

- `python3 -m benchmarks validate link`: `link: valid`.
- `make test TASK=link`: 28 runtime parity cases passed; 3 proof cases were
  deselected by the runtime target.
- `python3 -m pytest -q -n0 --import-mode=importlib -m dafny_verify
  bench/utils/link/Tests.py`: 3 proof cases passed; 28 runtime cases were
  deselected.
- `python3 tools/coreutils_fuzzer/run.py fuzz link --seeds 1,7,19
  --iterations 1000`: each seed completed 1,000 matches with zero mismatches,
  timeouts, incomplete iterations, or other errors.
- `make check TASK=link`: runtime tests, the 20-case automatic fuzz gate,
  Dafny verification, proof tests, and definition checks passed.

The first runtime test run exposed an older help-text layout copied from GNU
coreutils 9.4. The fixed text was updated to the pinned `9.10.13-2cf49` output,
after which all runtime cases passed. These automated results do not replace
the required human specification review.

### Exit Status

The supported command exits with status 0 after successful hard-link creation
or a help or version request. Operand, option, and link-creation errors exit
with status 1.
