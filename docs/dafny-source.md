# Bundled Dafny source

`dafny/` is an ordinary source directory tracked by this repository. Cloning
Dafnyutils includes the complete tracked source snapshot; access to the former
private Dafny repository is not required. Build outputs and local caches are not
included. `coreutils/` remains a separate submodule.

## Provenance

- Source repository: `https://github.com/prosyslab/dafny.git`
- Source branch: `expecto`
- Imported commit: `1eb9fc5fa2661483de151ff85b21eed0b695878a`
- Imported files: all 6,356 tracked files, with their original content and modes.
- Upstream project: <https://github.com/dafny-lang/dafny>
- License: [Dafny LICENSE.txt](../dafny/LICENSE.txt); existing notices remain in the source tree.

The import preserves the source snapshot, not the former repository's Git history.
Subsequent Dafny changes are maintained directly in this repository. This fork
provides analysis commands used by Dafnyutils; do not replace it with an arbitrary
upstream binary.

## Build

Use the [contributor development container](adding-utilities.md#install-the-tools)
for the configured toolchain, or install the prerequisites described in
[Dafny's installation guide](../dafny/docs/Installation.md).
From the Dafnyutils repository root, run:

```sh
make build-dafny
```

This builds the bundled solution with .NET 8 and writes the executable to
`dafny/Binaries/Dafny`. Expect several minutes; a first NuGet restore depends on
network speed. Successful output ends with a build summary and zero errors.
No private Dafny clone is performed. Package restoration can still require network access.

The contributor container and CI expose this executable as `dafny-benchmark`.
For a host installation, set `DAFNY_BENCHMARK` to the absolute path of
`dafny/Binaries/Dafny` when running Dafnyutils.
