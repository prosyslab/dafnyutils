# Public-input release maintenance

Dafnyutils retains public-source manifests and release locks in
[`public-inputs/`](../public-inputs/), with data schemas in
[`benchmarks.public_inputs`](../src/benchmarks/public_inputs.py). These schemas
use only the package's declared public dependencies.

The standalone contributor workflow does not include analysis-based release
maintenance. The former analysis-dependent scripts and Make targets were removed
from this repository. No replacement integration command is installed by this
change. The format and review requirements below describe the retained release
data; contributor validation does not regenerate locks or establish their native
analysis freshness.

`public-inputs/<task>.manifest.yaml` declares a task's public release inputs.
Authored manifests use safe YAML with duplicate-key rejection; generated locks
and command reports remain JSON. Each manifest declares public roots, its fixed `RunCore` header and method-body
hole, and specification exceptions. Its obligation also identifies the existing
Core, Proof and CLI outputs whose includes must become empty modules during release
resolution. No implementation body occurs in a manifest.

The existing `IMPLEMENTATION_SUPPORT_FILES` contract supplies explicit public
support roots: the nine shared Dafny files and `IOExtern.cs`. Some specifications
rely on these delivered modules without direct includes. The native build also
needs the C# adapter. Each task also names its fixed `dfyconfig.toml` as a public-support root.
Owners must review each needed exception;
the tool never approves declarations automatically.

The owner assigns roles by these exact conventions:

- `bench/utils/*/Spec/*.dfy` holds specifications.
- Flat algorithm files whose basename ends in `Spec.dfy` or `Schema.dfy` hold specifications.
- `bench/core/*` holds public support, including the native adapter.
- Each task root's exact `dfyconfig.toml` is fixed public support.
- Other task Dafny files are candidate outputs. Only the exact declared hole file
  receives the policy's public-support exception.
- Other paths are private and cannot enter a lock.

The lock generator follows native include edges from public roots and every
noncandidate include of the fixed hole scaffold. It ignores only the manifest's
explicit Core, Proof and CLI outputs. It rejects all other candidate/private dependencies.
It follows literal project includes through the existing TOML format. It rejects
unsupported globs, unknown project options and undeclared candidate inputs.
It hashes raw UTF-8 file bytes with SHA-256. For the hole file only, it excludes
the native method body's byte span. It verifies the fixed header against the
manifest before it writes a lock. It also binds the exact manifest bytes, native
Dafny version and installed `dafny-analysis` distribution version. It does not
hash an installed toolchain tree. These version labels are producer provenance,
not a hermetic toolchain or a claim of grading-time enforcement.

## Analysis requirements for release producers

Producing a new lock requires native include and declaration facts, exact method
body spans, declaration reachability, trust-construct checks and reviewed
specification exceptions. A release producer must validate the declared roles
and fixed hole signature, resolve the public scaffold without candidate bodies,
and bind the source bytes, manifest and producer identities to the lock.

A successful compiler parse is resolution evidence; it is not Dafny verification.
Missing or invalid locks remain release blockers. The independent contributor
checker checks authoring metadata, builds, executable behavior, fuzzing and native
project proofs; it does not claim these analysis-based release guarantees.

## Release requirements

Manifests alone do not establish a valid release. The fixed support at task-local
`Impl/CliSupport.dfy` (or flat algorithm `CliSupport.dfy`) occupies a candidate
path. Including it in a hole scaffold or public specification blocks release.
Additional candidate dependencies can
also block a release; Chmod specifications reach `Impl/ChmodDescriptorCore.dfy`.
Strict lock generation rejects candidate-path support. Move or split this
support into public-support paths before generating a release lock. Missing or
invalid locks block release.

Specification files also contain executable schema methods and functions that
need reviewed exceptions or source separation. Some declarations need explicit
permission for publication outside the obligation's dependency closure. Empty
exception lists do not authorize these declarations. A reviewer must decide whether
any proposed public helper reveals a task solution; mechanical lint cannot make
that decision.
