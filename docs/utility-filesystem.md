# Filesystem utility implementations and proofs

This chapter of the [utility guide](utility-guide.md) explains the filesystem
utilities. The linked symbols identify the implementation and the principal
relations to read alongside it; the guide explains their shared IO trust boundary.

## chmod

### Implementation

The active entrypoint uses
[ChmodDescriptorCore.Prepare](../bench/utils/chmod/Impl/ChmodDescriptorCore.dfy#L63).
It resolves an octal or symbolic mode against the process umask, or reads a
reference file's mode, and checks the root identity when preservation is requested.
[ChmodDescriptorRuntime.Visit](../bench/utils/chmod/Impl/ChmodDescriptorRuntime.dfy#L87)
reads an operand's identity, applies its mode change, and then visits eligible
directory children. Children are addressed relative to their open directory
handle. Separate policies control following a symlink for metadata, changing its
referent, and descending through it. Active inode identities prevent cyclic
descent. Operands and directory observations retain their order, and errors are
accumulated while later work continues.

### Proof idea

[ChmodDescriptorSpec.VisitFields](../bench/utils/chmod/Spec/ChmodDescriptorSpec.dfy#L183)
relates each visit to its status observations, requested mode, mode-setting
contract, child visits, intermediate states, and diagnostic fragments.
[FilesFields](../bench/utils/chmod/Spec/ChmodDescriptorSpec.dfy#L264) joins these judgments
in operand order. The runtime maintains directory anchors and proves that mode
changes preserve filesystem topology and existing directory identities. Mode
relations define affected permission bits, umask handling when `who` is omitted,
and conditional/copy permissions from the existing mode and file kind. Their
parsing and bit operations are connected to these mathematical relations by
[ChmodProof.BridgePlannedMode](../bench/utils/chmod/Proof/ChmodProof.dfy#L476).
The principal contract is
[ChmodDescriptorPrincipalSpec.Spec](../bench/utils/chmod/Spec/ChmodDescriptorPrincipalSpec.dfy#L165).
Its additional [NormalOutcomeFields](../bench/utils/chmod/Spec/ChmodDescriptorPrincipalSpec.dfy#L113)
bridge to the older path-based batch or recursive relation is conditional on
successful observations and compatible descriptor/path resolution. The prepared
behavior is guarded by `SpecExternalDomain`, which requires valid external text.

## cp

### Implementation

[CpCore.Discover](../bench/utils/cp/Impl/CpCore.dfy#L303) builds a source tree from
metadata and directory observations, checking recursion, ancestor identities,
symlink policy, and filesystem boundaries. Copying then distinguishes data,
links, and directories. Directories are prepared before their children and receive
final attributes afterward. [CopyOperand](../bench/utils/cp/Impl/CpCore.dfy#L2058)
combines parent preparation, duplicate and destination guards, copying, and parent
attribute restoration. [CopyBatch](../bench/utils/cp/Impl/CpCore.dfy#L2115) carries
hard-link and previous-destination information between operands. Data copying
retains read and write failure stages, including committed bytes; force and backup
policies may perform additional filesystem operations after an initial failure.

### Proof idea

[CpSpec.SourceTreeFields](../bench/utils/cp/Spec/CpSpec.dfy#L1337) characterizes the
observed source hierarchy, including omitted, cyclic, and failed sources.
[CopyTree](../bench/utils/cp/Spec/CpSpec.dfy#L1425) and
[ChildrenFields](../bench/utils/cp/Spec/CpSpec.dfy#L1570) relate recursive effects through
intermediate filesystems and ordered output fragments. They preserve partial
progress and permit a child sequence to stop when self-copy is detected.
[BatchOutcome](../bench/utils/cp/Spec/CpSpec.dfy#L1767) requires one operand relation per
source, connected filesystem and link-map states, and success exactly when every
operand succeeds. Most proof work lives in the Core methods' contracts and loop
invariants. [RunCore](../bench/utils/cp/Impl/CpCore.dfy#L2318) directly assembles the
command relation and stream publication into `Spec`; the separate
[CpProof.CoreSummaryImpliesSpec](../bench/utils/cp/Proof/CpProof.dfy#L10) merely exposes
that already-established result. Failed copies do not imply rollback.

## du

### Implementation

[DuCore.Prepare](../bench/utils/du/Impl/DuCore.dfy#L101) reads each operand in order and
prints its returned byte length and pathname, or appends its read diagnostic.
It continues after failed operands and remembers whether any failed. This
implementation covers apparent byte counts of readable file operands with the
byte-count options selected;
unsupported accounting requests produce an explicit error. It does not implement
a general recursive disk-allocation traversal.

### Proof idea

[DuSpec.RunRelation](../bench/utils/du/Spec/DuSpec.dfy#L191) requires an observation for
every operand, a corresponding count or error fragment, and partitions proving
that the fragments concatenate in operand order. Successful count fragments use
`|data|`; the normal exit is nonzero exactly when some observation is an error.
The implementation's prefix accumulators are converted into these finite witnesses
by [DuProof.BuildRunWitness](../bench/utils/du/Proof/DuProof.dfy#L144) and
[RunWitnessRefines](../bench/utils/du/Proof/DuProof.dfy#L237). The final bridge combines
that relation with the trusted stream-write outcomes, including partial emission.

## link

### Implementation

[LinkCore.Prepare](../bench/utils/link/Impl/LinkCore.dfy#L78) handles information and
operand errors, then makes one `CreateHardLink` call from the first pathname to
the second. Success has no normal output. Failure formats the source, target, and
native error into the prescribed diagnostic. `Flush` publishes the planned text
and turns a stream error into failure as well.

### Proof idea

[LinkSpec.LinkResult](../bench/utils/link/Spec/LinkSpec.dfy#L156) relates the initial and
final filesystems by `CreateHardLinkSpec`. The utility proof therefore establishes
that the correct operands reach the trusted hard-link operation and that its
result selects the required diagnostic and exit status.
[LinkProof.PreparedSummaryImpliesPreparedSpec](../bench/utils/link/Proof/LinkProof.dfy#L13)
connects preparation to the declarative cases; its final bridge combines that fact
with the emission relation. The filesystem operation's inode and link-count
effects come from its IO contract.

## ln

### Implementation

[LnCore.Prepare](../bench/utils/ln/Impl/LnCore.dfy#L424) chooses a link destination:
the source basename in the current directory for one operand, a direct or
directory-relative destination for two, and a target directory for a batch.
Symbolic links store the source text. Hard links first inspect the source without
following its final symlink and reject directories before creation.
[RunBatch](../bench/utils/ln/Impl/LnCore.dfy#L280) attempts each source in order and
accumulates diagnostics and success. The option schema exposes the symbolic-link
switch and information requests.

### Proof idea

[LnSpec.LinkStepRelation](../bench/utils/ln/Spec/LnSpec.dfy#L342) separates symbolic
creation from source inspection and hard-link creation.
[LinkBatchRelation](../bench/utils/ln/Spec/LnSpec.dfy#L382) requires connected filesystem
states, the basename-derived destination for each source, ordered diagnostic
pieces, and conjunction of step successes. Status observations also advance at
the required ordinals, so repeated operands are tied to the right native query.
[LnProof.BatchStepTraceImpliesSpec](../bench/utils/ln/Proof/LnProof.dfy#L82) translates
the implementation's step witnesses into this relation. Earlier successful links
remain part of the final state when a later source fails.

## ls

### Implementation

[LsCore.Prepare](../bench/utils/ls/Impl/LsCore.dfy#L3064) resolves formatting parameters
from options, environment, and the current time, then observes each operand.
Directory collection filters entries, obtains metadata when the requested display
or ordering needs it, and renders names or aligned metadata fields. Sorting
orders the observations before output groups and directory headings are assembled.
[WalkDirectoryRecursive](../bench/utils/ls/Impl/LsCore.dfy#L2567) lists a directory and
its eligible descendants, using opened-directory identities to detect ancestor
cycles. Native calls are wrapped by
[LsNativeCore](../bench/utils/ls/Impl/LsNativeCore.dfy), retaining their status ordinals
and directory-capability context.

### Proof idea

[LsSpec.EntrySortingRelation](../bench/utils/ls/Spec/LsSpec.dfy#L1363) requires both a
permutation and the requested pairwise ordering; the sorting proof establishes
both properties. [DirectoryListingRelation](../bench/utils/ls/Spec/LsSpec.dfy#L1618)
connects the observed entry set, sorted records, rendered fragments, totals, and
read/close diagnostics. [RunRelation](../bench/utils/ls/Spec/LsSpec.dfy#L2131) joins
operand observations, status intervals, sorted output groups, diagnostic order,
and the operand-based exit classification. Recursive witnesses provide the same
connection for descendants and cycles. Separately,
[LsNativeSpec.TraceFields](../bench/utils/ls/Spec/LsNativeSpec.dfy#L62) requires every
native call to satisfy its contract and adjacent context states to connect;
[LsRunNativeProof.RunWitness](../bench/utils/ls/Proof/LsRunNativeProof.dfy#L9) incorporates
that trace into the run relation. This proves orchestration and rendering relative
to observed native results, including incomplete directory reads.

## mkdir

### Implementation

[MkdirCore.RunCore](../bench/utils/mkdir/Impl/MkdirCore.dfy#L59) calls `CreateDirectory`
once per operand, in order, requesting mode `0777`; the IO contract applies the
umask. It collects a verbose announcement only for successful creations and an
error for failed creations, continues through the operands, and finally publishes
the collected streams.

### Proof idea

[MkdirSpec.CreationResults](../bench/utils/mkdir/Spec/MkdirSpec.dfy#L234) requires a
sequence of filesystems connected by the directory-creation contract.
[OrderedPieces](../bench/utils/mkdir/Spec/MkdirSpec.dfy#L218) partitions stdout and
stderr into exactly the pieces belonging to those results.
[MkdirProof.ExtendCreations](../bench/utils/mkdir/Proof/MkdirProof.dfy#L10) and
`ExtendPieces` preserve these properties as the loop appends an operand.
`AssembleRun` packages the witnesses and `Complete` combines them with stream
outcomes. The normal creation result succeeds only if every creation succeeded;
a later failure preserves earlier created directories.

## mkfifo

### Implementation

[`DecideMode`](../bench/utils/mkfifo/Impl/MkfifoCore.dfy) resolves the optional octal
or symbolic MODE before processing any operand.
[`ParseMode` and `ComputeMeaning`](../bench/utils/mkfifo/Impl/MkfifoModeCore.dfy)
use loops to parse and evaluate the expression. Symbolic modes start from `0666`;
octal modes specify the result directly.
`RunOperands` creates each FIFO in order. With `-m`, it sets permissions after
successful creation; otherwise the creation contract applies the process umask.
It continues after operand failures and retains earlier effects, including a
FIFO whose permission change fails. Security-context options remain outside
the [documented scope](../bench/utils/mkfifo/mkfifo.md).

### Proof idea

[`ModeDenotes`](../bench/utils/mkfifo/Spec/MkfifoSpec.dfy) describes valid MODE
strings through abstract expressions, their `Render` text, and their `Meaning`.
[`ParseModeOfRender` and `ParseModeRenders`](../bench/utils/mkfifo/Proof/MkfifoModeProof.dfy)
connect the parser to that relation in both directions. `OperandResults` and
`OrderedDiagnostics` require connected filesystem states and diagnostic pieces
for every operand. [`ExtendLoop`, `AssembleRun`, and `Complete`](../bench/utils/mkfifo/Proof/MkfifoProof.dfy)
combine those witnesses with native creation, permission, and stream contracts
to establish the final [`RunCore`](../bench/utils/mkfifo/Impl/Mkfifo.dfy) obligation.

## mv

### Implementation

[MvCore.MoveOne](../bench/utils/mv/Impl/MvCore.dfy#L4050) observes source and destination
metadata, applies overwrite/update policy, checks same-file identities, and
selects a backup when required. The final move is rename-based:
[ExecuteRenameFrame](../bench/utils/mv/Impl/MvCore.dfy#L3471) optionally renames the
existing target to its backup before renaming the source. A batch carries the
resulting filesystem forward to each subsequent source. Verbose/debug output and
errors are collected separately from their final stream writes.

### Proof idea

[MvSpec.RenameEffectRelation](../bench/utils/mv/Spec/MvSpec.dfy#L1151) describes the
allowed direct and backup rename outcomes, including the intermediate backup
filesystem. A backup rename may succeed before the source rename fails; the
relation retains that partial effect.
[BatchMoveWitnessRelation](../bench/utils/mv/Spec/MvSpec.dfy#L1439) connects every source
to successive filesystem bounds and ordered output fragments.
The principal [Spec](../bench/utils/mv/Spec/MvSpec.dfy#L2026) requires both the
mathematical candidate behavior and an observation-sensitive account of status
calls. [MvProof.CoreSummaryImpliesSpec](../bench/utils/mv/Proof/MvProof.dfy#L2746) uses
the runtime's separate status evidence to establish the latter as well as the
candidate relation, then incorporates stream outcomes. This evidence distinguishes
native metadata failures and skipped moves from successful renames.

## rm

### Implementation

[RmCore.RemoveDirectory](../bench/utils/rm/Impl/RmCore.dfy#L277) checks directory,
dot/root, device, and cycle restrictions before recursive work. Files use unlink;
recursive directories are enumerated, their children are processed in the
observed order, and the directory is removed afterward when child processing and
traversal permit it. [ProcessHierarchy](../bench/utils/rm/Impl/RmCore.dfy#L380) keeps
child effects after failure and suppresses the final parent removal when children
failed or the listing ended with an error. Later top-level operands still run.
Force policy affects which native failures count as errors, while verbose output
records successful removals.

### Proof idea

[RmSpec.RemoveJudgment](../bench/utils/rm/Spec/RmSpec.dfy#L625) is an inductive judgment
with atomic, refused, and hierarchical cases. The hierarchical case requires the
actual observed listing and a partition into consecutive child filesystem and
output states; it specifies exactly when the parent may be removed.
[RmProof.HierarchyJudgment](../bench/utils/rm/Proof/RmProof.dfy#L247) constructs this case
from recursive child contracts and the final operation. Termination uses a finite
universe of inode identities minus the active ancestor set, with removal lemmas
showing that no new identities are introduced.
[OperandsJudgment](../bench/utils/rm/Spec/RmSpec.dfy#L676) joins normalized operands in
order and makes any unignored failure determine the normal exit status.

## rmdir

### Implementation

[RmdirCore.RemoveOperand](../bench/utils/rmdir/Impl/RmdirCore.dfy#L174) attempts a
directory, then walks upward through its parents when requested and when the
previous removal succeeded. It stops the chain at a failure or at a path without
a parent, and continues with later operands. The ignore-nonempty policy recognizes
known nonempty errors and probes the directory for selected ambiguous errors.
Verbose output reports attempted removals, including failed attempts.

### Proof idea

[RmdirSpec.RemovalRelation](../bench/utils/rmdir/Spec/RmdirSpec.dfy#L293) connects one
attempt to the trusted removal operation, ignored-failure decision, and diagnostic
pathname. [ChainWitness](../bench/utils/rmdir/Spec/RmdirSpec.dfy#L328) requires adjacent
parent paths and filesystem states, permits continuation only after a successful
removal, specifies the stopping condition, and partitions output in attempt order.
[RmdirProof.AppendChain](../bench/utils/rmdir/Proof/RmdirProof.dfy#L163) maintains these
facts; the batch proof joins complete chains in operand order. Nonempty probes
are justified by open/read/close contracts and restore the legacy handle map.
An ignored failure is accepted for the exit result but still stops parent removal.

## stat

### Implementation

[StatCore.Prepare](../bench/utils/stat/Impl/StatCore.dfy#L297) scans the requested
format once to obtain literal/directive boundaries, then requests one status per
operand with the chosen symlink-following policy. It substitutes the supported
metadata directives using that template and appends a newline for each successful
operand. Failed status requests append diagnostics instead. The loop continues
through all operands before publishing its streams.

### Proof idea

[StatSpec.FormatRenderingRelation](../bench/utils/stat/Spec/StatSpec.dfy#L338) requires
a partition of the format into literal or directive pieces, with each directive
related to its status field by `DirectiveTextSpec`.
[RunFilesRelation](../bench/utils/stat/Spec/StatSpec.dfy#L405) assigns each operand its
observed status at the corresponding ordinal and concatenates its output/error
fragment in order. The error flag means that at least one status request failed.
[StatProof.RunFilesSummaryImpliesRelation](../bench/utils/stat/Proof/StatProof.dfy#L524)
converts the implementation's accumulated prefix summary to the finite fragment
relation. The final preparation and emission bridges connect metadata rendering
to the externally visible output and exit, accounting for stream failures too.

## touch

### Implementation

[TouchCore.Prepare](../bench/utils/touch/Impl/TouchCore.dfy#L567) resolves which times
to change and whether their source is now, an explicit timestamp/date, or a
reference file. Date interpretation is delegated to the trusted parser.
[RunOne](../bench/utils/touch/Impl/TouchCore.dfy#L955) treats `-` as the stdout timestamp
target; other operands are checked, updated, or created according to the
no-create and symlink policies. Selecting only one fixed timestamp preserves the
other timestamp through an observation and a suitable update. Each operand's
error is accumulated while later operands continue.

### Proof idea

[TouchSpec.RunStepSpecFields](../bench/utils/touch/Spec/TouchSpec.dfy#L400) distinguishes
stdout timestamps, existing paths, ignored missing paths, and create-then-update
outcomes. Creation remains observable even if the later timestamp update fails.
[RunFilesSpecFields](../bench/utils/touch/Spec/TouchSpec.dfy#L508) requires consecutive
states containing the filesystem, stdout timestamp target, accumulated errors,
and failure flag. [TouchProof.ExtendFileStates](../bench/utils/touch/Proof/TouchProof.dfy#L234)
connects implementation steps to these witnesses, while the requested-source
relations tie the selected times to reference observations or trusted parse
results. The final proof combines the resolved batch relation and stream
publication; it does not prove the native date parser or timestamp syscall.

## truncate

### Implementation

[TruncateCore.Resolve](../bench/utils/truncate/Impl/TruncateCore.dfy#L65) parses size
operands and resolves modifier and configuration errors before filesystem work.
For each file it opens or creates the path, unless no-create permits an absent
path to be skipped. [ResizeOne](../bench/utils/truncate/Impl/TruncateCore.dfy#L171)
obtains status when relative sizing or IO-block scaling needs it, chooses the
reference or current size, calculates the requested size, checks overflow, clamps
negative results to zero, and calls `TruncateFile`. Supported adjustments include
relative changes, upper/lower bounds, and rounding to a multiple. Later files
continue after errors.

### Proof idea

[TruncateSpec.AdjustedSize](../bench/utils/truncate/Spec/TruncateSpec.dfy#L302) gives the
arithmetic meaning of the requested adjustment.
[ResizeOutcome](../bench/utils/truncate/Spec/TruncateSpec.dfy#L351) relates needed status
observations, block scaling, overflow diagnostics, and the trusted truncation
effect. [FilesRelation](../bench/utils/truncate/Spec/TruncateSpec.dfy#L411) requires an
ordered sequence of filesystem and status-cursor states, concatenated errors,
and a cumulative failure flag. [TruncateProof.FilesWitness](../bench/utils/truncate/Proof/TruncateProof.dfy#L68)
packages the loop's states into this relation. Reference lookup and configuration
cases are joined by `RunWitness`. Opening/creation precedes resizing, so an error
in sizing or truncation need not undo a newly created file.

## unlink

### Implementation

[UnlinkCore.Prepare](../bench/utils/unlink/Impl/UnlinkCore.dfy#L67) handles information
and operand-count errors, then makes one `UnlinkPath` call for the selected path.
It emits no normal output and turns a native failure into the specified quoted
pathname and error diagnostic. Stream publication follows the filesystem attempt.

### Proof idea

[UnlinkSpec.UnlinkResult](../bench/utils/unlink/Spec/UnlinkSpec.dfy#L149) is the
before/after relation supplied by `UnlinkPathSpec`.
[PreparedSpec](../bench/utils/unlink/Spec/UnlinkSpec.dfy#L251) ties that outcome to
filesystem effects, diagnostics, and the normal exit, while information and
operand errors use their own cases.
[UnlinkProof.CoreSummaryImpliesSpec](../bench/utils/unlink/Proof/UnlinkProof.dfy#L22)
combines the prepared relation with the trusted stream-write results. The utility
proof establishes the call and reporting behavior; inode removal and hard-link
semantics reside in the IO contract.
