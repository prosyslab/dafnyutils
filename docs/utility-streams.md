# Stream utility implementations and proofs

This companion to the [utility guide](utility-guide.md) explains the algorithms
and central specifications for the stream utilities. Each section describes the
repository's modeled behavior; the guide explains the shared entrypoint and IO
trust boundary. These are source-reading notes, not a new verification result.

## base64

### Implementation

[`TransformMethod`](../bench/utils/base64/Impl/Base64Core.dfy) either encodes groups of
three bytes into four alphabet characters with padding, then wraps the encoded
text, or filters the input and decodes groups of four characters. Without
ignore-garbage mode the filter removes newlines; with it, only alphabet characters
and `=` survive. Terminal decoding can return bytes together with an invalid-input
status. `TransformAfterReadMethod` treats an interrupted decode specially: it uses
completed input buffers and complete quartets, so a read failure does not imply
that every available partial byte is decoded.

### Proof idea

[`EncodeRelation`, `WrappedRelation`, and `DecodeRelation`](../bench/utils/base64/Spec/Base64Spec.dfy)
describe block arithmetic, line fragments, and valid blocks followed by a terminal
fragment. `KeptInputRelation` requires an ordered selection containing exactly the
bytes permitted by the filter. These relations specify both output and success,
including partial terminal output. In
[`TransformRelationImpliesSpec`](../bench/utils/base64/Proof/Base64Proof.dfy), separate
encoding, wrapping, filtering, and decoding refinements establish the appropriate
branch. The interrupted-read bridge adds the buffer-prefix restriction before
the input observation and command relations are composed.

## cat

### Implementation

[`Prepare`](../bench/utils/cat/Impl/CatCore.dfy) reads operands in order and concatenates
the returned bytes, including data carried by read failures, while collecting
diagnostics. It then renders that combined stream once. `ProcessBytesMethod`
tracks the next line number, whether the current byte starts a line, and the
blank-line streak. These determine numbering, blank-line squeezing, end markers,
and visible representations of tabs and nonprinting bytes. Rendering after
concatenation lets line state span operand boundaries.

### Proof idea

[`KeptAt`, `NumberedAt`, and `LineNumberRelation`](../bench/utils/cat/Spec/CatSpec.dfy)
classify source positions directly: a numbered position receives one plus the
number of earlier numbered positions. `RenderRelation` assigns a fragment to
every byte and partitions the final output into exactly those fragments.
[`RenderWitnessRefines`](../bench/utils/cat/Proof/CatProof.dfy) connects the rendering
state to these position and cardinality properties. The input-trace refinement
separately establishes operand order, returned data, diagnostics, and stdin
consumption; together they establish `RunRelation`, including output retained when
an input fails.

## comm

### Implementation

[`CommRenderCore`](../bench/utils/comm/Impl/CommRenderCore.dfy) splits both inputs into
newline- or NUL-delimited records and compares records lexicographically by byte.
Its merge consumes the smaller leading record, or both equal records, and renders
the first-only, second-only, or common column. Suppressed columns change the
prefix delimiters; an optional totals row counts all three categories.
[`Prepare`](../bench/utils/comm/Impl/CommCore.dfy) reads the operands in order, rejects
unsorted successful inputs with no comparison output, and has a separate plan for
read failures that can preserve output from complete records before the failure.

### Proof idea

[`RecordPartition`, `BytesLess`, and `OutputRelation`](../bench/utils/comm/Spec/CommRenderSpec.dfy)
specify record boundaries, the first differing byte or proper-prefix ordering,
and the resulting merge fragments. A merge witness accounts for every consumed
record and its category count.
[`MergeWitnessForCore` and `OutputRelationForCore`](../bench/utils/comm/Proof/CommProof.dfy)
build those witnesses from the recursive merge and connect the comparison result
to byte ordering. Sortedness and failed-read lemmas establish the alternatives in
[`SpecCmd`](../bench/utils/comm/Spec/CommSpec.dfy), including its early-abort and partial
output cases.

## csplit

### Implementation

[`AnalyzeNumbers` and `SplitPlanFor`](../bench/utils/csplit/Impl/CsplitCore.dfy) validate
numeric line patterns and locate the corresponding byte cuts. The resulting
pieces are written in order to generated `xx` names, with byte counts on stdout
for successful writes. `WritePieces` stops on a write failure and attempts cleanup
while recursion unwinds; an out-of-range split similarly writes its planned
pieces before issuing the terminal diagnostic and cleaning up. Cleanup is an IO
operation that can itself fail, so failure does not promise restoration of the
original filesystem. This slice covers numeric patterns rather than regular
expressions or repeat syntax.

### Proof idea

[`LineCutRelation` and `PiecePartitionRelation`](../bench/utils/csplit/Spec/CsplitSpec.dfy)
describe cuts by newline counts and require pieces to partition the input.
`SplitPlanRelation` identifies the first out-of-range cut. `WriteTraceRelation`
adds ordered write attempts, byte-count output, and cleanup observations through
intermediate filesystem states, retaining partial-write effects.
[`SplitPlanRefines` and `WriteTraceSummaryRefines`](../bench/utils/csplit/Proof/CsplitProof.dfy)
connect the computed cuts and recursive writes to these witnesses. Separate
read-failure reasoning restricts partial stdin processing to complete input
records before the write/cleanup relation is applied.

## cut

### Implementation

[`CutData`](../bench/utils/cut/Impl/CutCore.dfy) divides input into newline- or
NUL-delimited records. It scans each record's one-based positions, retains those
in the range union or its complement, and optionally inserts output delimiters at
the specified selection-group boundaries. Every output record receives a record
terminator, including an unterminated final input record. The modeled byte and
character modes share byte semantics; field selection and locale-dependent
multibyte handling are outside this slice.

### Proof idea

[`SelectedIndexSequence`](../bench/utils/cut/Spec/CutSpec.dfy) requires strictly
increasing indices that contain every selected position and no others.
`RecordSelectionWitnessRelation` relates each retained byte and any preceding
output delimiter to its fragment. `DataSelectionRelation` combines that relation
with an input record partition and terminated output fragments. Much of the
selection argument lives beside the implementation in
[`SelectRecordSatisfiesRelation` and `DataSelectionSatisfiesRelation`](../bench/utils/cut/Impl/CutCore.dfy).
[`OutputPieceRefines` and `InputTraceCoreRefines`](../bench/utils/cut/Proof/CutProof.dfy)
then connect those results to ordered input reads, including partial stdin data
on a stream failure.

## dd

### Implementation

[`ReadBlock`, `FlushFull`, and `RunCore`](../bench/utils/dd/Impl/DdCore.dfy) copy finite
stdin to stdout with explicit `status=none`. A single bounded native read may
return a short prefix; full-block mode accumulates these reads locally. The
implementation applies ASCII case conversion, NUL padding and adjacent-byte
swapping, retaining an odd byte across input records. Separate input and output
block sizes and count limits determine when it reads and flushes. A failed
output stops further input consumption. File descriptors, seeking and timed
statistics are outside [this stream slice](../bench/utils/dd/dd.md).

### Proof idea

[`Transformed`, `InputPartition`, and `OutputPartition`](../bench/utils/dd/Spec/DdSpec.dfy)
relate each output byte to its source position and constrain input records,
native observations and output boundaries. They distinguish intermediate full
blocks from the final flush, including committed prefixes and GNU's diagnostic
choice on failure. Local append lemmas preserve those relations as blocks are
read and written. The final `RunCore` postcondition establishes `Spec`; the
shared `ReadStdinChunk` contract supplies only one bounded read, with no trusted
padding, conversion or block-count policy.

## expand

### Implementation

[`ExpandDataFromMethod`](../bench/utils/expand/Impl/ExpandCore.dfy) walks the bytes while
tracking the display column and whether it is still in the initial blank region.
A tab becomes spaces up to the next explicit stop or the configured repeating
stop; after a nonrepeating list ends it becomes one space. Newline resets the
column and backspace decreases it without going below zero. Initial-only mode
copies bytes after the leading blank region until the next newline. `Prepare`
carries column and leading-region state across operands and accumulates read
diagnostics alongside any output from partial stdin data.

### Proof idea

[`TabStopRelation`](../bench/utils/expand/Spec/ExpandSpec.dfy) selects the first future
stop or constrains the repeating distance arithmetically. `ByteExpansionRelation`
specifies each byte's output piece and column/leading-state effects;
`DataExpansionWitnessRelation` quantifies over a full sequence of these pieces and
states. [`TabStopRelationHolds` and `DataExpansionWitnessSummaryImpliesRelation`](../bench/utils/expand/Proof/ExpandProof.dfy)
connect the stop search and byte loop to those properties. The input-trace bridge
composes these witnesses across operands, preserving both state continuity and
the recorded read failures.

## fold

### Implementation

[`FittingPrefixMethod`](../bench/utils/fold/Impl/FoldCore.dfy) scans a line until the
next byte would exceed the width, retaining at least one byte and remembering the
last blank. `BreakPrefixMethod`
uses that blank when space mode calls for it; `FoldLineMethod` repeats on the
remaining suffix and inserts newlines between segments. Byte mode counts bytes;
column mode handles tabs, carriage returns, backspaces, and NUL through
`StepColumn`. `EffectiveInputMethod` deliberately restricts processing to the
prefix before the first `0xff` byte, a modeled behavior that matters when reading
this implementation as a general-purpose fold algorithm. A stream read failure
can still contribute folded partial data alongside its diagnostic.

### Proof idea

[`FittingEndRelation` and `BreakPointRelation`](../bench/utils/fold/Spec/FoldSpec.dfy)
characterize the width boundary and, when applicable, the last blank within the
fitting prefix. `LinePartitionRelation` requires nonempty segments whose join is
the original line and whose ends satisfy those break conditions.
`DataFoldRelation` adds the effective-prefix restriction and preserves original
record termination. The Core methods establish these relations directly while
constructing segments. [`FoldProof`](../bench/utils/fold/Proof/FoldProof.dfy) principally
connects width parsing and command selection to the specification and carries the
already established input/output relation into the final contract.

## head

### Implementation

[`RenderData`](../bench/utils/head/Impl/HeadCore.dfy) selects a byte prefix or a record
prefix, either keeping the requested count or removing that many units from the
end. `Prepare` processes operands in order, adds headers according to the command
and earlier header-producing reads, and collects diagnostics while continuing to
later operands. `OutputPiece` preserves selectable data from stream failures and
file close failures; an ordinary failed file read contributes no output.

### Proof idea

[`RecordCountRelation` and `RecordSelectionRelation`](../bench/utils/head/Spec/HeadRecordSpec.dfy)
count delimiters plus a possible unterminated final record, then choose a cut
whose prefix has exactly the required number of records. Byte selection is a
direct length-bounded prefix relation in
[`HeadSpec`](../bench/utils/head/Spec/HeadSpec.dfy). The input trace specifies read
outcomes, headers, stdout/error fragments, and failure status in operand order.
[`RecordSelectionRelation` and `CoreInputTraceWitnessRelation`](../bench/utils/head/Proof/HeadProof.dfy)
connect the recursive record selection and accumulated operand results to those
cut and trace witnesses.

## join

### Implementation

[`Records`, `Tiles`, and `Render`](../bench/utils/join/Impl/JoinDataCore.dfy) split binary
input into records and fields, compare join keys and group equal-key runs. Each
matched pair of runs emits its Cartesian product in GNU order; unmatched runs
follow `-a`/`-v`, and field lists, filler, headers and NUL delimiters control the
rendered rows. [`JoinPlanCore`](../bench/utils/join/Impl/JoinPlanCore.dfy) accounts for
read-ahead when locating order warnings and the first fatal order error, so
previous output and diagnostic order remain observable.

### Proof idea

[`RecordCuts`, `Fields`, `Tiles`, and `PrintedRow`](../bench/utils/join/Spec/JoinDataSpec.dfy)
constrain exact input partitions, maximal key-match rectangles and every output
field. Row coordinates prescribe Cartesian ordering; output partitions prevent
missing or extra rows. `ReadLayout`, `FirstWarning`, and `FirstFatal` constrain
the warning/error positions independently of the implementation's scans.
The local algorithms construct these witnesses before the IO proof composes
reads and writes into the principal `Spec` contract. Key comparison, field
selection and warning policy add no native trust.

## nl

### Implementation

[`Prepare`](../bench/utils/nl/Impl/NlCore.dfy) normalizes each nonempty input by adding a
missing final newline, combines the inputs, and splits them into lines. It rejects
logical-page delimiter lines before rendering. `RenderLinesMethod` starts at one,
numbers lines selected by the body style, increments only for numbered lines,
and prefixes unnumbered lines with spaces. Number format and separator determine
the visible prefix. Regex body styles and logical-page processing are explicitly
unsupported in this slice.

### Proof idea

[`LinePartitionRelation`, `LineNumberRelation`, and `OutputWitnessRelation`](../bench/utils/nl/Spec/NlSpec.dfy)
describe the combined input's line partition, successive numbering values, and
one rendered fragment per line. `NormalizedInputRelation` separately captures
the newline added at each input boundary.
[`OutputWitnessRefines` and `InputTraceRefines`](../bench/utils/nl/Proof/NlProof.dfy)
connect the line-rendering witnesses and ordered read observations to these
relations. `PreparedSpecFromTrace` distinguishes normal rendering from the
delimiter-rejection branch, which retains input diagnostics but emits no numbered
output. The entrypoint passes the Core's ghost trace witnesses into that proof.

## paste

### Implementation

[`RenderParallel` and `RenderSerial`](../bench/utils/paste/Impl/PasteCore.dfy) render a
table of input records in two ways: parallel mode joins equal-index records from
all operands, substituting empty fields when an input is shorter; serial mode
joins each input's records into one output record. Delimiter escapes are decoded
and the delimiter list cycles between fields. Repeated stdin operands in parallel
mode receive alternating records from the combined stdin data via
`SelectStdinLines`. A blocking file-read failure suppresses parallel output;
serial mode can still render other readable entries. Other read errors can leave
partial records available and produce a failing status.

### Proof idea

[`EntriesForOutputRelation`](../bench/utils/paste/Spec/PasteSpec.dfy) specifies how
records are assigned to operands, including the stdin distribution.
`Output` is the canonical concatenation of the parallel or serial records:
fields, cyclic delimiters, missing fields, and record terminators determine the
exact bytes. `Join` supplies the common cyclic-delimiter rule. `LinesRelation`
fixes records by reconstructing the original bytes, with the trailing terminator
determined by the input. Stdin record assignment uses the preceding and total
`StdinCount`, without a position list. Delimiter decoding uses a partition into
literal and escape tokens;
`DelimiterValue` fixes either the decoded list or the trailing-backslash error.
`VisibleErrors` selects the first blocking diagnostic in parallel mode, or
concatenates diagnostics in operand order. `InputRelation` describes remaining
stdin by the number of stdin operands and combines their observed read data.
[`EntriesForOutputRefines` and `OutputRefines`](../bench/utils/paste/Proof/PasteProof.dfy)
establish the record assignments and exact output equality. Assembly witnesses
for delimiters and diagnostics remain in the proof module. `LinesRelationEquivalent`
proves equivalence with the former line-partition contract. Rendering proofs
connect Core directly to the canonical concatenations. `InputRefinement` relates
the implementation's stdin states and data partitions to the input relation,
preserving partial reads and failures.

## tail

### Implementation

[`RenderData`](../bench/utils/tail/Impl/TailCore.dfy) selects a suffix containing the
last requested bytes or records, or drops the units preceding a requested
one-based start position. [`RecordCuts`](../bench/utils/tail/Impl/TailRecordCore.dfy)
builds the record boundary list used to choose that suffix. The operand loop adds
headers and diagnostics, retains data from stream and file-close failures, and
handles zero-length trailing selections and directory-error headers separately.
This is finite input selection; follow mode and waiting for future writes are
outside the modeled slice.

### Proof idea

[`DropFirstRecordsRelation` and `TakeLastRecordsRelation`](../bench/utils/tail/Spec/TailRecordSpec.dfy)
describe a complete record partition and the boundary where the retained suffix
begins. [`RenderDataRelation`](../bench/utils/tail/Spec/TailSpec.dfy) selects the byte or
record relation and accounts for the one-based start convention. The input trace
then relates observations, header counts, fragments, and status.
[`RecordCutsGiveRelation`, `RenderDataGivesRelation`, and `BuildPrefixWitness`](../bench/utils/tail/Proof/TailProof.dfy)
connect the computed boundaries and operand accumulators to these partition and
trace properties, including failure-dependent output.

## tee

### Implementation

[`Prepare`](../bench/utils/tee/Impl/TeeCore.dfy) reads stdin, then passes the returned
bytes to each output path in operand order. `WriteOne` chooses overwrite/create
or append; `WriteOutputs` continues after a failed write and combines diagnostics
and failure status. The same input bytes are planned for stdout, including bytes
returned before a stdin read failure. File writes happen before stdout emission,
so a later stream-write failure does not undo them. Partial file writes and
earlier successful writes likewise remain observable.

### Proof idea

[`WriteOneSpecFields`](../bench/utils/tee/Spec/TeeSpec.dfy) uses the file write/append
contracts to constrain each filesystem result, including failed partial writes.
`WriteOutputsSpecFields` requires intermediate `WriteState` values: every adjacent
pair accounts for one output path, cumulative diagnostics, and an accumulated
failure status. [`WriteOutputsSummaryFieldsImpliesSpec`](../bench/utils/tee/Proof/TeeProof.dfy)
constructs that state sequence from the recursive writes. `PreparedSpec` combines
it with the stdin observation and the planned stdout copy; emission then accounts
for the stream result without claiming transactional file effects.

## tr

### Implementation

[`DecodeSet`](../bench/utils/tr/Impl/TrCore.dfy) expands the supported literals,
escapes, and ascending byte ranges, rejecting unsupported set constructs.
`Command` separately collects escape warnings. `DeleteAndTranslate` removes
selected bytes or translates them;
translation uses the last occurrence in set one and repeats the final byte of a
shorter set two. `SqueezeFrom` then removes adjacent repetitions belonging to the
squeeze set. `Prepare` applies this pipeline to stdin bytes even when a read
failure returned partial data, preserving the transformed output and adding a
read diagnostic.

### Proof idea

[`TranslationRelation`](../bench/utils/tr/Spec/TrSpec.dfy) specifies the last matching
set position and its clamped replacement index. `Transform` fixes the exact
output: `Select` takes the ordered image of undeleted source positions,
`TranslateByte` fixes each replacement, and `Squeezed` retains the starts of
repeated runs and bytes outside the squeeze set. `PreparedSpec` equates stdout
directly to this function's result. The retained-index and squeeze relations live
in [`TrProof`](../bench/utils/tr/Proof/TrProof.dfy); `SelectInOrder`,
`DeleteTranslateCanonical`, and `SqueezeCanonical` connect their witnesses to the
sequence functions. `CoreOutputRefines` proves exact byte equality.
Separate set-decoding and command proofs account for validation, expansion, and
warnings before the transformation is applied.

## tsort

### Implementation

[`Tokenize` and `BuildGraph`](../bench/utils/tsort/Impl/TsortGraphBuildCore.dfy) split
input into pairs, register every distinct name, and retain duplicate edges in
reverse input order. [`SortGraph`](../bench/utils/tsort/Impl/TsortCore.dfy) starts
with zero-indegree vertices in byte order and uses a FIFO queue for vertices
released later.
When the queue is empty but vertices remain,
[`BreakStalledCycle`](../bench/utils/tsort/Impl/TsortCycleCore.dfy) selects GNU's cycle,
removes one edge occurrence, and resumes the sort. Cycles produce diagnostics
and failure status while preserving emitted vertices.

### Proof idea

[`SortCertificate` and `EventText`](../bench/utils/tsort/Spec/TsortSpec.dfy) relate
vertex ranks, edge-removal ranks, release order, and selected cycles to exact
output and diagnostic fragments. The step and cycle lemmas record a finite
sequence of emission and edge-cut events.
[`Certificate` and `Finish`](../bench/utils/tsort/Proof/TsortProof.dfy) connect that
sequence to `GraphResult`. Input and stream relations then account for odd-token
rejection, read/close failures, and committed output prefixes. The fully proved
[`PreparedRun`](../bench/utils/tsort/Proof/TsortProof.dfy) bridge assembles these
read and result relations before the final
[`RunCore`](../bench/utils/tsort/Impl/Tsort.dfy) contract. The
[task specification](../bench/utils/tsort/tsort.md) records the CLI and native IO
trust boundary.

## uniq

### Implementation

[`GroupsFrom`](../bench/utils/uniq/Impl/UniqCore.dfy) forms consecutive runs of equal
lines, keeping each run's first original line and its count. Equality can skip a
specified number of blank-separated fields and compare the remaining bytes with
ASCII case folding. `RenderGroups` selects singleton and/or repeated runs and
optionally prefixes their counts; emitted lines end with newline. This operates
on adjacent runs, so equal lines separated by a different line stay in separate
groups. A stdin stream failure can still supply partial data for rendering.

### Proof idea

[`RunPartitionWitnessRelation`](../bench/utils/uniq/Spec/UniqSpec.dfy) requires nonempty
runs that concatenate to the input records, records each run's exact length and
first line, and requires neighboring run representatives to differ under the
chosen comparison. `GroupRenderRelation` constrains filtering and count prefixes;
`OutputRelation` combines the record, run, and output partitions.
[`GroupsWitness` and `OutputRelationForCore`](../bench/utils/uniq/Proof/UniqProof.dfy)
construct those partitions and rendering fragments. Field-skip canonicality
lemmas connect the executable comparison to the specified field boundaries before
the grouping argument uses it.

## wc

### Implementation

[`CountDataMethod`](../bench/utils/wc/Impl/WcCore.dfy) scans bytes once, tracking newline
count, word starts, byte/character count, current display column, and maximum
column. This model makes character count equal byte count; word whitespace and
display-width behavior are the explicit rules in `IsWordSpace` and `NextLineLen`.
`Prepare` collects entries in operand order, then renders selected counts with a
shared field width and optional total. Totals add counts but take the maximum
line width. Partial stdin data receives counts despite a read failure; failed
file reads normally contribute diagnostics without an entry, with a separate
zero-count directory case.

### Proof idea

[`CountRelation`](../bench/utils/wc/Spec/WcSpec.dfy) equates counts to input length and
the cardinalities of newline and word-start index sets. A column trace and
`MaximumRelation` characterize the maximum width. The scan maintains those sets
and column witnesses rather than relying only on matching an executable counter.
[`CountWitnessImpliesRelation`](../bench/utils/wc/Proof/WcProof.dfy) projects them into
the specification. `RunOutputRelationForCore` separately supplies total-count,
field-width, decimal-rendering, and output-fragment witnesses; the ordered input
trace then ties the rendered entries and diagnostics to actual read outcomes.
