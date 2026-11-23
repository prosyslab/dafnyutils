include "../Impl/ChmodDirectoryRuntime.dfy"
include "ChmodTraversalProof.dfy"

module ChmodObservationProof {
  import W = BenchWorld
  import C = IOContract
  import Base = ChmodSpec
  import Schema = ChmodSchema
  import Spec = ChmodDescriptorSpec
  import Operand = ChmodOperandSpec
  import Identity = ChmodOperandProof
  import Directory = ChmodDirectoryRuntime
  import Frame = ChmodTraversalProof
  import FrameSpec = ChmodTraversalSpec

  lemma OffsetValid(fs: W.FileSystem, native: W.CwdContext, offset: nat)
    requires C.CwdContextFields(fs, native)
    ensures C.CwdContextFields(fs, Operand.AtOffset(native, offset))
  {
    hide *;
    reveal C.CwdContextFields(), Operand.AtOffset();
  }

  lemma {:isolate_assertions} EntryState(cmd: Schema.ChmodCmd, scope: Spec.Scope,
                                         display: string, operand: Operand.Operand, top: bool, fs: W.FileSystem,
                                         native: W.CwdContext, cursor: nat, entry: Spec.Entry)
    requires C.CwdContextFields(fs, native)
    requires Spec.EntryFields(cmd, scope, display, operand, top, fs, native, cursor, entry)
    ensures entry.result.fs == fs && C.CwdContextFields(fs, entry.result.native)
    ensures FrameSpec.FrameFields(native, entry.result.native)
    ensures entry.result.native.capabilities == native.capabilities
  {
    hide *;
    Frame.Entry(cmd, scope, display, operand, top, fs, native, cursor, entry);
    reveal Spec.EntryFields(), Operand.AtOffset();
    OffsetValid(fs, native, entry.rawAttempts);
    OffsetValid(fs, native, entry.rawAttempts+1);
  }

  lemma {:isolate_assertions} SetState(context: Base.ObservationContext, scope: Spec.Scope,
                                       fs: W.FileSystem, native: W.CwdContext, operand: Operand.Operand, follow: bool,
                                       mode: bv32, afterFs: W.FileSystem, after: W.CwdContext, ok: bool, err: int)
    requires Operand.SetFields(context, scope.now, fs, native, operand, follow, mode,
                               afterFs, after, ok, err)
    ensures C.CwdContextFields(afterFs, after)
    ensures FrameSpec.FrameFields(native, after)
    ensures W.FileSystemTopologyUnchangedExceptMode(fs, afterFs)
    ensures after.capabilities == native.capabilities
  {
    hide *;
    Frame.Mode(context, scope.now, fs, native, operand, follow, mode, afterFs, after, ok, err);
    reveal Operand.SetFields(), C.SetFileModeAtCwdSpec(), C.SetFileModeAtDirSpec(),
           C.SetFileModeFromCwdTargetContractFields();
    if !ok { Identity.TopologyReflexive(fs); }
    reveal C.CwdContextReadStepFields();
  }

  lemma {:isolate_assertions} ChangeState(cmd: Schema.ChmodCmd, plan: Base.SpecModePlan,
                                          scope: Spec.Scope, entry: Spec.Entry, fs: W.FileSystem, native: W.CwdContext,
                                          cursor: nat, change: Spec.Change)
    requires C.CwdContextFields(fs, native)
    requires Spec.ChangeFields(cmd, plan, scope, entry, fs, native, cursor, change)
    ensures C.CwdContextFields(change.result.fs, change.result.native)
    ensures FrameSpec.FrameFields(native, change.result.native)
    ensures W.FileSystemTopologyUnchangedExceptMode(fs, change.result.fs)
    ensures change.result.native.capabilities == native.capabilities
  {
    hide *;
    reveal Spec.ChangeFields();
    var mode := Operand.StatusAt(Base.AtCursor(scope.context, cursor), fs, native,
                                 entry.identity.operand, 0, entry.identity.metadataFollow);
    Frame.Offset(native, 1);
    OffsetValid(fs, native, 1);
    if mode.Err? {
      Identity.TopologyReflexive(fs);
      reveal Operand.AtOffset();
    } else {
      SetState(Base.AtCursor(scope.context, cursor+1), scope, fs, Operand.AtOffset(native, 1),
               entry.identity.operand, Spec.ModeFollow(cmd, entry.identity.top), change.desired,
               change.setFs, change.setNative, change.setErr == 0, change.setErr);
      Frame.Transitive(native, Operand.AtOffset(native, 1), change.setNative);
      assert change.result.fs == change.setFs;
      assert Operand.AtOffset(native, 1).capabilities == native.capabilities by { reveal Operand.AtOffset(); }
      if change.setErr == 0 {
        var result: Base.SpecPathResult :| Spec.SuccessFields(cmd, plan, scope, entry,
                                                              change.setFs, change.setNative, cursor+1, mode.v.mode, W.NormalizeMode(change.desired),
                                                              change.result.cursor, change.result.native, result) &&
                                           change.result == Spec.State(change.setFs, change.result.cursor, change.result.native,
                                                                       result.stdoutChunk, result.stderrChunk, result.ok);
        reveal Spec.SuccessFields();
        var count: nat := if Base.SpecPostChangeLookupNeeded(cmd, W.NormalizeMode(change.desired)) then 1 else 0;
        Frame.Offset(change.setNative, count);
        OffsetValid(change.setFs, change.setNative, count);
        Frame.Transitive(native, change.setNative, change.result.native);
        assert change.result.native == Operand.AtOffset(change.setNative, count);
        assert change.result.native.capabilities == change.setNative.capabilities by { reveal Operand.AtOffset(); }
        assert C.CwdContextFields(change.result.fs, change.result.native);
      } else {
        assert change.result.native == change.setNative;
        assert C.CwdContextFields(change.result.fs, change.result.native);
      }
      reveal Operand.AtOffset();
    }
  }

  lemma {:isolate_assertions} DirectoryState(fs: W.FileSystem, native: W.CwdContext,
                                             observations: W.DirectoryObservations, operation: W.DirectoryOperation, handle: int,
                                             cursor: nat, response: W.DirectoryResponse, after: W.CwdContext)
    requires C.CwdContextFields(fs, native)
    requires operation == W.DirectoryReadNext || operation == W.DirectoryClose
    requires C.ContextOperationSpec(fs, native, observations, operation, handle, 0, "",
                                    cursor, cursor, response, after)
    ensures C.CwdContextFields(fs, after)
    ensures FrameSpec.FrameFields(native, after)
  {
    hide *;
    Frame.DirectoryOperation(fs, native, observations, operation, handle, cursor, response, after);
    reveal C.ContextOperationSpec(), C.DirectoryRequestForContextFields(), C.DirectoryOperationSpec(),
           C.DirectoryNextPositionFields(), C.DirectoryNextCapabilitiesFields(),
           C.DirectoryResponseFields(), C.CwdContextFields(), C.LiveDirectoryCapabilitiesFields();
    forall h | h in after.capabilities
      ensures var state := after.capabilities[h];
              C.LiveDirectoryTopologyFields(state.anchorFs, state.anchorTopology) &&
              state.anchorTopology.nodes.Keys <= after.topology.nodes.Keys &&
              state.position in state.anchorTopology.nodes && state.position in after.topology.nodes &&
              state.remaining <= C.DirectoryCapabilityNamesFields(state.anchorTopology, state.position, state.includeDots) &&
              |state.descriptor| <= 1
    {
      assert h in native.capabilities;
    }
  }
}
