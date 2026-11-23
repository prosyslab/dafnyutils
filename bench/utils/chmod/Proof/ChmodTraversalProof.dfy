include "../Spec/ChmodTraversalSpec.dfy"
include "ChmodOperandProof.dfy"
include "../Spec/ChmodDescriptorSpec.dfy"

module ChmodTraversalProof {
  import W = BenchWorld
  import C = IOContract
  import Base = ChmodSpec
  import Operand = ChmodOperandSpec
  import Identity = ChmodOperandProof
  import Spec = ChmodTraversalSpec
  import Descriptor = ChmodDescriptorSpec
  import Schema = ChmodSchema

  lemma Reflexive(native: W.CwdContext)
    ensures Spec.FrameFields(native, native)
  {
    hide *;
    reveal Spec.FrameFields(), W.NodeShapeUnchangedExceptMode();
  }

  lemma {:isolate_assertions} Transitive(first: W.CwdContext, middle: W.CwdContext, last: W.CwdContext)
    requires Spec.FrameFields(first, middle) && Spec.FrameFields(middle, last)
    ensures Spec.FrameFields(first, last)
  {
    hide *;
    reveal Spec.FrameFields(), W.NodeShapeUnchangedExceptMode();
    forall position | position in first.topology.nodes
      ensures var prior := first.topology.nodes[position];
              var next := last.topology.nodes[position];
              next.status.hostKey == prior.status.hostKey && next.status.kind == prior.status.kind &&
              next.parent == prior.parent && next.pathname == prior.pathname &&
              next.selfRawInode == prior.selfRawInode && next.parentRawInode == prior.parentRawInode &&
              next.parentMountBoundary == prior.parentMountBoundary && next.entries.Keys == prior.entries.Keys &&
              forall name | name in prior.entries ::
                var oldEntry := prior.entries[name];
                var newEntry := next.entries[name];
                newEntry.rawInode == oldEntry.rawInode && newEntry.kind == oldEntry.kind &&
                newEntry.directory == oldEntry.directory && newEntry.mountBoundary == oldEntry.mountBoundary &&
                newEntry.status.hostKey == oldEntry.status.hostKey && newEntry.status.kind == oldEntry.status.kind
    {
      assert position in middle.topology.nodes;
    }
  }

  lemma ReadStep(before: W.CwdContext, after: W.CwdContext)
    requires C.CwdContextReadStepFields(before, after)
    ensures Spec.FrameFields(before, after)
  {
    hide *;
    reveal C.CwdContextReadStepFields(), Spec.FrameFields(), W.NodeShapeUnchangedExceptMode();
  }

  lemma {:isolate_assertions} ModeUpdate(before: W.CwdContext, key: W.HostInodeKey, mode: bv32, now: int)
    ensures Spec.FrameFields(before,
                             before.(topology := C.ModeChangedTopologyFields(before.topology, key, mode, now), ordinal := before.ordinal+1))
  {
    hide *;
    reveal Spec.FrameFields(), C.ModeChangedTopologyFields(), C.ModeChangedDirectoryFields(),
           C.ModeChangedEntryFields(), C.ModeChangedStatusFields(), C.ModeChangedRecordsFields(),
           C.ModeChangedRecordFields(), W.InodeRecordWithNode(), W.WithNodeMode(), W.WithNodeChangeTime(),
           W.WithNodeTimes(), W.NodeTimes(), W.NodeShapeUnchangedExceptMode();
  }

  lemma {:isolate_assertions} Mode(context: Base.ObservationContext, now: int,
                                   fs: W.FileSystem, before: W.CwdContext, operand: Operand.Operand, follow: bool, mode: bv32,
                                   afterFs: W.FileSystem, after: W.CwdContext, ok: bool, err: int)
    requires Operand.SetFields(context, now, fs, before, operand, follow, mode, afterFs, after, ok, err)
    ensures Spec.FrameFields(before, after)
  {
    hide *;
    reveal Operand.SetFields(), C.SetFileModeAtCwdSpec(), C.SetFileModeAtDirSpec(),
           C.SetFileModeFromCwdTargetContractFields();
    if !ok { ReadStep(before, after); }
    else {
      reveal C.CwdResolvedModeCanSucceedFields();
      reveal Operand.ResolveTarget();
      var target := Operand.ResolveTarget(fs, before, operand, follow);
      assert target.Ok?;
      ModeUpdate(before, C.CwdTargetRecordFields(fs, before, target.v).hostKey, mode, now);
    }
  }

  lemma {:isolate_assertions} Extension(before: W.CwdContext, after: W.CwdContext)
    requires C.Extends(before.topology, after.topology)
    requires after.hint == before.hint && after.position == before.position
    requires after.legacyHandles == before.legacyHandles && after.legacyOrigins == before.legacyOrigins
    ensures Spec.FrameFields(before, after)
  {
    hide *;
    reveal C.Extends(), Spec.FrameFields(), W.NodeShapeUnchangedExceptMode();
  }

  lemma {:isolate_assertions} Open(context: Base.ObservationContext, fs: W.FileSystem,
                                   before: W.CwdContext, operand: Operand.Operand, after: W.CwdContext,
                                   ok: bool, handle: int, err: int)
    requires Operand.OpenFields(context, fs, before, operand, after, ok, handle, err)
    ensures Spec.FrameFields(before, after)
  {
    hide *;
    reveal Operand.OpenFields(), C.OpenDirAtCwdSpec(), C.OpenDirAtDirSpec(), C.OpenDirFromCwdTargetContractFields();
    if !ok { ReadStep(before, after); }
    else { Extension(before, after); }
  }

  lemma {:isolate_assertions} DirectoryOperation(fs: W.FileSystem, before: W.CwdContext,
                                                 observations: W.DirectoryObservations, operation: W.DirectoryOperation, handle: int,
                                                 cursor: nat, response: W.DirectoryResponse, after: W.CwdContext)
    requires operation == W.DirectoryReadNext || operation == W.DirectoryClose
    requires C.ContextOperationSpec(fs, before, observations, operation, handle, 0, "", cursor, cursor, response, after)
    ensures Spec.FrameFields(before, after)
  {
    hide *;
    reveal C.ContextOperationSpec(), C.DirectoryRequestForContextFields(), C.DirectoryOperationSpec(),
           C.DirectoryNextPositionFields(), Spec.FrameFields(), W.NodeShapeUnchangedExceptMode();
  }

  lemma {:isolate_assertions} ReadCurrent(before: W.CwdContext, after: W.CwdContext,
                                          capability: W.DirectoryCapabilityState)
    requires Spec.FrameFields(before, after)
    requires C.DirectoryCapabilityReadCurrentFields(before.topology, capability)
    ensures C.DirectoryCapabilityReadCurrentFields(after.topology, capability)
  {
    hide *;
    reveal Spec.FrameFields(), C.DirectoryCapabilityReadCurrentFields(), C.DirectoryCapabilityAnchorCurrentFields(),
           C.DirectoryCapabilityNamesFields();
  }

  lemma {:isolate_assertions} Anchor(beforeFs: W.FileSystem, afterFs: W.FileSystem,
                                     before: W.CwdContext, after: W.CwdContext, operand: Operand.Operand)
    requires W.FileSystemTopologyUnchangedExceptMode(beforeFs, afterFs)
    requires Spec.FrameFields(before, after) && Operand.AnchorSnapshot(beforeFs, before, operand)
    requires (operand.DirectoryOperand? && operand.path != "" && !((0 as char) in operand.path) &&
              !W.IsAbsolutePath(operand.path)) ==>
               (operand.parent in after.capabilities <==> operand.parent in before.capabilities)
    requires operand.DirectoryOperand? && operand.parent in before.capabilities ==>
               operand.parent in after.capabilities &&
               after.capabilities[operand.parent].position == before.capabilities[operand.parent].position &&
               after.capabilities[operand.parent].anchorTopology == before.capabilities[operand.parent].anchorTopology
    ensures Operand.AnchorSnapshot(afterFs, after, operand)
  {
    hide *;
    reveal Spec.FrameFields(), Operand.AnchorSnapshot(), C.DirectoryParentAnchorForContextRequestFields();
    if operand.DirectoryOperand? && operand.path != "" && !((0 as char) in operand.path) &&
       !W.IsAbsolutePath(operand.path) {
      if operand.parent in before.capabilities {
        reveal C.DirectoryCapabilityAnchorCurrentFields();
      } else if operand.parent in before.legacyHandles {
        reveal C.DirectoryParentAnchorForRequestFields();
        Identity.PreserveAnchor(beforeFs, afterFs, before.legacyHandles, before.legacyOrigins, operand.parent, operand.path);
      }
    }
  }
  lemma Offset(native: W.CwdContext, offset: nat)
    ensures Spec.FrameFields(native, Operand.AtOffset(native, offset))
  {
    hide *;
    reveal Spec.FrameFields(), Operand.AtOffset(), W.NodeShapeUnchangedExceptMode();
  }

  lemma {:isolate_assertions} Entry(cmd: Schema.ChmodCmd, scope: Descriptor.Scope, display: string,
                                    operand: Operand.Operand, top: bool, fs: W.FileSystem, native: W.CwdContext, cursor: nat,
                                    entry: Descriptor.Entry)
    requires Descriptor.EntryFields(cmd, scope, display, operand, top, fs, native, cursor, entry)
    ensures Spec.FrameFields(native, entry.result.native)
  {
    hide *;
    reveal Descriptor.EntryFields();
    if entry.result.cursor == cursor+entry.rawAttempts {
      assert entry.result.native == Operand.AtOffset(native, entry.rawAttempts);
      Offset(native, entry.rawAttempts);
    } else {
      assert entry.result.native == Operand.AtOffset(native, entry.rawAttempts+1);
      Offset(native, entry.rawAttempts+1);
    }
  }
  lemma Projection(before: W.CwdContext, after: W.CwdContext)
    requires Spec.FrameFields(before, after)
    ensures after.position == before.position && after.hint == before.hint
    ensures after.legacyHandles == before.legacyHandles && after.legacyOrigins == before.legacyOrigins
    ensures after.topology.objects.Keys == before.topology.objects.Keys
    ensures before.topology.nodes.Keys <= after.topology.nodes.Keys
  {
    hide *;
    reveal Spec.FrameFields(), W.NodeShapeUnchangedExceptMode();
  }
}
