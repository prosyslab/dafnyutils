include "../Spec/LsNativeSpec.dfy"

module LsNativeResourceProof {
  import W = BenchWorld
  import C = IOContract
  import Spec = LsNativeSpec

  lemma OpenFrame(inputs: Spec.Inputs, call: Spec.Call)
    requires Spec.CallFields(inputs,call) && call.action.OpenAction?
    ensures C.Extends(call.before.context.topology,call.after.context.topology)
    ensures call.after.context.position == call.before.context.position
    ensures call.after.context.hint == call.before.context.hint
    ensures call.after.context.legacyHandles == call.before.context.legacyHandles
    ensures call.after.context.legacyOrigins == call.before.context.legacyOrigins
    ensures call.action.openResult.Ok? ==>
              call.action.openResult.v in call.after.context.capabilities &&
              call.action.openResult.v !in call.before.context.capabilities &&
              call.action.openResult.v !in call.before.context.legacyHandles &&
              call.after.context.capabilities[call.action.openResult.v].anchorFs == inputs.fs &&
              call.after.context.capabilities[call.action.openResult.v].anchorTopology == call.after.context.topology &&
              call.after.context.capabilities[call.action.openResult.v].includeDots == call.action.dots &&
              C.DirectoryCapabilityReadCurrentFields(call.after.context.topology,
                                                     call.after.context.capabilities[call.action.openResult.v])
    ensures call.action.openResult.Err? ==>
              call.after.context.capabilities == call.before.context.capabilities
  {
    hide *;
    reveal Spec.CallFields(), C.OpenDirAtCwdSpec();
    reveal C.OpenDirFromCwdTargetContractFields(), C.CwdContextReadStepFields();
    reveal C.ResultValue(), C.ResultErrno(), C.IOErrorErrno();
    reveal C.DirectoryCapabilityReadCurrentFields(), C.DirectoryCapabilityAnchorCurrentFields();
    if call.action.openResult.Err? {
      reveal C.Extends();
    }
  }

  lemma ReadFrame(inputs: Spec.Inputs, call: Spec.Call)
    requires Spec.CallFields(inputs,call) && call.action.ReadAction?
    requires call.action.handle in call.before.context.capabilities
    ensures 0 <= C.ResultErrno(call.action.readResult)
    ensures call.action.readResult.Ok? <==> C.ResultErrno(call.action.readResult) == 0
    ensures call.action.readResult.Ok? && call.action.readResult.v.DirectoryEnd? ==>
              call.before.context.capabilities[call.action.handle].remaining == {}
    ensures call.after.context.topology == call.before.context.topology
    ensures call.after.context.position == call.before.context.position
    ensures call.after.context.hint == call.before.context.hint
    ensures call.after.context.legacyHandles == call.before.context.legacyHandles
    ensures call.after.context.legacyOrigins == call.before.context.legacyOrigins
    ensures call.action.handle in call.after.context.capabilities
    ensures call.after.context.capabilities[call.action.handle].anchorFs ==
            call.before.context.capabilities[call.action.handle].anchorFs
    ensures call.after.context.capabilities[call.action.handle].anchorTopology ==
            call.before.context.capabilities[call.action.handle].anchorTopology
    ensures call.after.context.capabilities[call.action.handle].position ==
            call.before.context.capabilities[call.action.handle].position
    ensures call.after.context.capabilities[call.action.handle].includeDots ==
            call.before.context.capabilities[call.action.handle].includeDots
    ensures call.after.context.capabilities[call.action.handle].remaining <=
            call.before.context.capabilities[call.action.handle].remaining
    ensures call.after.context.capabilities - {call.action.handle} ==
            call.before.context.capabilities - {call.action.handle}
    ensures call.action.readResult.Ok? && call.action.readResult.v.DirectoryItem? ==>
              call.after.context.capabilities[call.action.handle].remaining ==
              call.before.context.capabilities[call.action.handle].remaining - {call.action.readResult.v.name}
    ensures C.DirectoryCapabilityReadCurrentFields(call.after.context.topology,
                                                   call.after.context.capabilities[call.action.handle])
    ensures call.action.readResult.Ok? && call.action.readResult.v.DirectoryEnd? ==>
              call.after.context.capabilities[call.action.handle].remaining == {}
  {
    hide *;
    reveal Spec.CallFields(), C.ContextOperationSpec(), C.DirectoryRequestForContextFields();
    reveal C.DirectoryOperationSpec(), C.DirectoryResponseFields(), C.DirectoryRequestFields();
    reveal C.DirectoryNextPositionFields(), C.DirectoryNextCapabilitiesFields();
    reveal C.DirectoryReadResultFields(), C.ResultErrno(), C.IOErrorErrno();
    reveal C.DirectoryOperationCapabilitiesCurrentFields(), C.DirectoryCapabilityReadCurrentFields();
    reveal C.DirectoryCapabilityAnchorCurrentFields();
  }

  lemma ReadItem(inputs: Spec.Inputs, call: Spec.Call)
    requires Spec.CallFields(inputs,call) && call.action.ReadAction?
    requires call.action.handle in call.before.context.capabilities
    requires call.action.readResult.Ok? && call.action.readResult.v.DirectoryItem?
    ensures var capability := call.before.context.capabilities[call.action.handle];
            var node := call.before.context.topology.nodes[capability.position];
            var entry := call.action.readResult.v;
            entry.name in capability.remaining &&
            if entry.name == "." then
              capability.includeDots && entry.kind == W.DirectoryDirentKind && entry.inode == node.selfRawInode
            else if entry.name == ".." then
              capability.includeDots && entry.kind == W.DirectoryDirentKind && entry.inode == node.parentRawInode
            else W.InodeChildNameValid(entry.name) && entry.name in node.entries &&
                 entry.kind == node.entries[entry.name].kind && entry.inode == node.entries[entry.name].rawInode
  {
    hide *;
    reveal Spec.CallFields(), C.ContextOperationSpec(), C.DirectoryRequestForContextFields();
    reveal C.DirectoryOperationSpec(), C.DirectoryResponseFields(), C.DirectoryRequestFields();
    reveal C.DirectoryReadResultFields();
    ghost var context := call.before.context;
    ghost var capability := context.capabilities[call.action.handle];
    assert capability.position in context.topology.nodes by {
      reveal C.CwdContextFields(), C.LiveDirectoryCapabilitiesFields();
    }
    assert C.LiveDirectoryTopologyFields(inputs.fs,context.topology) by {
      reveal C.CwdContextFields();
    }
    ghost var entry := call.action.readResult.v;
    if entry.name != "." && entry.name != ".." {
      assert entry.name in context.topology.nodes[capability.position].entries;
      assert W.InodeChildNameValid(entry.name) by {
        reveal C.CwdContextFields(), C.LiveDirectoryTopologyFields();
      }
    }
  }

  lemma CloseFrame(inputs: Spec.Inputs, call: Spec.Call)
    requires Spec.CallFields(inputs,call) && call.action.CloseAction?
    ensures call.after.context.topology == call.before.context.topology
    ensures call.after.context.position == call.before.context.position
    ensures call.after.context.hint == call.before.context.hint
    ensures call.after.context.legacyHandles == call.before.context.legacyHandles
    ensures call.after.context.legacyOrigins == call.before.context.legacyOrigins
    ensures call.after.context.capabilities == call.before.context.capabilities - {call.action.handle}
  {
    hide *;
    reveal Spec.CallFields(), C.ContextOperationSpec(), C.DirectoryRequestForContextFields();
    reveal C.DirectoryOperationSpec(), C.DirectoryResponseFields();
    reveal C.DirectoryNextPositionFields(), C.DirectoryNextCapabilitiesFields();
  }
}
