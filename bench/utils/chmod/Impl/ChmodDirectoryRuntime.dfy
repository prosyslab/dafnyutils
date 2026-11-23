include "ChmodEntryRuntime.dfy"
include "../Proof/ChmodTraversalProof.dfy"

module ChmodDirectoryRuntime {
  import W = BenchWorld
  import BenchIO
  import C = IOContract
  import Entry = ChmodEntryRuntime
  import Spec = ChmodDescriptorSpec
  import Frame = ChmodTraversalProof
  import FrameSpec = ChmodTraversalSpec

  lemma {:isolate_assertions} ReadShape(fs: W.FileSystem, before: W.CwdContext,
                                        observations: W.DirectoryObservations, handle: int, cursor: nat,
                                        response: W.DirectoryResponse, after: W.CwdContext)
    requires C.CwdContextFields(fs, before)
    requires handle in before.capabilities && !before.capabilities[handle].includeDots
    requires C.DirectoryCapabilityReadCurrentFields(before.topology, before.capabilities[handle])
    requires C.ContextOperationSpec(fs, before, observations, W.DirectoryReadNext, handle, 0, "",
                                    cursor, cursor, response, after)
    ensures after.capabilities.Keys == before.capabilities.Keys
    ensures after.capabilities[handle].position == before.capabilities[handle].position &&
            after.capabilities[handle].anchorTopology == before.capabilities[handle].anchorTopology &&
            after.capabilities[handle].anchorFs == before.capabilities[handle].anchorFs &&
            after.capabilities[handle].descriptor == before.capabilities[handle].descriptor &&
            !after.capabilities[handle].includeDots
    ensures after.capabilities[handle].remaining <= before.capabilities[handle].remaining
    ensures forall other | other in before.capabilities && other != handle ::
              after.capabilities[other] == before.capabilities[other]
    ensures C.DirectoryCapabilityReadCurrentFields(after.topology, after.capabilities[handle])
    ensures response.err == 0 && response.read.DirectoryItem? ==>
              response.read.name in before.capabilities[handle].remaining &&
              after.capabilities[handle].remaining == before.capabilities[handle].remaining-{response.read.name} &&
              |after.capabilities[handle].remaining| < |before.capabilities[handle].remaining| &&
              W.InodeChildNameValid(response.read.name)
  {
    hide *;
    reveal C.ContextOperationSpec(), C.DirectoryRequestForContextFields(), C.DirectoryOperationSpec(),
           C.DirectoryNextCapabilitiesFields(), C.DirectoryResponseFields(),
           C.CwdContextFields(), C.LiveDirectoryTopologyFields(),
           C.DirectoryCapabilityReadCurrentFields(), C.DirectoryCapabilityAnchorCurrentFields();
    if response.err == 0 && response.read.DirectoryItem? {
      assert response.read.name != "." && response.read.name != "..";
    }
  }

  lemma CloseShape(fs: W.FileSystem, before: W.CwdContext,
                   observations: W.DirectoryObservations, handle: int, cursor: nat,
                   response: W.DirectoryResponse, after: W.CwdContext)
    requires C.ContextOperationSpec(fs, before, observations, W.DirectoryClose, handle, 0, "",
                                    cursor, cursor, response, after)
    ensures after.capabilities == before.capabilities-{handle}
  {
    hide *;
    reveal C.ContextOperationSpec(), C.DirectoryRequestForContextFields(), C.DirectoryOperationSpec();
    reveal C.DirectoryNextCapabilitiesFields();
  }

  method {:isolate_assertions} Read(scope: Spec.Scope, handle: int, io: BenchIO.IO)
    returns (result: W.IOResult<W.DirectoryRead>, ghost read: Spec.DirectoryRead)
    requires Entry.ScopeFields(io, scope)
    requires handle in io.cwdContext().capabilities && !io.cwdContext().capabilities[handle].includeDots
    requires C.DirectoryCapabilityReadCurrentFields(io.cwdContext().topology, io.cwdContext().capabilities[handle])
    modifies io.directoryStateRegion
    ensures Entry.ScopeFields(io, scope)
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures io.directoryObservations() == old(io.directoryObservations())
    ensures FrameSpec.FrameFields(old(io.cwdContext()), io.cwdContext())
    ensures read.before == old(io.cwdContext()) && read.after == io.cwdContext()
    ensures Spec.ReadFields(scope, old(io.fs()), old(io.statusCursor()), handle, read)
    ensures result == C.DirectoryReadResultFields(read.response)
    ensures result.Ok? <==> C.ResultErrno(result) == 0
    ensures C.ResultErrno(result) == read.response.err
    ensures result.Ok? ==> result.v == read.response.read
    ensures io.cwdContext().capabilities.Keys == old(io.cwdContext()).capabilities.Keys
    ensures io.cwdContext().capabilities[handle].position == old(io.cwdContext()).capabilities[handle].position &&
            io.cwdContext().capabilities[handle].anchorTopology == old(io.cwdContext()).capabilities[handle].anchorTopology &&
            io.cwdContext().capabilities[handle].anchorFs == old(io.cwdContext()).capabilities[handle].anchorFs &&
            io.cwdContext().capabilities[handle].descriptor == old(io.cwdContext()).capabilities[handle].descriptor &&
            !io.cwdContext().capabilities[handle].includeDots
    ensures io.cwdContext().capabilities[handle].remaining <= old(io.cwdContext()).capabilities[handle].remaining
    ensures forall other | other in old(io.cwdContext()).capabilities && other != handle ::
              io.cwdContext().capabilities[other] == old(io.cwdContext()).capabilities[other]
    ensures C.DirectoryCapabilityReadCurrentFields(io.cwdContext().topology, io.cwdContext().capabilities[handle])
    ensures result.Ok? && result.v.DirectoryItem? ==>
              result.v.name in old(io.cwdContext()).capabilities[handle].remaining &&
              io.cwdContext().capabilities[handle].remaining == old(io.cwdContext()).capabilities[handle].remaining-{result.v.name} &&
              |io.cwdContext().capabilities[handle].remaining| < |old(io.cwdContext()).capabilities[handle].remaining| &&
              W.InodeChildNameValid(result.v.name)
  {
    hide *;
    ghost var fs0 := io.fs();
    ghost var native0 := io.cwdContext();
    ghost var cursor0 := io.statusCursor();
    ghost var observations := io.directoryObservations();
    ghost var state0 := io.directoryState();
    assert observations == scope.directories by { reveal Entry.ScopeFields(); }
    assert C.DirectoryOperationCapabilitiesCurrentFields(io.directoryTopology(), io.directoryCapabilities(),
                                                         W.DirectoryReadNext, handle, 0) by { reveal C.DirectoryOperationCapabilitiesCurrentFields(); }
    result := io.ReadDirectoryCapability(handle);
    ghost var request := C.DirectoryRequestForContextFields(fs0, native0, W.DirectoryReadNext, handle, 0, "", cursor0);
    ghost var response := observations(request);
    assert result == C.DirectoryReadResultFields(response) by { reveal C.DirectoryRequestForContextFields(); }
    read := Spec.DirectoryRead(native0, io.cwdContext(), response);
    assert Spec.ReadFields(scope, fs0, cursor0, handle, read) by { reveal Spec.ReadFields(); }
    ReadShape(fs0, native0, observations, handle, cursor0, response, io.cwdContext());
    Frame.DirectoryOperation(fs0, native0, observations, W.DirectoryReadNext, handle, cursor0, response, io.cwdContext());
    assert C.ResultErrno(result) == response.err && (result.Ok? ==> result.v == response.read) by {
      reveal C.DirectoryReadResultFields(), C.ResultErrno(), C.IOErrorErrno();
    }
    ghost var state1 := io.directoryState();
    assert state1.model == state0.model;
    assert io.directoryObservations() == observations;
    assert Entry.ScopeFields(io, scope) by { reveal Entry.ScopeFields(); }
  }

  method {:isolate_assertions} Close(scope: Spec.Scope, handle: int, io: BenchIO.IO)
    returns (result: W.IOResult<W.Unit>, ghost response: W.DirectoryResponse)
    requires Entry.ScopeFields(io, scope)
    requires handle in io.cwdContext().capabilities
    modifies io.directoryStateRegion
    ensures Entry.ScopeFields(io, scope)
    ensures io.dirHandles() == old(io.dirHandles()) && io.directoryOrigins() == old(io.directoryOrigins())
    ensures io.directoryObservations() == old(io.directoryObservations())
    ensures FrameSpec.FrameFields(old(io.cwdContext()), io.cwdContext())
    ensures C.ContextOperationSpec(old(io.fs()), old(io.cwdContext()), scope.directories,
                                   W.DirectoryClose, handle, 0, "", old(io.statusCursor()), io.statusCursor(), response, io.cwdContext())
    ensures result == C.DirectoryUnitResultFields(response)
    ensures result.Ok? <==> C.ResultErrno(result) == 0
    ensures C.ResultErrno(result) == response.err
    ensures io.cwdContext().capabilities == old(io.cwdContext()).capabilities-{handle}
  {
    hide *;
    ghost var fs0 := io.fs();
    ghost var native0 := io.cwdContext();
    ghost var cursor0 := io.statusCursor();
    ghost var observations := io.directoryObservations();
    ghost var state0 := io.directoryState();
    assert observations == scope.directories by { reveal Entry.ScopeFields(); }
    result := io.CloseDirectoryCapability(handle);
    ghost var request := C.DirectoryRequestForContextFields(fs0, native0, W.DirectoryClose, handle, 0, "", cursor0);
    response := observations(request);
    assert result == C.DirectoryUnitResultFields(response) by { reveal C.DirectoryRequestForContextFields(); }
    CloseShape(fs0, native0, observations, handle, cursor0, response, io.cwdContext());
    Frame.DirectoryOperation(fs0, native0, observations, W.DirectoryClose, handle, cursor0, response, io.cwdContext());
    assert C.ResultErrno(result) == response.err by {
      reveal C.DirectoryUnitResultFields(), C.ResultErrno(), C.IOErrorErrno();
    }
    ghost var state1 := io.directoryState();
    assert state1.model == state0.model;
    assert io.directoryObservations() == observations;
    assert Entry.ScopeFields(io, scope) by { reveal Entry.ScopeFields(); }
  }
}
