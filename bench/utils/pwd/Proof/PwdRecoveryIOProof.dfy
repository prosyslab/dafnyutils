include "PwdDirectoryModelProof.dfy"
include "../../../core/IO.dfy"

module PwdRecoveryIOProof {
  import DirectoryModelProof = PwdDirectoryModelProof
  import opened BenchWorld
  import C = IOContract

  lemma ResponseErrnos(request: DirectoryRequest, response: DirectoryResponse)
    requires C.DirectoryResponseFields(request,response)
    ensures response.err >= 0
    ensures C.ResultErrno(C.DirectoryPathResultFields(response)) == response.err
    ensures C.ResultErrno(C.DirectoryStatusResultFields(response)) == response.err
    ensures C.ResultErrno(C.DirectoryHandleResultFields(response)) == response.err
    ensures C.ResultErrno(C.DirectoryDescriptorResultFields(response)) == response.err
    ensures C.ResultErrno(C.DirectoryReadResultFields(response)) == response.err
    ensures C.ResultErrno(C.DirectoryUnitResultFields(response)) == response.err
  {
    hide *;
    reveal C.DirectoryResponseFields(), C.ResultErrno(), C.IOErrorErrno();
    reveal C.DirectoryPathResultFields(), C.DirectoryStatusResultFields();
    reveal C.DirectoryHandleResultFields(), C.DirectoryDescriptorResultFields();
    reveal C.DirectoryReadResultFields(), C.DirectoryUnitResultFields();
  }

  lemma ReadName(request: DirectoryRequest, response: DirectoryResponse)
    requires C.DirectoryResponseFields(request,response)
    requires request.operation == DirectoryReadNext
    requires request.handle in request.capabilities
    requires !request.capabilities[request.handle].includeDots
    ensures response.err == 0 && response.read.DirectoryItem? ==>
              InodeChildNameValid(response.read.name)
  {
    hide *;
    reveal C.DirectoryResponseFields(), C.DirectoryRequestFields();
    reveal C.LiveDirectoryCapabilitiesFields(), C.LiveDirectoryTopologyFields();
    reveal C.DirectoryOperationCapabilitiesCurrentFields(), C.DirectoryCapabilityReadCurrentFields();
    reveal C.DirectoryCapabilityAnchorCurrentFields(), C.DirectoryCapabilityNamesFields();
    if response.err == 0 && response.read.DirectoryItem? {
      var capability := request.capabilities[request.handle];
      assert response.read.name in capability.remaining;
      assert response.read.name in request.topology.nodes[capability.position].entries;
    }
  }

  lemma StatusKind(request: DirectoryRequest, response: DirectoryResponse)
    requires C.DirectoryResponseFields(request,response)
    requires request.operation == DirectoryCurrentStatus || request.operation == DirectoryFstat
    ensures response.err == 0 ==> response.status.kind == DirectoryKind
  {
    hide *;
    reveal C.DirectoryResponseFields(), C.DirectoryRequestFields();
    reveal C.LiveDirectoryCapabilitiesFields(), C.LiveDirectoryTopologyFields();
    reveal C.DirectoryStatusSameStructure();
    if response.err == 0 && request.operation == DirectoryFstat {
      var handle :| handle in request.capabilities &&
                    request.capabilities[handle].descriptor == [request.fd] &&
                    C.DirectoryStatusSameStructure(
                      request.topology.nodes[request.capabilities[handle].position].status,response.status);
    }
  }

  lemma OperationCapabilities(request: DirectoryRequest, observations: DirectoryObservations,
                              response: DirectoryResponse, position: DirectoryPosition,
                              capabilities: map<int,DirectoryCapabilityState>, ordinal: nat,
                              statusOrdinal: nat, cwdHint: Path)
    requires C.DirectoryOperationSpec(request,observations,response,position,
                                      capabilities,ordinal,statusOrdinal,cwdHint)
    ensures (request.operation != DirectoryOpenParent && request.operation != DirectoryGetDescriptor &&
             request.operation != DirectoryReadNext && request.operation != DirectoryClose) ==>
              capabilities == request.capabilities
    ensures request.operation == DirectoryOpenParent && response.err == 0 ==>
              response.handle in capabilities && capabilities[response.handle].anchorFs == request.fs &&
              !capabilities[response.handle].includeDots &&
              C.DirectoryCapabilityReadCurrentFields(request.topology,capabilities[response.handle])
    ensures request.operation == DirectoryGetDescriptor && response.err == 0 ==>
              request.handle in capabilities && capabilities[request.handle].descriptor == [response.fd] && response.fd >= 0
    ensures request.operation == DirectoryReadNext && request.handle in request.capabilities ==>
              request.handle in capabilities &&
              capabilities[request.handle].anchorFs == request.capabilities[request.handle].anchorFs &&
              capabilities[request.handle].includeDots == request.capabilities[request.handle].includeDots &&
              C.DirectoryCapabilityReadCurrentFields(request.topology,capabilities[request.handle])
    ensures request.operation == DirectoryClose ==> request.handle !in capabilities
    ensures (request.operation == DirectoryGetDescriptor && request.handle in request.capabilities &&
             C.DirectoryCapabilityReadCurrentFields(request.topology,request.capabilities[request.handle])) ==>
              request.handle in capabilities &&
              capabilities[request.handle].anchorFs == request.capabilities[request.handle].anchorFs &&
              capabilities[request.handle].includeDots == request.capabilities[request.handle].includeDots &&
              C.DirectoryCapabilityReadCurrentFields(request.topology,capabilities[request.handle]) &&
              (response.err == 0 ==>
                 C.DirectoryOperationCapabilitiesCurrentFields(request.topology,capabilities,DirectoryFchdir,0,response.fd) &&
                 C.DirectoryOperationCapabilitiesCurrentFields(request.topology,capabilities,DirectoryFstat,0,response.fd))
  {
    hide *;
    reveal C.DirectoryOperationSpec(), C.DirectoryResponseFields(), C.DirectoryRequestFields();
    reveal C.DirectoryNextCapabilitiesFields();
    reveal C.DirectoryCapabilityReadCurrentFields(), C.DirectoryCapabilityAnchorCurrentFields();
    reveal C.DirectoryCapabilityNamesFields(), C.DirectoryOperationCapabilitiesCurrentFields();
    if request.operation == DirectoryOpenParent && response.err == 0 {
      assert request.topology.nodes[request.position].parent in request.topology.nodes by {
        reveal C.LiveDirectoryTopologyFields();
      }
    }
  }

  lemma PathIsAbsolute(request: DirectoryRequest, response: DirectoryResponse)
    requires C.DirectoryResponseFields(request,response)
    requires request.operation == DirectoryGetCwd
    ensures response.err == 0 ==> IsAbsolutePath(response.path)
  {
    hide *;
    reveal C.DirectoryResponseFields(), C.DirectoryRequestFields();
    reveal C.LiveDirectoryTopologyFields();
    if response.err == 0 {
      assert request.topology.nodes[request.position].pathname == [response.path];
    }
  }

  lemma RootStatusKind(observations: StatusTimeObservations,
                       failures: (NativeFailureRequest)->int, beforeCursor: nat, afterCursor: nat,
                       fs: FileSystem, result: IOResult<FileStatus>)
    requires C.GetFileStatusSpec(observations,failures,beforeCursor,afterCursor,fs,"/",false,
                                 result.Ok?,C.ResultValue(result,DEFAULT_FILE_STATUS),C.ResultErrno(result))
    ensures C.ResultErrno(result) >= 0
    ensures result.Err? ==> C.ResultErrno(result) > 0
    ensures result.Ok? ==> result.v.kind == DirectoryKind
  {
    hide *;
    reveal C.GetFileStatusSpec(), C.FileStatusStructureContractFields(), C.ResultValue();
    DirectoryModelProof.RootDirectorySnapshotFields(fs);
  }
}
