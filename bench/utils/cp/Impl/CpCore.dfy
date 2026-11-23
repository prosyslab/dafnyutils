include "../../../core/Utf8.dfy"
include "../Spec/CpPathSpec.dfy"
include "../Spec/CpSpec.dfy"
include "../Proof/CpPathProof.dfy"
include "CpPathCore.dfy"
include "../Proof/CpPathBridge.dfy"

module CpCore {
  import Text = CpSpec
  import BenchIO
  import BW = BenchWorld
  import C = IOContract
  import S = CpSchema
  import Spec = CpSpec
  import Proof = CpPathProof
  import Paths = CpPathCore
  import PathProof = CpPathBridge
  import PathSpec = CpPathSpec
  import Results
  import CliModel
  import Utf8 = Utf8Semantics

  method Metadata(path: string, follow: bool, io: BenchIO.IO) returns (meta: Spec.Metadata)
    ensures Spec.MetadataFields(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),path,follow,meta)
  {
    hide C.GetFileTimesSpec;
    var result := io.GetFileTimes(path,follow);
    meta := Spec.Metadata(result.Ok?,C.ResultErrno(result),
                          C.ResultValue(result,BW.FileTimeStatus(0,0,0,0,false,false,0,0,0)));
  }

  method Quoted(path: string, io: BenchIO.IO) returns (value: BW.Bytes)
    ensures value == Spec.Q(path)
  { value := io.QuoteafPath(path); }

  method Reason(err: int, io: BenchIO.IO) returns (value: string)
    ensures value == Spec.E(err)
  { value := io.GetCLocaleErrnoText(err); }

  method NameConcat(directory: string, base: string) returns (value: string)
    ensures Spec.NameConcat(directory,base,value)
  {
    var trimmed := Paths.TrimTrailingSlashes(directory);
    Proof.TrimmedSummaryGivesRelation(directory,trimmed);
    value := Spec.JoinTrimmed(trimmed,base);
  }

  method Target(directory: string, source: string) returns (value: string)
    ensures Spec.TargetFields(directory,source,value)
  {
    var base := Paths.ComputeBasenameValue(source);
    PathProof.BasenameValueSummaryGivesRelation(source,base);
    value := NameConcat(directory,if base == ".." then "." else base);
  }

  method ParentsTarget(directory: string, source: string) returns (value: string)
    ensures Spec.ParentsTargetFields(directory,source,value)
  {
    var trimmed := Paths.TrimTrailingSlashes(source);
    Proof.TrimmedSummaryGivesRelation(source,trimmed);
    value := NameConcat(directory,trimmed);
  }

  lemma MetadataIdentityInFilesystem(fs: BW.FileSystem, provider: Spec.FilesystemProvider,
                                     path: string, follow: bool, meta: Spec.Metadata)
    requires Spec.MetadataFields(fs,provider,path,follow,meta)
    requires meta.ok
    ensures Spec.Identity(meta) in Spec.Identities(fs)
  {
    var request := BW.FilesystemQuery(fs,path,follow);
    var observation := provider.filesystem(request);
    var target := C.ResolvePathForMetadataFields(fs,path,follow).v;
    var id := BW.FsIdAt(fs,target);
    assert id in fs.inodes;
    assert Spec.Identity(meta) == (fs.inodes[id].hostKey.device,fs.inodes[id].hostKey.inode);
  }

  method {:isolate_assertions} Enumerate(path: string, io: BenchIO.IO) returns (entries: seq<Spec.DirectoryName>, err: int, wasOpened: bool)
    modifies io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.Enumeration(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),path,entries,err)
    ensures Spec.EnumerationWithOpen(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),path,entries,err,wasOpened)
  {
    reveal Spec.Enumeration(), Spec.EnumerationWithOpen();
    ghost var initial := io.dirHandles();
    var result := io.OpenDir(path,false);
    wasOpened := result.Ok?;
    entries := [];
    err := C.ResultErrno(result);
    ghost var openedHandles := io.dirHandles();
    if result.Err? {
      assert Spec.EnumerationWithOpen(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),path,entries,err,wasOpened) by {
        hide *;
        reveal Spec.EnumerationWithOpen();
      }
      assert Spec.Enumeration(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),path,entries,err) by {
        hide *;
        reveal Spec.Enumeration();
      }
      return;
    }
    var handle := result.v;
    assert C.OpenDirSpec(io.fs(),initial,io.trustedNativeFailures(),openedHandles,path,false,true,handle,0) by {
      hide *;
      reveal C.ResultValue(), C.ResultErrno();
    }
    assert handle !in initial && openedHandles.Keys == initial.Keys + {handle} by {
      hide *;
      reveal C.OpenDirSpec(), C.OpenDirContractFields();
    }
    ghost var states := [io.dirHandles()];
    ghost var kinds: seq<BW.DirectoryEntryKind> := [];
    while true
      invariant handle in io.dirHandles()
      invariant io.dirHandles().Keys == openedHandles.Keys
      invariant forall other | other in initial :: io.dirHandles()[other] == initial[other]
      invariant |states| == |entries| + 1 && |kinds| == |entries|
      invariant states[0] == openedHandles && states[|entries|] == io.dirHandles()
      invariant forall i | 0 <= i < |entries| ::
                  C.ReadDirSpec(io.fs(),states[i],io.trustedNativeFailures(),states[i+1],handle,true,entries[i].name,kinds[i],0) &&
                  C.ReadDirInodeFields(io.fs(),states[i],handle,entries[i].name,true,entries[i].inode)
      decreases |io.dirHandles()[handle].remaining|
    {
      ghost var before := io.dirHandles();
      var item := io.ReadDir(handle);
      if item.Err? || item.v.DirectoryEnd? {
        err := C.ResultErrno(item);
        assert io.dirHandles() == before by {
          hide *;
          reveal C.ReadDirSpec(), C.ReadDirContractFields();
        }
        assert C.ReadDirSpec(io.fs(),states[|entries|],io.trustedNativeFailures(),states[|entries|],handle,false,"",BW.UnknownDirentKind,err);
        break;
      }
      assert C.ReadDirSpec(io.fs(),before,io.trustedNativeFailures(),io.dirHandles(),handle,true,item.v.name,item.v.kind,0) by {
        hide *;
        assert item.Ok? && item.v.DirectoryItem? && C.ResultErrno(item) == 0;
      }
      assert C.ReadDirInodeFields(io.fs(),before,handle,item.v.name,true,item.v.inode);
      ghost var previousEntries, previousKinds, previousStates := entries,kinds,states;
      entries := entries + [Spec.DirectoryName(item.v.name,item.v.inode)];
      kinds := kinds + [item.v.kind];
      states := states + [io.dirHandles()];
      assert forall j | 0 <= j < |entries| ::
          C.ReadDirSpec(io.fs(),states[j],io.trustedNativeFailures(),states[j+1],handle,true,entries[j].name,kinds[j],0) &&
          C.ReadDirInodeFields(io.fs(),states[j],handle,entries[j].name,true,entries[j].inode) by {
        hide *;
        forall j | 0 <= j < |entries|
          ensures C.ReadDirSpec(io.fs(),states[j],io.trustedNativeFailures(),states[j+1],handle,true,entries[j].name,kinds[j],0)
          ensures C.ReadDirInodeFields(io.fs(),states[j],handle,entries[j].name,true,entries[j].inode)
        {
          if j < |previousEntries| {
            assert entries[j] == previousEntries[j] && kinds[j] == previousKinds[j];
            assert states[j] == previousStates[j] && states[j+1] == previousStates[j+1];
          } else {
            assert j == |previousEntries|;
            assert states[j] == before;
          }
        }
      }
    }
    ghost var finalHandles := io.dirHandles();
    assert finalHandles.Keys == openedHandles.Keys;
    assert forall other | other in initial :: finalHandles[other] == initial[other];
    ghost var readErr := err;
    var closeResult := io.CloseDir(handle);
    if err == 0 { err := C.ResultErrno(closeResult); }
    assert io.dirHandles() == initial by {
      hide *;
      reveal C.CloseDirSpec(), C.CloseDirContractFields();
      assert io.dirHandles() == finalHandles - {handle};
      assert io.dirHandles().Keys == initial.Keys;
      forall other | other in initial
        ensures io.dirHandles()[other] == initial[other]
      {
        assert other != handle;
      }
    }
    assert Spec.EnumerationWithOpen(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),path,entries,err,wasOpened) by {
      hide *;
      reveal Spec.EnumerationWithOpen();
    }
    assert Spec.Enumeration(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),path,entries,err) by {
      hide *;
      reveal Spec.Enumeration();
    }

  }

  method InsertEntry(entries: seq<Spec.DirectoryName>, entry: Spec.DirectoryName)
    returns (result: seq<Spec.DirectoryName>)
    requires Spec.SortedEntries(entries)
    ensures Spec.SortedEntries(result)
    ensures multiset(result) == multiset(entries) + multiset{entry}
  {
    var i := 0;
    while i < |entries| && entries[i].inode <= entry.inode
      invariant 0 <= i <= |entries|
      invariant forall j | 0 <= j < i :: entries[j].inode <= entry.inode
      decreases |entries|-i
    { i := i+1; }
    result := entries[..i] + [entry] + entries[i..];
    assert entries == entries[..i] + entries[i..];
    assert multiset([entry]) == multiset{entry};
    forall j,k | 0 <= j < k < |result|
      ensures result[j].inode <= result[k].inode
    {
      if j < i && k < i { assert result[j] == entries[j] && result[k] == entries[k]; }
      else if j < i && k == i { assert result[k] == entry; }
      else if j < i { assert result[j] == entries[j] && result[k] == entries[k-1]; }
      else if j == i { assert result[j] == entry && result[k] == entries[k-1]; }
      else { assert result[j] == entries[j-1] && result[k] == entries[k-1]; }
    }
  }

  method SortEntries(entries: seq<Spec.DirectoryName>) returns (result: seq<Spec.DirectoryName>)
    ensures Spec.SortedEntries(result)
    ensures multiset(result) == multiset(entries)
  {
    result := [];
    var i := 0;
    while i < |entries|
      invariant 0 <= i <= |entries|
      invariant Spec.SortedEntries(result)
      invariant multiset(result) == multiset(entries[..i])
      decreases |entries|-i
    {
      result := InsertEntry(result,entries[i]);
      assert entries[..i+1] == entries[..i] + [entries[i]];
      i := i+1;
    }
    assert entries[..i] == entries;
  }

  lemma LookupBoundaryContains(fs: BW.FileSystem, path: string)
    ensures C.TerminalNoFollowResultFields(fs,path).Ok? ==> BW.FsContainsPath(fs,path)
    ensures C.DirectNoFollowResultFields(fs,path).Ok? ==> BW.FsContainsPath(fs,path)
  {
  }

  lemma FollowedRawResultIsNotSymlink(fs: BW.FileSystem, segments: seq<string>, i: nat,
                                      current: string, seen: set<string>, fuel: nat, directory: bool)
    requires i <= |segments|
    ensures var result := C.ResolveRawSymlinkSegmentsFields(fs,segments,i,current,seen,fuel,true,false,directory);
            result.Ok? ==> !BW.FsNodeAt(fs,result.v).Symlink?
    decreases fuel, |segments|-i
  {
    hide *;
    reveal C.ResolveRawSymlinkSegmentsFields(), C.TerminalNoFollowResultFields(), C.DirectNoFollowResultFields();
    LookupBoundaryContains(fs,current);
    if i == |segments| {
      if C.TerminalNoFollowResultFields(fs,current).Ok? && BW.FsNodeAt(fs,current).Symlink? {
        var target := BW.FsNodeAt(fs,current).target;
        if target != "" && fuel > 0 {
          FollowedRawResultIsNotSymlink(fs,C.RawPathSegmentsFields(target),0,
                                        if BW.IsAbsolutePath(target) then "/" else BW.ParentPath(current),seen + {current},fuel-1,
                                        directory || C.HasTrailingSlash(target));
        }
      }
    } else if BW.FsContainsPath(fs,current) && BW.FsNodeAt(fs,current).Directory? &&
              !BW.FixtureOwnerCanSearch(BW.FsNodeAt(fs,current)) {
    } else if segments[i] == "." || segments[i] == ".." {
      if C.TerminalNoFollowResultFields(fs,current).Ok? {
        if BW.FsNodeAt(fs,current).Directory? {
          FollowedRawResultIsNotSymlink(fs,segments,i+1,
                                        if segments[i] == ".." then BW.ParentPath(current) else current,seen,fuel,directory);
        } else if BW.FsNodeAt(fs,current).Symlink? {
          var target := BW.FsNodeAt(fs,current).target;
          if target != "" && fuel > 0 {
            FollowedRawResultIsNotSymlink(fs,C.RawPathSegmentsFields(target)+segments[i..],0,
                                          if BW.IsAbsolutePath(target) then "/" else BW.ParentPath(current),seen + {current},fuel-1,directory);
          }
        }
      }
    } else {
      var next := BW.AppendPath(current,segments[i]);
      LookupBoundaryContains(fs,next);
      if C.DirectNoFollowResultFields(fs,next).Ok? {
        if BW.FsNodeAt(fs,next).Directory? {
          FollowedRawResultIsNotSymlink(fs,segments,i+1,next,seen,fuel,directory);
        } else if BW.FsNodeAt(fs,next).Symlink? {
          var target := BW.FsNodeAt(fs,next).target;
          if target != "" && fuel > 0 {
            var remaining := segments[i+1..];
            FollowedRawResultIsNotSymlink(fs,C.RawPathSegmentsFields(target)+remaining,0,
                                          if BW.IsAbsolutePath(target) then "/" else BW.ParentPath(next),seen + {next},fuel-1,
                                          directory || (|remaining| == 0 && C.HasTrailingSlash(target)));
          }
        }
      }
    }
  }

  lemma FollowedMetadataIsNotSymlink(fs: BW.FileSystem, path: string)
    ensures var result := C.ResolvePathForMetadataFields(fs,path,true);
            result.Ok? ==> !BW.FsNodeAt(fs,result.v).Symlink?
  {
    FollowedRawResultIsNotSymlink(fs,C.RawPathSegmentsFields(path),0,
                                  if BW.IsAbsolutePath(path) then "/" else "",{},BW.SYMLINK_MAX_DEPTH,C.HasTrailingSlash(path));
  }

  method {:isolate_assertions} Discover(raw: S.CpCmdRaw, path: string, ancestors: set<(int,int)>, parentDevice: int, io: BenchIO.IO)
    returns (tree: Spec.SourceTree)
    modifies io.dirHandlesRegion
    ensures tree.path == path
    ensures Spec.SourceTreeFields(raw,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),ancestors,parentDevice,tree)
    ensures io.dirHandles() == old(io.dirHandles())
    decreases Spec.Identities(io.fs()) - ancestors
  {
    reveal Spec.SourceTreeFields();
    var meta := Metadata(path,raw.policy.dereference,io);
    if !meta.ok { return Spec.MissingSource(path,meta); }
    if meta.value.isDir && !raw.policy.recursive { return Spec.OmittedSource(path,meta); }
    if meta.value.isDir && Spec.Identity(meta) in ancestors { return Spec.CyclicSource(path,meta); }
    var modeResult := io.GetFileMode(path,raw.policy.dereference);
    if modeResult.Err? {
      return Spec.ModeFailureSource(path,meta,C.ResultErrno(modeResult));
    }
    var mode := modeResult.v;
    assert C.GetFileModeSpec(io.fs(),io.trustedNativeFailures(),path,raw.policy.dereference,true,mode,0);
    if !meta.value.isDir {
      var linkTarget := path;
      if meta.value.isSymlink && !raw.policy.hard && !raw.policy.symbolic {
        if raw.policy.dereference { FollowedMetadataIsNotSymlink(io.fs(),path); }
        assert !raw.policy.dereference;
        assert C.ResolvePathForMetadataFields(io.fs(),path,false).Ok?;
        assert BW.FsNodeAt(io.fs(),C.ResolvePathForMetadataFields(io.fs(),path,false).v).Symlink?;
        var link := io.ReadLink(path);
        if link.Err? {
          return Spec.LinkFailureSource(path,meta,mode,link.e);
        }
        linkTarget := link.v;
      }
      assert Spec.SourceTreeFields(raw,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),ancestors,parentDevice,
                                   Spec.FileSource(path,meta,mode,linkTarget)) by {
        hide *;
        reveal Spec.SourceTreeFields();
      }
      return Spec.FileSource(path,meta,mode,linkTarget);
    }
    if raw.policy.oneFileSystem && |ancestors| != 0 && meta.value.device != parentDevice {
      return Spec.DirectorySource(path,meta,mode,[],0);
    }
    MetadataIdentityInFilesystem(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),path,raw.policy.dereference,meta);
    var nativeEntries, err, wasOpened := Enumerate(path,io);
    var entries: seq<Spec.DirectoryName> := [];
    if err == 0 { entries := SortEntries(nativeEntries); }
    reveal Spec.OrderedEnumeration();
    assert Spec.OrderedEnumeration(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),path,entries,err);
    var children: seq<Spec.SourceTree> := [];
    var i := 0;
    while i < |entries|
      invariant 0 <= i <= |entries|
      invariant |children| == i
      invariant (forall j | 0 <= j < i ::
                   Spec.NameConcat(path,entries[j].name,children[j].path) &&
                   Spec.SourceTreeFields(S.ChildCommand(raw),io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),ancestors + {Spec.Identity(meta)},meta.value.device,children[j]))
      invariant io.dirHandles() == old(io.dirHandles())
      decreases |entries| - i
    {
      var childPath := NameConcat(path,entries[i].name);
      var child := Discover(S.ChildCommand(raw),childPath,ancestors + {Spec.Identity(meta)},meta.value.device,io);
      ghost var previousChildren := children;
      children := children + [child];
      assert forall j | 0 <= j < |children| ::
          Spec.NameConcat(path,entries[j].name,children[j].path) &&
          Spec.SourceTreeFields(S.ChildCommand(raw),io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),ancestors + {Spec.Identity(meta)},meta.value.device,children[j]) by {
        hide *;
        forall j | 0 <= j < |children|
          ensures Spec.NameConcat(path,entries[j].name,children[j].path)
          ensures Spec.SourceTreeFields(S.ChildCommand(raw),io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),ancestors + {Spec.Identity(meta)},meta.value.device,children[j])
        {
          if j < i {
            assert children[j] == previousChildren[j];
          } else {
            assert j == i && children[j] == child;
          }
        }
      }
      i := i + 1;
    }
    tree := Spec.DirectorySource(path,meta,mode,children,err);
    assert Spec.SourceTreeFields(raw,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),ancestors,parentDevice,tree) by {
      hide *;
      reveal Spec.SourceTreeFields();
    }
  }

  method Attributes(raw: S.CpCmdRaw, meta: Spec.Metadata, mode: bv32, target: string, follow: bool,
                    io: BenchIO.IO) returns (err: BW.Bytes, ok: bool)
    modifies io.fsRegion
    ensures Spec.Attributes(raw,meta,mode,target,follow,old(io.fs()),io.fs(),io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),err,ok)
  {
    hide *;
    reveal Spec.Attributes();
    ghost var before := io.fs();
    ghost var now := io.now();
    ghost var provider := Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures());
    err, ok := [], true;
    var timeOK, timeErr := true, 0;
    if raw.policy.preserveTimes {
      var result := io.SetFileTimes(target,follow,meta.value.atimeSec,meta.value.atimeNsec,
                                    meta.value.mtimeSec,meta.value.mtimeNsec);
      assert C.SetFileTimesSpec(before,now,provider.filesystem,io.fs(),target,follow,
                                meta.value.atimeSec,meta.value.atimeNsec,meta.value.mtimeSec,meta.value.mtimeNsec,result.Ok?,C.ResultErrno(result));
      timeOK, timeErr := result.Ok?, C.ResultErrno(result);
      if !timeOK {
        var q := Quoted(target,io);
        var reason := Reason(timeErr,io);
        err := Text.TimeError(q,reason);
        ok := false;
      }
    }
    ghost var middle := io.fs();
    assert (if raw.policy.preserveTimes then
              C.SetFileTimesSpec(before,now,provider.filesystem,middle,target,follow,
                                 meta.value.atimeSec,meta.value.atimeNsec,meta.value.mtimeSec,meta.value.mtimeNsec,timeOK,timeErr)
            else middle == before && timeOK && timeErr == 0);
    var modeOK, modeErr := true, 0;
    if raw.policy.preserveMode && follow {
      var result := io.SetFileMode(target,follow,mode);
      modeOK, modeErr := result.Ok?,C.ResultErrno(result);
      if !modeOK {
        var q := Quoted(target,io);
        var reason := Reason(modeErr,io);
        err := err + Text.ModeError(q,reason);
        ok := false;
      }
    }
    assert (if raw.policy.preserveTimes then
              C.SetFileTimesSpec(before,now,provider.filesystem,middle,target,follow,
                                 meta.value.atimeSec,meta.value.atimeNsec,meta.value.mtimeSec,meta.value.mtimeNsec,timeOK,timeErr)
            else middle == before && timeOK && timeErr == 0);
    assert (if raw.policy.preserveMode && follow then
              C.SetFileModeSpec(middle,io.now(),io.trustedNativeFailures(),io.fs(),target,follow,mode,modeOK,modeErr)
            else io.fs() == middle && modeOK && modeErr == 0);
    assert err == (if timeOK then [] else Spec.TimeError(Spec.Q(target),Spec.E(timeErr))) +
                  (if modeOK then [] else Spec.ModeError(Spec.Q(target),Spec.E(modeErr)));
    assert ok == (timeOK && modeOK);
    reveal Spec.AttributeOutcome();
    assert Spec.AttributeOutcome(raw,meta,mode,target,follow,before,io.fs(),io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),err,ok,
                                 (middle,(timeOK,timeErr),(modeOK,modeErr)));

  }

  method {:isolate_assertions} WritePayload(raw: S.CpCmdRaw, target: string, data: BW.Bytes, mode: bv32, io: BenchIO.IO)
    returns (result: BW.IOResult<BW.WriteReceipt>, removeFailed: bool, didRemove: bool)
    modifies io.fsRegion
    ensures Spec.PayloadWrite(raw,old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),
                              Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),target,data,mode,result.Ok?,C.ResultErrno(result),C.WriteResultCommitted(result),C.WriteResultStage(result),removeFailed,didRemove)
  {
    hide *;
    reveal Spec.PayloadWrite();
    reveal C.IOErrorErrno(), C.ResultErrno(), C.WriteResultCommitted(), C.WriteResultStage(), C.ReadResultData(), C.ReadResultStage();
    ghost var before := io.fs();
    var targetMeta := Metadata(target,true,io);
    if raw.policy.attributesOnly && targetMeta.ok { result := io.AppendFile(target,[]); }
    else { result := io.WriteFile(target,data,Spec.CreationMode(raw,mode)); }
    ghost var first := io.fs();
    ghost var firstResult := result;
    removeFailed,didRemove := false,false;
    if raw.policy.force && targetMeta.ok && C.WriteResultStage(result) == BW.WriteOpenFailed {
      var removed := io.UnlinkPath(target);
      ghost var removedFs := io.fs();
      if removed.Err? {
        removeFailed := true;
        result := Results.Err(BW.WriteFailure(C.ResultErrno(removed),"",0,BW.WriteOpenFailed));
      } else {
        didRemove := true;
        result := io.WriteFile(target,data,Spec.CreationMode(raw,mode));
      }
    }
    reveal Spec.PayloadOutcome();
    assert Spec.PayloadOutcome(raw,before,io.fs(),io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),
                               target,data,mode,result.Ok?,C.ResultErrno(result),C.WriteResultCommitted(result),C.WriteResultStage(result),(removeFailed,didRemove),
                               (first,firstResult.Ok?,C.ResultErrno(firstResult),C.WriteResultCommitted(firstResult),C.WriteResultStage(firstResult),targetMeta));
  }

  method CopyData(raw: S.CpCmdRaw, source: string, target: string,
                  meta: Spec.Metadata, mode: bv32, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool)
    modifies io.fsRegion
    ensures Spec.DataCopy(raw,source,target,meta,mode,old(io.fs()),io.fs(),io.props(),io.now(),
                          io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok)
  {
    hide *;
    reveal Spec.DataCopy(), Spec.DataOutcome();
    reveal C.IOErrorErrno(), C.ResultErrno(), C.WriteResultCommitted(), C.WriteResultStage(), C.ReadResultData(), C.ReadResultStage();
    ghost var before := io.fs();
    var read: BW.IOResult<BW.Bytes>;
    if raw.policy.attributesOnly { read := io.ProbeReadFile(source); }
    else { read := io.ReadFile(source); }
    var data, readErr, readStage := C.ReadResultData(read), C.ResultErrno(read), C.ReadResultStage(read);
    var qs := Quoted(source,io);
    var qt := Quoted(target,io);
    out := [];
    if readStage == BW.OpenFailed {
      var reason := Reason(readErr,io);
      assert Spec.DataOutcome(raw,source,target,meta,mode,before,io.fs(),io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                              [],Spec.CannotOpen(qs,reason),false,(data,readErr,readStage,meta,meta,(before,true,0,0,BW.WriteSucceeded,false,[],true,meta,false)));
      return [],Text.CannotOpen(qs,reason),false;
    }
    var targetMetadata := Metadata(target,true,io);
    var entryMetadata := Metadata(target,false,io);
    if !targetMetadata.ok && entryMetadata.ok && entryMetadata.value.isSymlink && !raw.policy.creation.writeDangling {
      assert Spec.DataOutcome(raw,source,target,meta,mode,before,io.fs(),io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                              [],Spec.Dangling(qt),false,(data,readErr,readStage,targetMetadata,entryMetadata,(before,true,0,0,BW.WriteSucceeded,false,[],true,meta,false)));
      return [],Spec.Dangling(qt),false;
    }
    var write: BW.IOResult<BW.WriteReceipt>;
    ghost var attributeTargetMetadata := meta;
    var removeFailed,didRemove := false,false;
    if raw.policy.attributesOnly {
      var targetMeta := Metadata(target,true,io);
      attributeTargetMetadata := targetMeta;
      write,removeFailed,didRemove := WritePayload(raw,target,[],mode,io);
    } else { write,removeFailed,didRemove := WritePayload(raw,target,data,mode,io); }
    ghost var written := io.fs();
    var attributesErr: BW.Bytes := [];
    var attributesOK := true;
    if (write.Ok? || C.WriteResultStage(write) == BW.WriteCloseFailed) && (readErr == 0 || readStage == BW.CloseFailed) {
      attributesErr, attributesOK := Attributes(raw,meta,mode,target,true,io);
    }
    out := if raw.policy.verbose && didRemove then Spec.Removed(qt) else [];
    err := attributesErr;
    if write.Err? {
      var reason := Reason(C.ResultErrno(write),io);
      err := err + (if removeFailed then Text.CannotRemove(qt,reason)
                    else if C.WriteResultStage(write) == BW.WriteOpenFailed then Text.CannotCreate(qt,reason)
                    else if C.WriteResultStage(write) == BW.WriteCloseFailed then Text.CloseError(qt,reason)
                    else Text.WriteError(qt,reason));
    }
    if readErr != 0 && C.WriteResultStage(write) != BW.WriteOpenFailed && C.WriteResultStage(write) != BW.WriteFailed {
      var reason := Reason(readErr,io);
      err := err + (if readStage == BW.CloseFailed then Text.CloseError(qs,reason) else Text.ReadError(qs,reason));
    }
    ok := write.Ok? && readErr == 0 && attributesOK;
    assert Spec.DataOutcome(raw,source,target,meta,mode,before,io.fs(),io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok,
                            (data,readErr,readStage,targetMetadata,entryMetadata,
                             (written,write.Ok?,C.ResultErrno(write),C.WriteResultCommitted(write),C.WriteResultStage(write),removeFailed,attributesErr,attributesOK,attributeTargetMetadata,didRemove)));
  }

  method {:isolate_assertions} RelativeLinkAllowed(source: string, target: string, io: BenchIO.IO) returns (allowed: bool)
    ensures Spec.RelativeLinkAllowed(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),source,target,allowed)
  {
    hide *;
    reveal Spec.RelativeLinkAllowed();
    if |source| > 0 && source[0] == '/' { return true; }
    var parent := Paths.ComputeDirnameValue(target);
    PathProof.DirnameValueSummaryGivesRelation(target,parent);
    if parent == "." { return true; }
    var dot := Metadata(".",true,io);
    var destination := Metadata(parent,true,io);
    allowed := !dot.ok || !destination.ok || Spec.Identity(dot) == Spec.Identity(destination);
  }

  method RecordDestination(target: string, io: BenchIO.IO) returns (record: Spec.DestinationRecord)
    ensures Spec.DestinationRecordFields(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),target,record)
  {
    reveal Spec.DestinationRecordFields();
    var metadata := Metadata(target,false,io);
    record := if metadata.ok then Spec.RecordedDestination(metadata) else Spec.NoDestinationRecord;
  }

  method CopyLeaf(raw: S.CpCmdRaw, source: string, target: string,
                  sm: Spec.Metadata, tm: Spec.Metadata, mode: bv32, linkTarget: string, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool, receipt: Spec.CopyReceipt)
    modifies io.fsRegion
    ensures Spec.LeafCopy(raw,source,target,sm,tm,(mode,linkTarget),old(io.fs()),io.fs(),io.props(),io.now(),
                          io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok)
    ensures Spec.LeafResult(raw,source,target,sm,tm,(mode,linkTarget),old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),(out,err,ok,receipt))
  {
    hide *;
    reveal Spec.LeafCopy(), Spec.LeafResult(), Spec.LeafOutcome();
    receipt := Spec.CopyReceipt(Spec.NoDestinationRecord,false,false);
    ghost var before := io.fs();
    var qs := Quoted(source,io);
    var qt := Quoted(target,io);
    var removeOK,removeErr := true,0;
    var preUnlink := Spec.PreUnlink(raw,sm,tm);
    if preUnlink {
      var result := io.UnlinkPath(target);
      removeOK,removeErr := result.Ok?,C.ResultErrno(result);
      if !removeOK && removeErr != 2 {
        var reason := Reason(removeErr,io);
        assert Spec.LeafOutcome(raw,source,target,sm,tm,(mode,linkTarget),before,io.fs(),io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                                ([],Spec.CannotRemove(qt,reason),false,receipt),(io.fs(),removeOK,removeErr,true,0,true,io.fs(),[],true,[]));
        return [],Text.CannotRemove(qt,reason),false,receipt;
      }
    }
    ghost var ready := io.fs();
    out := (if raw.policy.verbose && preUnlink then Spec.Removed(qt) else []) +
    (if raw.policy.verbose then Spec.Verbose(qs,qt) else []);
    var linkOK,linkErr,relativeOK := true,0,true;
    ghost var linked := ready;
    var attributeErr: BW.Bytes := [];
    var attributeOK := true;
    var dataOut: BW.Bytes := [];
    if raw.policy.symbolic || sm.value.isSymlink || raw.policy.hard {
      if raw.policy.symbolic { relativeOK := RelativeLinkAllowed(source,target,io); }
      if !relativeOK { err,ok := Text.RelativeSymlinkError(target),false; }
      else {
        var result: BW.IOResult<BW.Unit>;
        if raw.policy.hard { result := io.CreateHardLink(linkTarget,target,raw.policy.dereference); }
        else { result := io.CreateSymlink(target,linkTarget); }
        linkOK,linkErr := result.Ok?,C.ResultErrno(result);
        linked := io.fs();
        if linkOK {
          var record := RecordDestination(target,io);
          receipt := Spec.CopyReceipt(record,true,false);
        }
        if linkOK && !raw.policy.hard {
          attributeErr,attributeOK := Attributes(raw,sm,mode,target,false,io);
        }
        ok := linkOK && attributeOK;
        err := attributeErr;
        if !linkOK {
          var reason := Reason(linkErr,io);
          var qLinkSource := Quoted(if raw.policy.hard then linkTarget else source,io);
          err := if raw.policy.hard || raw.policy.symbolic then Text.LinkError(qLinkSource,qt,reason,!raw.policy.hard)
          else Text.CopiedSymlinkError(qt,reason);
        }
      }
    } else {
      dataOut,err,ok := CopyData(raw,source,target,sm,mode,io);
      out := out+dataOut;
      if ok {
        var record := RecordDestination(target,io);
        receipt := Spec.CopyReceipt(record,true,false);
      }
    }
    assert Spec.LeafOutcome(raw,source,target,sm,tm,(mode,linkTarget),before,io.fs(),io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                            (out,err,ok,receipt),(ready,removeOK,removeErr,linkOK,linkErr,relativeOK,linked,attributeErr,attributeOK,dataOut)) by {
      hide *;
      reveal Spec.LeafOutcome();
    }
  }

  method SameEntry(source: string, target: string, io: BenchIO.IO) returns (result: bool)
    ensures Spec.SameEntryFields(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),source,target,result)
  {
    hide *;
    reveal Spec.SameEntryFields();
    if source == target { return true; }
    var sourceParent := Paths.ComputeDirnameValue(source);
    var targetParent := Paths.ComputeDirnameValue(target);
    var sourceBase := Paths.ComputeBasenameValue(source);
    var targetBase := Paths.ComputeBasenameValue(target);
    PathProof.DirnameValueSummaryGivesRelation(source,sourceParent);
    PathProof.DirnameValueSummaryGivesRelation(target,targetParent);
    PathProof.BasenameValueSummaryGivesRelation(source,sourceBase);
    PathProof.BasenameValueSummaryGivesRelation(target,targetBase);
    var sm := Metadata(sourceParent,false,io);
    var tm := Metadata(targetParent,false,io);
    result := sm.ok && tm.ok && Spec.Identity(sm) == Spec.Identity(tm) && sourceBase == targetBase;
  }

  function SameFileValue(raw: S.CpCmdRaw, source: Spec.Metadata, target: Spec.Metadata, observed: Spec.SameFileObservation): (result: (bool,bool))
    ensures Spec.SameFileDecisionFields(raw,source,target,observed,result.0,result.1)
  {
    var sl,tl,sf,tf,sameEntry := observed.sourceEntry,observed.targetEntry,observed.sourceFollow,observed.targetFollow,observed.sameEntry;
    var same := Spec.Identity(source) == Spec.Identity(target);
    var sameLink := Spec.Identity(sl) == Spec.Identity(tl);
    var bothLinks := sl.value.isSymlink && tl.value.isSymlink;
    var backup := Spec.BackupMode(raw) != "off";
    if same && raw.policy.hard then (true,true)
    else if raw.policy.dereference && (!same || !tl.ok || !sl.ok) then (true,false)
    else if !raw.policy.dereference && bothLinks then (!sameEntry,!sameEntry && !backup && sameLink)
    else if raw.policy.dereference && bothLinks && raw.policy.remove then (true,false)
    else if backup then ((if sameLink then !sameEntry else !(raw.policy.dereference && sl.value.isSymlink && !tl.value.isSymlink)),false)
    else if raw.policy.remove && (tl.value.isSymlink || (sameLink && tl.value.linkCount > 1 && !sameEntry)) then (true,false)
    else if !sl.value.isSymlink && !tl.value.isSymlink then (!sameLink || raw.policy.hard,sameLink && raw.policy.hard)
    else if raw.policy.symbolic && tl.value.isSymlink then (true,false)
    else if !raw.policy.dereference then
      var different := !sf.ok || !tf.ok || Spec.Identity(sf) != Spec.Identity(tf);
      (different || raw.policy.hard,!different && raw.policy.hard && !tl.value.isSymlink)
    else (false,false)
  }

  method SameFileEligibility(raw: S.CpCmdRaw, source: string, target: string, sm: Spec.Metadata, tm: Spec.Metadata, io: BenchIO.IO)
    returns (allowed: bool, returnNow: bool)
    ensures Spec.SameFileEligibility(raw,source,target,sm,tm,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),allowed,returnNow)
  {
    hide *;
    var sl,tl := sm,tm;
    var same := Spec.Identity(sm) == Spec.Identity(tm);
    if raw.policy.dereference && same && !raw.policy.hard {
      tl := Metadata(target,false,io);
      if tl.ok { sl := Metadata(source,false,io); }
    }
    var sameLink := Spec.Identity(sl) == Spec.Identity(tl);
    var bothLinks := sl.value.isSymlink && tl.value.isSymlink;
    var backup := Spec.BackupMode(raw) != "off";
    var active := !(same && raw.policy.hard) && !(raw.policy.dereference && (!same || !tl.ok || !sl.ok));
    var askEntry := active && ((!raw.policy.dereference && bothLinks) ||
                               (!(raw.policy.dereference && bothLinks && raw.policy.remove) &&
                                ((backup && sameLink) || (!backup && raw.policy.remove && !tl.value.isSymlink && sameLink && tl.value.linkCount > 1))));
    var sameEntry := false;
    if askEntry { sameEntry := SameEntry(source,target,io); }
    var askFollow := active && !raw.policy.dereference && !bothLinks && !backup &&
                     !(raw.policy.remove && (tl.value.isSymlink || (sameLink && tl.value.linkCount > 1 && !sameEntry))) &&
                     !(!sl.value.isSymlink && !tl.value.isSymlink) && !(raw.policy.symbolic && tl.value.isSymlink);
    var sf,tf := sl,tl;
    if askFollow && sl.value.isSymlink { sf := Metadata(source,true,io); }
    if askFollow && sf.ok && tl.value.isSymlink { tf := Metadata(target,true,io); }
    var observed := Spec.SameFileObservation(sl,tl,sf,tf,sameEntry);
    var result := SameFileValue(raw,sm,tm,observed);
    allowed,returnNow := result.0,result.1;
    assert Spec.SameFileObservationFields(raw,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),source,target,sm,tm,observed) by {
      hide *;
      reveal Spec.SameFileObservationFields();
    }
    assert Spec.SameFileEligibility(raw,source,target,sm,tm,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),allowed,returnNow) by {
      hide *;
      reveal Spec.SameFileEligibility();
    }
  }

  method ParseBackupVersion(base: string, name: string) returns (version: nat)
    ensures Spec.BackupVersion(base,name,version)
  {
    hide *;
    version := 0;
    if |name| < |base|+4 || !CliModel.HasPrefix(name,base+".~") || name[|name|-1] != '~' || !('1' <= name[|base|+2] <= '9') {
      Proof.RejectBackupLayout(base,name);
      return;
    }
    var start,stop := |base|+2,|name|-1;
    var i := start;
    while i < stop
      invariant start == |base|+2 && stop == |name|-1
      invariant start <= i <= stop
      invariant i == start ==> version == 0
      invariant i > start ==> version > 0 && PathSpec.DecimalNatSpec(version) == name[start..i]
      modifies {}
      decreases stop-i
    {
      if !('0' <= name[i] <= '9') {
        Proof.RejectBackupDigit(base,name,i);
        return 0;
      }
      var digit := ((name[i] as int)-('0' as int)) as nat;
      Proof.DigitCharacter(digit);
      assert PathSpec.DigitCharSpec(digit) == name[i];
      if i == start {
        version := digit;
        assert version > 0;
        assert PathSpec.DecimalNatSpec(version) == [name[i]] by { reveal PathSpec.DecimalNatSpec(); }
      } else {
        Proof.DecimalAppend(version,digit);
        version := version*10+digit;
      }
      assert name[start..i+1] == name[start..i]+[name[i]];
      i := i+1;
    }
    assert name[..start] == base+".~" by { reveal CliModel.HasPrefix(); }
    assert name == base+".~"+name[start..stop]+"~";
    reveal Spec.BackupVersion(), Spec.NumberedVersion();
  }

  method BackupName(target: string, mode: string, suffix: string, io: BenchIO.IO) returns (path: string, err: int)
    modifies io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.BackupSelection(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),target,mode,suffix,path,err)
  {
    hide *;
    reveal Spec.BackupSelection();
    var parent,base := "","";
    var entries: seq<Spec.DirectoryName> := [];
    var scanErr,wasOpened := 0,false;
    ghost var chosenMaximum: nat := 0;
    if mode == "simple" {
      path := PathSpec.SimpleBackupPathSpec(target,suffix);
      err := 0;
    } else {
      parent := Paths.ComputeDirnameValue(target);
      PathProof.DirnameValueSummaryGivesRelation(target,parent);
      base := Paths.ComputeBasenameValue(target);
      PathProof.BasenameValueSummaryGivesRelation(target,base);
      entries,scanErr,wasOpened := Enumerate(parent,io);
      if !wasOpened && scanErr == 12 { path,err := "",12; }
      else {
        var maximum: nat := 0;
        var i := 0;
        assert Spec.MaximumBackup([],base,0) by { reveal Spec.MaximumBackup(); }
        while i < |entries|
          invariant 0 <= i <= |entries|
          invariant Spec.MaximumBackup(entries[..i],base,maximum)
          modifies {}
          decreases |entries|-i
        {
          var number := ParseBackupVersion(base,entries[i].name);
          Proof.MaximumBackupAppend(entries[..i],base,maximum,entries[i],number);
          assert entries[..i]+[entries[i]] == entries[..i+1];
          if number > maximum { maximum := number; }
          i := i+1;
        }
        assert Spec.MaximumBackup(entries,base,maximum) by {
          hide *;
          assert i == |entries|;
          assert entries[..i] == entries;
        }
        chosenMaximum := maximum;
        if mode == "existing" && maximum == 0 {
          path := PathSpec.SimpleBackupPathSpec(target,suffix);
        }
        else {
          path := PathSpec.NumberedBackupPathSpec(target,maximum+1);
        }
        err := 0;
      }
    }
    assert Spec.BackupSelectionFields(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),target,mode,suffix,path,err,(parent,base,entries,scanErr,wasOpened,chosenMaximum)) by {
      hide *;
      reveal Spec.BackupSelectionFields();
    }
  }

  method PrepareBackup(raw: S.CpCmdRaw, source: string, target: string, sm: Spec.Metadata, io: BenchIO.IO)
    returns (preparation: Spec.BackupPreparationResult)
    modifies io.fsRegion,io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.BackupPreparation(raw,source,target,sm,old(io.fs()),io.fs(),io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),preparation)
  {
    hide *;
    reveal Spec.BackupPreparation();
    ghost var before := io.fs();
    var sourceBase := Paths.ComputeBasenameValue(source);
    PathProof.BasenameValueSummaryGivesRelation(source,sourceBase);
    var targetBase := Paths.ComputeBasenameValue(target);
    PathProof.BasenameValueSummaryGivesRelation(target,targetBase);
    var candidate := Spec.Metadata(false,0,BW.FileTimeStatus(0,0,0,0,false,false,0,0,0));
    var selected,selectionErr,renameOK,renameErr := "",0,true,0;
    if Spec.BackupMode(raw) != "numbered" && sourceBase == targetBase+Spec.BackupSuffix(raw) {
      candidate := Metadata(target+Spec.BackupSuffix(raw),true,io);
    }
    if candidate.ok && Spec.Identity(candidate) == Spec.Identity(sm) {
      var qs := Quoted(source,io);
      var qt := Quoted(target,io);
      preparation := Spec.BackupRejected(Spec.BackupDestroysSource(qs,qt));
    } else {
      selected,selectionErr := BackupName(target,Spec.BackupMode(raw),Spec.BackupSuffix(raw),io);
      if selectionErr != 0 {
        var qt := Quoted(target,io);
        var reason := Reason(selectionErr,io);
        preparation := Spec.BackupRejected(Text.CannotBackup(qt,reason));
      } else {
        var result := io.RenamePath(target,selected);
        renameOK,renameErr := result.Ok?,C.ResultErrno(result);
        if !renameOK && renameErr != 2 {
          var qt := Quoted(target,io);
          var reason := Reason(renameErr,io);
          preparation := Spec.BackupRejected(Text.CannotBackup(qt,reason));
        } else { preparation := Spec.BackupReady(selected,renameOK); }
      }
    }
    assert Spec.BackupPreparationFields(raw,source,target,sm,before,io.fs(),io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),preparation,
                                        Spec.BackupPreparationObservation(sourceBase,targetBase,candidate,selected,selectionErr,io.fs(),renameOK,renameErr)) by {
      hide *;
      reveal Spec.BackupPreparationFields();
    }
  }

  method RestoreBackup(raw: S.CpCmdRaw, backup: string, target: string, needed: bool, io: BenchIO.IO) returns (out: BW.Bytes, err: BW.Bytes)
    modifies io.fsRegion
    ensures Spec.BackupRestoration(raw,backup,target,needed,old(io.fs()),io.fs(),io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),out,err)
  {
    hide *;
    reveal Spec.BackupRestoration();
    ghost var before := io.fs();
    out,err := [],[];
    var restoredOK,restoreErr := true,0;
    if needed {
      var result := io.RenamePath(backup,target);
      restoredOK,restoreErr := result.Ok?,C.ResultErrno(result);
      var qt := Quoted(target,io);
      if !restoredOK {
        var reason := Reason(restoreErr,io);
        err := Text.CannotUnbackup(qt,reason);
      } else if raw.policy.verbose {
        var qb := Quoted(backup,io);
        out := Spec.VerboseUnbackup(qb,qt);
      }
    }
    assert Spec.BackupRestorationFields(raw,backup,target,needed,before,io.fs(),io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),out,err,(restoredOK,restoreErr)) by {
      hide *;
      reveal Spec.BackupRestorationFields();
    }
  }

  method {:isolate_assertions} CopyBackupLeaf(raw: S.CpCmdRaw, source: string, target: string, sm: Spec.Metadata, tm: Spec.Metadata,
                                              mode: bv32, linkTarget: string, io: BenchIO.IO) returns (out: BW.Bytes, err: BW.Bytes, ok: bool, receipt: Spec.CopyReceipt)
    modifies io.fsRegion,io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.BackupLeaf(raw,source,target,sm,tm,(mode,linkTarget),old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),(out,err,ok,receipt))
  {
    hide *;
    reveal Spec.BackupLeaf();
    ghost var before := io.fs();
    var preparation := Spec.BackupReady("",false);
    ghost var prepared,copied := before,before;
    var readyMetadata := tm;
    var leafOut: BW.Bytes := [];
    var leafErr: BW.Bytes := [];
    var leafOK := true;
    var restoreOut: BW.Bytes := [];
    var restoreErr: BW.Bytes := [];
    receipt := Spec.CopyReceipt(Spec.NoDestinationRecord,false,false);
    if Spec.BackupMode(raw) == "off" || !tm.ok || tm.value.isDir {
      out,err,ok,receipt := CopyLeaf(raw,source,target,sm,tm,mode,linkTarget,io);
    } else {
      preparation := PrepareBackup(raw,source,target,sm,io);
      prepared := io.fs();
      if preparation.BackupRejected? { out,err,ok := [],preparation.error,false; }
      else {
        readyMetadata := Metadata(target,!raw.policy.remove && !raw.policy.symbolic && !raw.policy.hard && !sm.value.isSymlink,io);
        var quiet := raw.(policy := raw.policy.(verbose := false));
        leafOut,leafErr,leafOK,receipt := CopyLeaf(quiet,source,target,sm,readyMetadata,mode,linkTarget,io);
        copied := io.fs();
        restoreOut,restoreErr := RestoreBackup(raw,preparation.path,target,!leafOK && !receipt.retained && preparation.renamed,io);
        var qs := Quoted(source,io);
        var qt := Quoted(target,io);
        var qb := Quoted(preparation.path,io);
        out := (if raw.policy.verbose then (if preparation.renamed then Spec.VerboseBackup(qs,qt,qb) else Spec.Verbose(qs,qt)) else [])+leafOut+restoreOut;
        err,ok := leafErr+restoreErr,leafOK;
      }
    }
    assert Spec.BackupLeafFields(raw,source,target,sm,tm,(mode,linkTarget),before,io.fs(),io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),(out,err,ok,receipt),
                                 Spec.BackupObservation(prepared,preparation,readyMetadata,copied,leafOut,leafErr,leafOK,receipt,restoreOut,restoreErr)) by {
      hide *;
      reveal Spec.BackupLeafFields();
      if Spec.BackupMode(raw) == "off" || !tm.ok || tm.value.isDir {
        assert Spec.LeafResult(raw,source,target,sm,tm,(mode,linkTarget),before,io.fs(),io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),(out,err,ok,receipt));
      } else {
        assert Spec.BackupPreparation(raw,source,target,sm,before,prepared,io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),preparation);
        if preparation.BackupRejected? {
          assert io.fs() == prepared && out == [] && err == preparation.error && !ok;
          assert receipt == Spec.CopyReceipt(Spec.NoDestinationRecord,false,false);
        } else {
          assert Spec.MetadataFields(prepared,Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),target,!raw.policy.remove && !raw.policy.symbolic && !raw.policy.hard && !sm.value.isSymlink,readyMetadata);
          assert Spec.LeafResult(raw.(policy := raw.policy.(verbose := false)),source,target,sm,readyMetadata,(mode,linkTarget),prepared,copied,io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),(leafOut,leafErr,leafOK,receipt));
          assert Spec.BackupRestoration(raw,preparation.path,target,!leafOK && !receipt.retained && preparation.renamed,copied,io.fs(),io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),restoreOut,restoreErr);
          assert out == (if raw.policy.verbose then (if preparation.renamed then Spec.VerboseBackup(Spec.Q(source),Spec.Q(target),Spec.Q(preparation.path)) else Spec.Verbose(Spec.Q(source),Spec.Q(target))) else [])+leafOut+restoreOut;
          assert err == leafErr+restoreErr && ok == leafOK;
        }
      }
    }
  }

  method CopyFile(raw: S.CpCmdRaw, tree: Spec.SourceTree, target: string, tm: Spec.Metadata,
                  known: Spec.LinkMap, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool, links: Spec.LinkMap, record: Spec.CopyReceipt)
    requires tree.FileSource?
    modifies io.fsRegion,io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.FileEffect(raw,tree,target,tm,old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok,(known,links),record)
  {
    hide *;
    reveal Spec.FileEffect();
    links := known;
    record := Spec.CopyReceipt(Spec.NoDestinationRecord,false,false);
    var receipt: Spec.CopyReceipt;
    if Spec.PreserveEligible(raw,tree) && Spec.Identity(tree.metadata) in known {
      out,err,ok,receipt := CopyBackupLeaf(Spec.LinkCommand(raw),tree.path,target,tree.metadata,tm,tree.mode,known[Spec.Identity(tree.metadata)],io);
      record := Spec.CopyReceipt(Spec.NoDestinationRecord,receipt.retained,false);
    } else {
      out,err,ok,receipt := CopyBackupLeaf(raw,tree.path,target,tree.metadata,tm,tree.mode,tree.linkTarget,io);
      record := receipt;
      if Spec.PreserveEligible(raw,tree) && receipt.retained { links := known[Spec.Identity(tree.metadata) := target]; }
    }
  }

  lemma {:isolate_assertions} CompleteFileTree(raw: S.CpCmdRaw, tree: Spec.SourceTree, target: string, tm: Spec.Metadata,
                                               before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                               credentials: BW.ProcessCredentials, mask: bv32, provider: Spec.FilesystemProvider,
                                               streams: Spec.StreamProvider, out: BW.Bytes, err: BW.Bytes, ok: bool,
                                               linkState: (Spec.LinkMap,Spec.LinkMap,bool), record: Spec.CopyReceipt, allowed: bool, returnNow: bool)
    requires tree.FileSource?
    requires Spec.MetadataFields(before,provider,target,!raw.policy.remove && !raw.policy.symbolic && !raw.policy.hard && !tree.metadata.value.isSymlink && Spec.BackupMode(raw) == "off",tm)
    requires if tm.ok && !raw.policy.skip && raw.policy.update != "none" && raw.policy.update != "none-fail" then
               Spec.SameFileEligibility(raw,tree.path,target,tree.metadata,tm,before,provider,allowed,returnNow)
             else allowed && !returnNow
    requires if !allowed then record == Spec.CopyReceipt(Spec.NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == Spec.SameFile(Spec.Q(tree.path),Spec.Q(target)) && !ok
             else if Spec.Skip(raw,tree.metadata,tm) then record == Spec.CopyReceipt(Spec.NoDestinationRecord,false,false) && linkState.1 == (if raw.policy.update == "older" && Spec.Identity(tree.metadata) !in linkState.0 then linkState.0[Spec.Identity(tree.metadata) := target] else linkState.0) && after == before && out == [] && err == (if raw.policy.update == "none-fail" then Spec.NotReplaced(Spec.Q(target)) else []) && ok == (raw.policy.update != "none-fail")
             else if returnNow then record == Spec.CopyReceipt(Spec.NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == [] && ok
             else if tm.ok && tm.value.isDir && Spec.BackupMode(raw) == "off" then
               record == Spec.CopyReceipt(Spec.NoDestinationRecord,false,false) && linkState.1 == linkState.0 && after == before && out == [] && err == Spec.NonDirectory(Spec.Q(tree.path),Spec.Q(target)) && !ok
             else Spec.FileEffect(raw,tree,target,tm,before,after,props,now,credentials,provider,streams,out,err,ok,(linkState.0,linkState.1),record)
    ensures Spec.CopyTree(raw,tree,target,before,after,props,now,credentials,mask,provider,streams,out,err,ok,linkState,record)
  {
    hide *;
    reveal Spec.CopyTree();
    assert Spec.FileTreeFields(raw,tree,target,before,after,props,now,credentials,provider,streams,
                               out,err,ok,linkState,record,Spec.FileTreeObservation(tm,allowed,returnNow)) by {
      reveal Spec.FileTreeFields();
    }
  }

  method CopyTree(raw: S.CpCmdRaw, tree: Spec.SourceTree, target: string, known: Spec.LinkMap, selfCheck: bool, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool, links: Spec.LinkMap, record: Spec.CopyReceipt)
    modifies io.fsRegion,io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.CopyTree(raw,tree,target,old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok,(known,links,selfCheck),record)
    decreases Spec.TreeHeight(tree),2
  {
    links := known;
    record := Spec.CopyReceipt(Spec.NoDestinationRecord,false,false);
    hide *;
    reveal Spec.CopyTree();
    ghost var before := io.fs();
    var qs := Quoted(tree.path,io);
    var qt := Quoted(target,io);
    if tree.MissingSource? { var reason := Reason(tree.metadata.err,io); return [],Text.CannotStat(qs,reason),false,known,record; }
    if tree.ModeFailureSource? { var reason := Reason(tree.modeErr,io); return [],Text.CannotStat(qs,reason),false,known,record; }
    if tree.LinkFailureSource? { var reason := Reason(C.IOErrorErrno(tree.linkError),io); return [],Text.ReadSymlinkError(qs,reason),false,known,record; }
    if tree.OmittedSource? { return [],Spec.Omitting(qs),false,known,record; }
    if tree.CyclicSource? { return [],Spec.Cycle(qs),false,known,record; }
    var follow := if tree.DirectorySource? then raw.policy.keepDirectorySymlink else (!raw.policy.remove && !raw.policy.symbolic && !raw.policy.hard && !tree.metadata.value.isSymlink && Spec.BackupMode(raw) == "off");
    var tm := Metadata(target,follow,io);
    if tree.FileSource? {
      var allowed,returnNow := true,false;
      if tm.ok && !raw.policy.skip && raw.policy.update != "none" && raw.policy.update != "none-fail" {
        allowed,returnNow := SameFileEligibility(raw,tree.path,target,tree.metadata,tm,io);
      }
      if !allowed { out,err,ok := [],Spec.SameFile(qs,qt),false; }
      else if Spec.Skip(raw,tree.metadata,tm) {
        if raw.policy.update == "older" && Spec.Identity(tree.metadata) !in links {
          links := links[Spec.Identity(tree.metadata) := target];
        }
        out,err,ok := [],(if raw.policy.update == "none-fail" then Spec.NotReplaced(qt) else []),raw.policy.update != "none-fail";
      }
      else if returnNow { out,err,ok := [],[],true; }
      else if tm.ok && tm.value.isDir && Spec.BackupMode(raw) == "off" { out,err,ok := [],Spec.NonDirectory(qs,qt),false; }
      else { out,err,ok,links,record := CopyFile(raw,tree,target,tm,known,io); }
      CompleteFileTree(raw,tree,target,tm,before,io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok,(known,links,selfCheck),record,allowed,returnNow);
    } else {
      if tm.ok && Spec.Identity(tree.metadata) == Spec.Identity(tm) { return [],Spec.SameFile(qs,qt),false,known,record; }
      if tm.ok && !tm.value.isDir && Spec.BackupMode(raw) == "off" { return [],Spec.DirectoryOverFile(qs,qt),false,known,record; }
      var receipt: Spec.CopyReceipt;
      out,err,ok,links,receipt := CopyBackupDirectory(raw,tree,target,tm,known,selfCheck,io);
      record := receipt;
    }
  }

  lemma CompleteDirectoryReady(raw: S.CpCmdRaw, target: string, tm: Spec.Metadata, sourceMode: bv32,
                               before: BW.FileSystem, after: BW.FileSystem, now: int, mask: bv32,
                               provider: Spec.FilesystemProvider, ok: bool, err: BW.Bytes,
                               observed: Spec.DirectoryReadyObservation)
    requires tm.ok && tm.value.isDir ==> after == before && ok && err == []
    requires !(tm.ok && tm.value.isDir) ==>
               C.CreateDirectorySpec(before,now,provider.filesystem,mask,observed.created,target,Spec.DirectoryCreationMode(raw,sourceMode),observed.createOK,observed.createErr)
    requires !(tm.ok && tm.value.isDir) && !observed.createOK ==>
               after == observed.created && !ok && err == Spec.CreateDirectoryError(Spec.Q(target),Spec.E(observed.createErr))
    requires !(tm.ok && tm.value.isDir) && observed.createOK ==>
               Spec.MetadataFields(observed.created,provider,target,false,observed.metadata)
    requires !(tm.ok && tm.value.isDir) && observed.createOK && !observed.metadata.ok ==>
               after == observed.created && !ok && err == Spec.CannotStat(Spec.Q(target),Spec.E(observed.metadata.err))
    requires !(tm.ok && tm.value.isDir) && observed.createOK && observed.metadata.ok ==>
               C.GetFileModeSpec(observed.created,provider.failures,target,false,observed.modeOK,observed.mode,observed.modeErr)
    requires !(tm.ok && tm.value.isDir) && observed.createOK && observed.metadata.ok && !observed.modeOK ==>
               after == observed.created && !ok && err == Spec.CannotStat(Spec.Q(target),Spec.E(observed.modeErr))
    requires !(tm.ok && tm.value.isDir) && observed.createOK && observed.metadata.ok && observed.modeOK && (observed.mode & (448 as bv32)) != (448 as bv32) ==>
               C.SetFileModeSpec(observed.created,now,provider.failures,after,target,false,observed.mode | (448 as bv32),observed.changeOK,observed.changeErr)
    requires !(tm.ok && tm.value.isDir) && observed.createOK && observed.metadata.ok && observed.modeOK && (observed.mode & (448 as bv32)) == (448 as bv32) ==>
               after == observed.created && observed.changeOK && observed.changeErr == 0
    requires !(tm.ok && tm.value.isDir) && observed.createOK && observed.metadata.ok && observed.modeOK ==>
               ok == observed.changeOK && err == (if ok then [] else Spec.ParentSetModeError(Spec.Q(target),Spec.E(observed.changeErr)))
    ensures Spec.DirectoryReady(raw,target,tm,sourceMode,before,after,now,mask,provider,ok,err,observed.mode)
  {
    hide *;
    assert Spec.DirectoryReadyFields(raw,target,tm,sourceMode,before,after,now,mask,provider,ok,err,observed) by {
      reveal Spec.DirectoryReadyFields();
    }
    reveal Spec.DirectoryReady();
  }

  method {:isolate_assertions} ReadyDirectory(raw: S.CpCmdRaw, target: string, tm: Spec.Metadata, sourceMode: bv32, io: BenchIO.IO)
    returns (ok: bool, err: BW.Bytes, mode: bv32)
    modifies io.fsRegion
    ensures Spec.DirectoryReady(raw,target,tm,sourceMode,old(io.fs()),io.fs(),io.now(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),ok,err,mode)
  {
    hide *;
    reveal Spec.DirectoryReady();
    ghost var before := io.fs();
    ghost var created := before;
    var createOK,createErr,modeOK,modeErr,changeOK,changeErr := true,0,true,0,true,0;
    var metadata := tm;
    mode := 0 as bv32;
    ok,err := true,[];
    if !tm.ok || !tm.value.isDir {
      var result := io.CreateDirectory(target,Spec.DirectoryCreationMode(raw,sourceMode));
      createOK,createErr := result.Ok?,C.ResultErrno(result);
      created := io.fs();
      var qt := Quoted(target,io);
      if !createOK {
        var reason := Reason(createErr,io);
        ok,err := false,Text.CreateDirectoryError(qt,reason);
        assert err == Spec.CreateDirectoryError(Spec.Q(target),Spec.E(createErr));
      } else {
        metadata := Metadata(target,false,io);
        if !metadata.ok {
          var reason := Reason(metadata.err,io);
          ok,err := false,Text.CannotStat(qt,reason);
          assert err == Spec.CannotStat(Spec.Q(target),Spec.E(metadata.err));
        } else {
          var modeResult := io.GetFileMode(target,false);
          modeOK,modeErr := modeResult.Ok?,C.ResultErrno(modeResult);
          mode := C.ResultValue(modeResult,0 as bv32);
          if !modeOK {
            var reason := Reason(modeErr,io);
            ok,err := false,Text.CannotStat(qt,reason);
            assert err == Spec.CannotStat(Spec.Q(target),Spec.E(modeErr));
          } else if (mode & (448 as bv32)) != (448 as bv32) {
            var changed := io.SetFileMode(target,false,mode | (448 as bv32));
            changeOK,changeErr := changed.Ok?,C.ResultErrno(changed);
            if !changeOK {
              var reason := Reason(changeErr,io);
              ok,err := false,Text.ParentSetModeError(qt,reason);
              assert err == Spec.ParentSetModeError(Spec.Q(target),Spec.E(changeErr));
            }
          }
        }
      }
    }
    CompleteDirectoryReady(raw,target,tm,sourceMode,before,io.fs(),io.now(),io.umask(),
                           Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),ok,err,
                           Spec.DirectoryReadyObservation(created,createOK,createErr,metadata,modeOK,mode,modeErr,changeOK,changeErr));
  }

  method CopyBackupDirectory(raw: S.CpCmdRaw, tree: Spec.SourceTree, target: string, tm: Spec.Metadata,
                             known: Spec.LinkMap, selfCheck: bool, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool, links: Spec.LinkMap, receipt: Spec.CopyReceipt)
    requires tree.DirectorySource?
    modifies io.fsRegion,io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.BackupDirectory(raw,tree,target,tm,old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),(out,err,ok,receipt),(known,links,selfCheck))
    decreases Spec.TreeHeight(tree),1
  {
    hide *;
    reveal Spec.BackupDirectory();
    ghost var before := io.fs();
    var preparation := Spec.BackupReady("",false);
    ghost var prepared,copied := before,before;
    var readyMetadata := tm;
    var sourceBase := "";
    var removeOK,removeErr := true,0;
    var copyOut: BW.Bytes := [];
    var copyErr: BW.Bytes := [];
    var copyOK := true;
    var restoreOut: BW.Bytes := [];
    var restoreErr: BW.Bytes := [];
    receipt := Spec.CopyReceipt(Spec.NoDestinationRecord,false,false);
    links := known;
    if Spec.BackupMode(raw) == "off" || !tm.ok || tm.value.isDir {
      out,err,ok,links,receipt := CopyDirectory(raw,tree,target,tm,known,selfCheck,io);
    } else {
      sourceBase := Paths.ComputeBasenameValue(tree.path);
      PathProof.BasenameValueSummaryGivesRelation(tree.path,sourceBase);
      if sourceBase == "." || sourceBase == ".." {
        if Spec.PreUnlink(raw,tree.metadata,tm) {
          var removed := io.UnlinkPath(target);
          removeOK,removeErr := removed.Ok?,C.ResultErrno(removed);
        }
        prepared := io.fs();
        if !removeOK && removeErr != 2 {
          var qt := Quoted(target,io);
          var reason := Reason(removeErr,io);
          out,err,ok := [],Text.CannotRemove(qt,reason),false;
        } else {
          readyMetadata := Metadata(target,raw.policy.keepDirectorySymlink,io);
          copyOut,copyErr,copyOK,links,receipt := CopyDirectory(raw,tree,target,readyMetadata,known,selfCheck,io);
          copied := io.fs();
          var qt := Quoted(target,io);
          out := (if raw.policy.verbose && Spec.PreUnlink(raw,tree.metadata,tm) then Spec.Removed(qt) else [])+copyOut;
          err,ok := copyErr,copyOK;
        }
      } else {
        preparation := PrepareBackup(raw,tree.path,target,tree.metadata,io);
        prepared := io.fs();
        if preparation.BackupRejected? { out,err,ok := [],preparation.error,false; }
        else {
          readyMetadata := Metadata(target,raw.policy.keepDirectorySymlink,io);
          copyOut,copyErr,copyOK,links,receipt := CopyDirectory(raw,tree,target,readyMetadata,known,selfCheck,io);
          copied := io.fs();
          restoreOut,restoreErr := RestoreBackup(raw,preparation.path,target,!copyOK && !receipt.retained && preparation.renamed,io);
          out,err,ok := copyOut+restoreOut,copyErr+restoreErr,copyOK;
        }
      }
    }
    assert Spec.BackupDirectoryFields(raw,tree,target,tm,before,io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),(out,err,ok,receipt),(known,links,selfCheck),
                                      Spec.DirectoryBackupObservation(prepared,preparation,readyMetadata,copied,copyOut,copyErr,copyOK,receipt,restoreOut,restoreErr,sourceBase,removeOK,removeErr)) by {
      hide *;
      reveal Spec.BackupDirectoryFields();
    }
  }

  lemma ForestMemberHeight(trees: seq<Spec.SourceTree>, index: nat)
    requires index < |trees|
    ensures Spec.TreeHeight(trees[index]) <= Spec.ForestHeight(trees)
    decreases |trees|
  {
    reveal Spec.ForestHeight();
    if index > 0 { ForestMemberHeight(trees[1..],index-1); }
  }

  lemma ForestBound(trees: seq<Spec.SourceTree>, bound: nat)
    requires 0 < bound
    requires forall i | 0 <= i < |trees| :: Spec.TreeHeight(trees[i]) < bound
    ensures Spec.ForestHeight(trees) < bound
    decreases |trees|
  {
    reveal Spec.ForestHeight();
    if |trees| > 0 { ForestBound(trees[1..],bound); }
  }

  method OriginalChildIndex(trees: seq<Spec.SourceTree>, path: string) returns (index: int)
    ensures Spec.OriginalChildIndex(trees,path,index)
  {
    index := 0;
    while index < |trees|
      invariant 0 <= index <= |trees|
      invariant forall i | 0 <= i < index :: trees[i].path != path
      decreases |trees|-index
    {
      if trees[index].path == path { return; }
      index := index+1;
    }
    index := -1;
  }

  method LiveChild(raw: S.CpCmdRaw, original: seq<Spec.SourceTree>, path: string, io: BenchIO.IO)
    returns (value: Spec.SourceTree, stopped: bool)
    ensures value.path == path
    ensures Spec.LiveChild(raw,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),original,path,value,stopped)
    ensures stopped || Spec.TreeHeight(value) <= Spec.ForestHeight(original)
  {
    reveal Spec.LiveChild();
    var index := OriginalChildIndex(original,path);
    var metadata := Metadata(path,raw.policy.dereference,io);
    var mode := 0 as bv32;
    var modeOK := false;
    var modeErr := 0;
    var linkTarget := path;
    var linkResult: BW.IOResult<string> := Results.Ok(path);
    stopped := false;
    if !metadata.ok { value := Spec.MissingSource(path,metadata); }
    else {
      var result := io.GetFileMode(path,raw.policy.dereference);
      modeOK := result.Ok?;
      modeErr := C.ResultErrno(result);
      mode := C.ResultValue(result,0 as bv32);
      assert C.GetFileModeSpec(io.fs(),io.trustedNativeFailures(),path,raw.policy.dereference,modeOK,mode,modeErr);
      if !modeOK {
        value := Spec.ModeFailureSource(path,metadata,modeErr);
      } else if metadata.value.isDir {
        reveal Spec.OriginalChildIndex();
        stopped := index < 0 || !original[index].DirectorySource? || Spec.Identity(original[index].metadata) != Spec.Identity(metadata);
        if stopped {
          value := Spec.UncopiedSource(path);
          reveal Spec.UncopiedSource();
          assert value.path == path;
        }
        else {
          value := Spec.DirectorySource(path,metadata,mode,original[index].children,original[index].scanErr);
          ForestMemberHeight(original,index);
          assert Spec.TreeHeight(value) == Spec.TreeHeight(original[index]) by { reveal Spec.TreeHeight(); }
        }
      } else {
        if metadata.value.isSymlink && !raw.policy.hard && !raw.policy.symbolic {
          if raw.policy.dereference { FollowedMetadataIsNotSymlink(io.fs(),path); }
          assert !raw.policy.dereference;
          assert C.ResolvePathForMetadataFields(io.fs(),path,false).Ok?;
          assert BW.FsNodeAt(io.fs(),C.ResolvePathForMetadataFields(io.fs(),path,false).v).Symlink?;
          linkResult := io.ReadLink(path);
          if linkResult.Ok? { linkTarget := linkResult.v; }
        }
        value := if linkResult.Ok? then Spec.FileSource(path,metadata,mode,linkTarget)
        else Spec.LinkFailureSource(path,metadata,mode,linkResult.e);
      }
    }
    assert stopped || Spec.TreeHeight(value) <= Spec.ForestHeight(original) by {
      reveal Spec.TreeHeight();
    }
    assert Spec.LiveChildFields(raw,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),original,path,value,stopped,
                                Spec.LiveChildObservation(index,metadata,mode,linkTarget,modeOK,modeErr,linkResult)) by {
      hide *;
      reveal Spec.LiveChildFields();
    }
  }

  method SelectChildren(raw: S.CpCmdRaw, tree: Spec.SourceTree, enabled: bool, io: BenchIO.IO)
    returns (selected: seq<Spec.SourceTree>, stopped: bool, scanErr: int)
    requires tree.DirectorySource?
    modifies io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.LiveSelection(raw,tree,enabled,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),selected,stopped,scanErr)
    ensures Spec.ForestHeight(selected) < Spec.TreeHeight(tree)
  {
    hide *;
    reveal Spec.LiveSelection();
    selected,stopped,scanErr := tree.children,false,tree.scanErr;
    var entries: seq<Spec.DirectoryName> := [];
    ghost var processed: seq<Spec.SourceTree> := [];
    ghost var flags: seq<bool> := [];
    if enabled {
      var native,err,wasOpened := Enumerate(tree.path,io);
      entries := [];
      scanErr := err;
      if scanErr == 0 { entries := SortEntries(native); }
      assert Spec.OrderedEnumeration(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),tree.path,entries,scanErr) by {
        reveal Spec.OrderedEnumeration();
      }
      selected := [];
      var i := 0;
      while i < |entries| && !stopped
        invariant 0 <= i <= |entries|
        invariant |processed| == i && |flags| == i
        invariant |selected| == i - (if stopped then 1 else 0)
        invariant selected == processed[..|selected|]
        invariant forall j | 0 <= j < |selected| :: !flags[j]
        invariant !stopped || (i > 0 && flags[i-1])
        invariant forall j | 0 <= j < i :: Spec.NameConcat(tree.path,entries[j].name,processed[j].path) &&
                                           Spec.LiveChild(raw,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),tree.children,processed[j].path,processed[j],flags[j])
        invariant forall j | 0 <= j < |selected| :: Spec.TreeHeight(selected[j]) <= Spec.ForestHeight(tree.children)
        modifies {}
        decreases |entries|-i
      {
        var path := NameConcat(tree.path,entries[i].name);
        var value,stop := LiveChild(raw,tree.children,path,io);
        ghost var oldProcessed,oldFlags := processed,flags;
        ghost var oldSelected := selected;
        processed,flags := processed+[value],flags+[stop];
        if !stop { selected := selected+[value]; }
        stopped := stop;
        assert forall j | 0 <= j < |processed| :: Spec.NameConcat(tree.path,entries[j].name,processed[j].path) &&
                                                  Spec.LiveChild(raw,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),tree.children,processed[j].path,processed[j],flags[j]) by {
          hide *;
          forall j | 0 <= j < |processed|
            ensures Spec.NameConcat(tree.path,entries[j].name,processed[j].path)
            ensures Spec.LiveChild(raw,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),tree.children,processed[j].path,processed[j],flags[j])
          {
            if j < i { assert processed[j] == oldProcessed[j] && flags[j] == oldFlags[j]; }
            else { assert j == i; }
          }
        }
        i := i+1;
      }
    }
    assert Spec.TreeHeight(tree) == 1+Spec.ForestHeight(tree.children) by { reveal Spec.TreeHeight(); }
    if !enabled {
      forall j | 0 <= j < |selected|
        ensures Spec.TreeHeight(selected[j]) < Spec.TreeHeight(tree)
      {
        ForestMemberHeight(tree.children,j);
      }
    }
    ForestBound(selected,Spec.TreeHeight(tree));
    assert Spec.LiveSelectionFields(raw,tree,enabled,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),selected,stopped,scanErr,
                                    (entries,processed,flags)) by {
      hide *;
      reveal Spec.LiveSelectionFields();
    }
  }

  lemma CompleteDirectoryOutcome(raw: S.CpCmdRaw, tree: Spec.SourceTree, target: string, tm: Spec.Metadata,
                                 before: BW.FileSystem, after: BW.FileSystem, props: map<string,string>, now: int,
                                 credentials: BW.ProcessCredentials, mask: bv32, provider: Spec.FilesystemProvider,
                                 streams: Spec.StreamProvider, reported: (BW.Bytes,BW.Bytes,bool,Spec.CopyReceipt),
                                 observed: (BW.FileSystem,bool,BW.Bytes,BW.FileSystem,BW.Bytes,BW.Bytes,bool,BW.Bytes,bool,bv32,seq<Spec.SourceTree>,bool,int,bool),
                                 linkState: (Spec.LinkMap,Spec.LinkMap,bool))
    requires tree.DirectorySource? && observed.1
    requires Spec.DirectoryReady(raw,target,tm,tree.mode,before,observed.0,now,mask,provider,true,observed.2,observed.9)
    requires Spec.LiveSelection(S.ChildCommand(raw),tree,linkState.2,observed.0,provider,observed.10,observed.11,observed.12)
    requires Spec.Children(S.ChildCommand(raw),observed.10,target,observed.0,observed.3,props,now,credentials,mask,provider,streams,
                           observed.4,observed.5,observed.6,(linkState.0,linkState.1,linkState.2,observed.13))
    requires reported.3.retained && reported.3.selfCopy == (observed.11 || observed.13)
    requires Spec.DestinationRecordFields(observed.3,provider,target,reported.3.record)
    requires Spec.DirectoryAttributes(raw,tree,tm,observed.9,target,observed.3,after,now,props,provider,observed.7,observed.8)
    requires reported.0 == (if raw.policy.verbose && !tm.ok then Spec.Verbose(Spec.Q(tree.path),Spec.Q(target)) else []) + observed.4
    requires reported.1 == observed.5 + (if observed.12 == 0 then [] else Spec.ReadDirectoryError(Spec.Q(tree.path),Spec.E(observed.12))) + observed.7
    requires reported.2 == (observed.6 && observed.12 == 0 && observed.8 && !observed.11)
    ensures Spec.DirectoryOutcome(raw,tree,target,tm,before,after,props,now,credentials,mask,provider,streams,reported,observed,linkState)
  {
    hide *;
    reveal Spec.DirectoryOutcome();
  }

  method CopyDirectory(raw: S.CpCmdRaw, tree: Spec.SourceTree, target: string,
                       tm: Spec.Metadata, known: Spec.LinkMap, selfCheck: bool, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool, links: Spec.LinkMap, receipt: Spec.CopyReceipt)
    requires tree.DirectorySource?
    modifies io.fsRegion,io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.DirectoryEffect(raw,tree,target,tm,old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),(out,err,ok,receipt),(known,links,selfCheck))
    decreases Spec.TreeHeight(tree),0
  {
    links := known;
    receipt := Spec.CopyReceipt(Spec.NoDestinationRecord,false,false);
    hide *;
    reveal Spec.DirectoryEffect();
    var qs := Quoted(tree.path,io);
    var qt := Quoted(target,io);
    ghost var before := io.fs();
    var createOK,createErr,createdMode := ReadyDirectory(raw,target,tm,tree.mode,io);
    if !createOK {
      assert Spec.DirectoryOutcome(raw,tree,target,tm,before,io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),([],createErr,false,receipt),(io.fs(),createOK,createErr,io.fs(),[],[],true,[],true,createdMode,[],false,tree.scanErr,false),(known,links,selfCheck)) by {
        hide *;
        reveal Spec.DirectoryOutcome();
      }
      return [],createErr,false,known,receipt;
    }
    ghost var created := io.fs();
    var childOut: BW.Bytes;
    var childErr: BW.Bytes;
    var childOK: bool;
    var selected,selectionStopped,scanErr := SelectChildren(S.ChildCommand(raw),tree,selfCheck,io);
    var childStopped: bool;
    childOut,childErr,childOK,links,childStopped := CopyChildren(S.ChildCommand(raw),selected,target,known,selfCheck,io);
    ghost var copied := io.fs();
    var record := RecordDestination(target,io);
    receipt := Spec.CopyReceipt(record,true,selectionStopped || childStopped);
    var attributeCmd := raw.(policy := raw.policy.(preserveMode := raw.policy.preserveMode || !tm.ok));
    var mask := io.GetUmask();
    var finalMode := Spec.DirectoryFinalMode(raw,tree.mode,mask,createdMode);
    var attributeErr,attributeOK := Attributes(attributeCmd,tree.metadata,finalMode,target,true,io);
    assert Spec.DirectoryAttributes(raw,tree,tm,createdMode,target,copied,io.fs(),io.now(),io.props(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),attributeErr,attributeOK) by {
      hide *;
      reveal Spec.DirectoryAttributes();
    }
    out := (if raw.policy.verbose && !tm.ok then Spec.Verbose(qs,qt) else []) + childOut;
    err := childErr;
    if scanErr != 0 {
      var reason := Reason(scanErr,io);
      err := err + Text.ReadDirectoryError(qs,reason);
    }
    err := err + attributeErr;
    ok := childOK && scanErr == 0 && attributeOK && !selectionStopped;
    CompleteDirectoryOutcome(raw,tree,target,tm,before,io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),(out,err,ok,receipt),
                             (created,createOK,createErr,copied,childOut,childErr,childOK,attributeErr,attributeOK,createdMode,selected,selectionStopped,scanErr,childStopped),(known,links,selfCheck));
  }

  lemma AppendBlocks(parts: seq<BW.Bytes>, value: BW.Bytes, offsets: seq<nat>, next: BW.Bytes)
    requires Spec.BlockOffsets(parts,value,offsets)
    ensures Spec.BlockOffsets(parts+[next],value+next,offsets+[|value+next|])
  {
    reveal Spec.BlockOffsets();
    forall j {:nowarn} | 0 <= j < |parts|+1
      ensures (offsets+[|value+next|])[j] <= (offsets+[|value+next|])[j+1] <= |value+next|
      ensures (value+next)[(offsets+[|value+next|])[j]..(offsets+[|value+next|])[j+1]] == (parts+[next])[j]
    {
      if j < |parts| {
        ghost var block := parts[j];
        assert offsets[j] <= offsets[j+1] <= |value|;
        assert (value+next)[offsets[j]..offsets[j+1]] == value[offsets[j]..offsets[j+1]];
      } else {
        assert j == |parts|;
        assert offsets[j] == |value|;
        assert (offsets+[|value+next|])[j] == |value|;
        assert (offsets+[|value+next|])[j+1] == |value+next|;
        assert (value+next)[|value|..] == next;
      }
    }
  }

  lemma AllTrueAppend(values: seq<bool>, next: bool)
    ensures (forall i | 0 <= i < |values+[next]| :: (values+[next])[i]) ==
            ((forall i | 0 <= i < |values| :: values[i]) && next)
  {
    if forall i | 0 <= i < |values+[next]| :: (values+[next])[i] {
      assert (values+[next])[|values|] == next;
      forall i | 0 <= i < |values|
        ensures values[i]
      { assert (values+[next])[i] == values[i]; }
    } else if (forall i | 0 <= i < |values| :: values[i]) && next {
      forall i | 0 <= i < |values+[next]|
        ensures (values+[next])[i]
      {
        if i < |values| { assert (values+[next])[i] == values[i]; }
        else { assert i == |values|; }
      }
    }
  }

  method CopyChildren(raw: S.CpCmdRaw, trees: seq<Spec.SourceTree>, target: string, known: Spec.LinkMap, selfCheck: bool, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool, links: Spec.LinkMap, stopped: bool)
    modifies io.fsRegion,io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.Children(raw,trees,target,old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok,(known,links,selfCheck,stopped))
    decreases Spec.ForestHeight(trees),3
  {
    links := known;
    hide *;
    reveal Spec.Children();
    ghost var maps := [links];
    ghost var records: seq<Spec.CopyReceipt> := [];
    ghost var states := [io.fs()];
    ghost var outputs: seq<BW.Bytes> := [];
    ghost var errors: seq<BW.Bytes> := [];
    ghost var results: seq<bool> := [];
    ghost var targets: seq<string> := [];
    ghost var outputOffsets: seq<nat> := [0];
    ghost var errorOffsets: seq<nat> := [0];
    out,err,ok,stopped := [],[],true,false;
    assert Spec.BlockOffsets(errors,err,errorOffsets) by { reveal Spec.BlockOffsets(); }
    assert Spec.BlockOffsets(outputs,out,outputOffsets) by { reveal Spec.BlockOffsets(); }
    var i := 0;
    while i < |trees| && !stopped
      invariant |maps| == i+1 && maps[i] == links
      invariant maps[0] == known
      invariant io.dirHandles() == old(io.dirHandles())
      invariant 0 <= i <= |trees|
      invariant |states| == i+1 && states[0] == old(io.fs()) && states[i] == io.fs()
      invariant |records| == i
      invariant forall j | 0 <= j < i-1 :: !records[j].selfCopy
      invariant stopped == (i > 0 && records[i-1].selfCopy)
      invariant |outputs| == i && |errors| == i && |results| == i && |targets| == i
      invariant forall j | 0 <= j < i ::
                  Spec.TargetFields(target,trees[j].path,targets[j]) &&
                  Spec.CopyTree(raw,trees[j],targets[j],states[j],states[j+1],io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),outputs[j],errors[j],results[j],(maps[j],maps[j+1],selfCheck),records[j])
      invariant |outputOffsets| == i+1 && outputOffsets[0] == 0 && outputOffsets[i] == |out|
      invariant |errorOffsets| == i+1 && errorOffsets[0] == 0 && errorOffsets[i] == |err|
      invariant Spec.BlockOffsets(outputs,out,outputOffsets)
      invariant Spec.BlockOffsets(errors,err,errorOffsets)
      invariant ok == (forall j | 0 <= j < i :: results[j])
      modifies io.fsRegion,io.dirHandlesRegion
      decreases |trees|-i
    {
      var destination := Target(target,trees[i].path);
      var childOut: BW.Bytes;
      var childErr: BW.Bytes;
      var childOK: bool;
      var record: Spec.CopyReceipt;
      ForestMemberHeight(trees,i);
      childOut,childErr,childOK,links,record := CopyTree(raw,trees[i],destination,links,selfCheck,io);
      stopped := record.selfCopy;
      AppendBlocks(outputs,out,outputOffsets,childOut);
      AppendBlocks(errors,err,errorOffsets,childErr);
      AllTrueAppend(results,childOK);
      maps := maps + [links];
      records := records+[record];
      states := states + [io.fs()];
      targets := targets + [destination];
      outputs := outputs + [childOut];
      errors := errors + [childErr];
      results := results + [childOK];
      out,err,ok := out + childOut,err + childErr,ok && childOK;
      outputOffsets := outputOffsets + [|out|];
      errorOffsets := errorOffsets + [|err|];
      i := i+1;
    }
    assert Spec.Concatenation(outputs,out) by { reveal Spec.Concatenation(); }
    assert Spec.Concatenation(errors,err) by { reveal Spec.Concatenation(); }
    assert Spec.ChildrenFields(raw,trees,target,old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok,(known,links,selfCheck,stopped),
                               (states,outputs,errors,results,targets,maps,records)) by {
      hide *;
      reveal Spec.ChildrenFields();
    }
  }

  method SelfDestination(source: string, target: string, io: BenchIO.IO) returns (result: bool)
    ensures Spec.SelfDestination(io.fs(),io.cwd(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),source,target,result)
  {
    hide *;
    reveal Spec.SelfDestination(), C.ResultValue();
    var parent := Paths.ComputeDirnameValue(target);
    PathProof.DirnameValueSummaryGivesRelation(target,parent);
    var sourcePath := io.ResolvePathIdentity(source);
    var parentPath := io.ResolvePathIdentity(parent);
    result := sourcePath.Ok? && parentPath.Ok? &&
              (sourcePath.v == "/" || C.HasPathPrefix(sourcePath.v,parentPath.v));
  }

  method CopyRoot(raw: S.CpCmdRaw, tree: Spec.SourceTree, target: string, known: Spec.LinkMap, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool, links: Spec.LinkMap, record: Spec.CopyReceipt)
    modifies io.fsRegion,io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.RootCopy(raw,tree,target,io.cwd(),old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),(out,err,ok,record),(known,links))
  {
    links := known;
    hide *;
    reveal Spec.RootCopy(), Spec.RootOutcome();
    ghost var before := io.fs();
    ghost var provider := Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures());
    ghost var beforeTarget,afterTarget := tree.metadata,tree.metadata;
    var inside := false;
    var self := false;
    if tree.DirectorySource? && tree.scanErr == 0 {
      inside := SelfDestination(tree.path,target,io);
      self := inside;
      if self {
        var tm := Metadata(target,raw.policy.keepDirectorySymlink,io);
        beforeTarget := tm;
        self := !tm.ok || (if tm.value.isDir then Spec.Identity(tm) != Spec.Identity(tree.metadata) else Spec.BackupMode(raw) != "off");
      }
    }
    ghost var candidateSelf := self;
    assert (if tree.DirectorySource? && tree.scanErr == 0 then
              Spec.SelfDestination(before,io.cwd(),provider,tree.path,target,inside) &&
              (if inside then Spec.MetadataFields(before,provider,target,raw.policy.keepDirectorySymlink,beforeTarget) &&
                              candidateSelf == (!beforeTarget.ok || (if beforeTarget.value.isDir then
                                                                       Spec.Identity(beforeTarget) != Spec.Identity(tree.metadata) else Spec.BackupMode(raw) != "off"))
               else !candidateSelf)
            else !candidateSelf);
    out,err,ok,links,record := CopyTree(raw,tree,target,known,self,io);
    ghost var childErr,childOK := err,ok;
    assert Spec.CopyTree(raw,tree,target,before,io.fs(),io.props(),io.now(),io.credentials(),io.umask(),
                         provider,io.trustedStreams(),out,childErr,childOK,(known,links,candidateSelf),record);
    if self {
      var tm := Metadata(target,true,io);
      afterTarget := tm;
      self := record.selfCopy && tm.ok && tm.value.isDir;
    }
    assert (if candidateSelf then Spec.MetadataFields(io.fs(),provider,target,true,afterTarget) &&
                                  self == (record.selfCopy && afterTarget.ok && afterTarget.value.isDir) else !self);
    if self {
      var qs := Quoted(tree.path,io);
      var qt := Quoted(target,io);
      err := err + Spec.IntoSelf(qs,qt);
      ok := false;
    }
    assert err == childErr + (if self then Spec.IntoSelf(Spec.Q(tree.path),Spec.Q(target)) else []) &&
           ok == (childOK && !self);
    assert Spec.RootOutcome(raw,tree,target,io.cwd(),before,io.fs(),io.props(),io.now(),io.credentials(),io.umask(),provider,io.trustedStreams(),(out,err,ok,record),(candidateSelf,self,childErr,childOK,inside,beforeTarget,afterTarget),(known,links)) by {
      hide *;
      reveal Spec.RootOutcome();
    }
  }

  lemma ParentStepWitness(raw: S.CpCmdRaw, source: string, target: string, before: BW.FileSystem, after: BW.FileSystem,
                          now: int, mask: bv32, provider: Spec.FilesystemProvider,
                          reported: (BW.Bytes,BW.Bytes,bool,seq<Spec.ParentInfo>), observed: Spec.ParentStepObservation)
    requires Spec.MetadataFields(before,provider,target,true,observed.destination)
    requires !observed.destination.ok || raw.policy.preserveMode || raw.policy.preserveTimes ==>
               Spec.MetadataFields(before,provider,source,true,observed.source)
    requires (!observed.destination.ok || raw.policy.preserveMode || raw.policy.preserveTimes) && observed.source.ok && observed.source.value.isDir ==>
               C.GetFileModeSpec(before,provider.failures,source,true,observed.sourceModeOK,observed.sourceMode,observed.sourceModeErr)
    requires !observed.destination.ok && observed.source.ok && observed.source.value.isDir && observed.sourceModeOK ==>
               C.CreateDirectorySpec(before,now,provider.filesystem,mask,observed.created,target,Spec.ParentCreationMode(raw,observed.sourceMode),observed.createOK,observed.createErr)
    requires !observed.destination.ok && observed.source.ok && observed.source.value.isDir && observed.sourceModeOK && observed.createOK ==>
               Spec.MetadataFields(observed.created,provider,target,false,observed.createdMetadata)
    requires !observed.destination.ok && observed.source.ok && observed.source.value.isDir && observed.sourceModeOK && observed.createOK && observed.createdMetadata.ok ==>
               C.GetFileModeSpec(observed.created,provider.failures,target,false,observed.createdModeOK,observed.createdMode,observed.createdModeErr)
    requires !observed.destination.ok && observed.source.ok && observed.source.value.isDir && observed.sourceModeOK && observed.createOK && observed.createdMetadata.ok && observed.createdModeOK &&
             (observed.createdMode | (448 as bv32)) != observed.createdMode ==>
               C.SetFileModeSpec(observed.created,now,provider.failures,after,target,false,observed.createdMode | (448 as bv32),observed.changeOK,observed.changeErr)
    requires observed.destination.ok && !raw.policy.preserveMode && !raw.policy.preserveTimes ==>
               after == before && reported.0 == [] && reported.3 == [] &&
               reported.1 == (if observed.destination.value.isDir then [] else Spec.ParentNotDirectory(Spec.Q(target))) && reported.2 == observed.destination.value.isDir
    requires (!observed.destination.ok || raw.policy.preserveMode || raw.policy.preserveTimes) && (!observed.source.ok || !observed.source.value.isDir) ==>
               after == before && reported.0 == [] && reported.3 == [] && !reported.2 &&
               reported.1 == Spec.ParentAttributesError(Spec.Q(source),Spec.E(if observed.source.ok then 20 else observed.source.err))
    requires (!observed.destination.ok || raw.policy.preserveMode || raw.policy.preserveTimes) && observed.source.ok && observed.source.value.isDir && !observed.sourceModeOK ==>
               after == before && reported.0 == [] && reported.3 == [] && !reported.2 && reported.1 == Spec.ParentAttributesError(Spec.Q(source),Spec.E(observed.sourceModeErr))
    requires observed.destination.ok && (raw.policy.preserveMode || raw.policy.preserveTimes) && observed.source.ok && observed.source.value.isDir && observed.sourceModeOK ==>
               after == before && reported.0 == [] && reported.3 == [Spec.ParentInfo(source,target,observed.source,observed.sourceMode,false)] &&
               reported.1 == (if observed.destination.value.isDir then [] else Spec.ParentNotDirectory(Spec.Q(target))) && reported.2 == observed.destination.value.isDir
    requires !observed.destination.ok && observed.source.ok && observed.source.value.isDir && observed.sourceModeOK && !observed.createOK ==>
               after == observed.created && reported.0 == [] && reported.3 == [Spec.ParentInfo(source,target,observed.source,observed.sourceMode,false)] && !reported.2 &&
               reported.1 == Spec.ParentCreateError(Spec.Q(target),Spec.E(observed.createErr))
    requires !observed.destination.ok && observed.source.ok && observed.source.value.isDir && observed.sourceModeOK && observed.createOK ==>
               reported.0 == (if raw.policy.verbose then Spec.ParentVerbose(source,target) else [])
    requires !observed.destination.ok && observed.source.ok && observed.source.value.isDir && observed.sourceModeOK && observed.createOK && !observed.createdMetadata.ok ==>
               after == observed.created && reported.3 == [Spec.ParentInfo(source,target,observed.source,observed.sourceMode,false)] && !reported.2 &&
               reported.1 == Spec.ParentAttributesError(Spec.Q(target),Spec.E(observed.createdMetadata.err))
    requires !observed.destination.ok && observed.source.ok && observed.source.value.isDir && observed.sourceModeOK && observed.createOK && observed.createdMetadata.ok && !observed.createdModeOK ==>
               after == observed.created && reported.3 == [Spec.ParentInfo(source,target,observed.source,observed.sourceMode,false)] && !reported.2 &&
               reported.1 == Spec.ParentAttributesError(Spec.Q(target),Spec.E(observed.createdModeErr))
    requires !observed.destination.ok && observed.source.ok && observed.source.value.isDir && observed.sourceModeOK && observed.createOK && observed.createdMetadata.ok && observed.createdModeOK ==>
               reported.3 == [Spec.ParentInfo(source,target,observed.source,if raw.policy.preserveMode then observed.sourceMode else observed.createdMode,
                                              !raw.policy.preserveMode && (observed.createdMode & (448 as bv32)) != (448 as bv32))] &&
               reported.2 == observed.changeOK && reported.1 == (if reported.2 then [] else Spec.ParentSetModeError(Spec.Q(target),Spec.E(observed.changeErr))) &&
               ((observed.createdMode | (448 as bv32)) == observed.createdMode ==> after == observed.created && observed.changeOK && observed.changeErr == 0)
    ensures Spec.ParentStepFields(raw,source,target,before,after,now,mask,provider,reported.0,reported.1,reported.2,reported.3,observed)
  {
    hide *;
    reveal Spec.ParentStepFields();
  }

  method {:isolate_assertions} ParentStep(raw: S.CpCmdRaw, source: string, target: string, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool, records: seq<Spec.ParentInfo>)
    modifies io.fsRegion
    ensures Spec.ParentStep(raw,source,target,old(io.fs()),io.fs(),io.now(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),out,err,ok,records)
  {
    hide *;
    reveal Spec.ParentStep();
    ghost var before := io.fs();
    out,err,ok,records := [],[],true,[];
    var dm := Metadata(target,true,io);
    var sm := dm;
    var sourceMode,createdMode := 0 as bv32,0 as bv32;
    var sourceModeOK,sourceModeErr,createdModeOK,createdModeErr := true,0,true,0;
    var createOK,createErr,changeOK,changeErr := true,0,true,0;
    ghost var created := before;
    var createdMetadata := dm;
    if !dm.ok || raw.policy.preserveMode || raw.policy.preserveTimes {
      sm := Metadata(source,true,io);
      if !sm.ok || !sm.value.isDir {
        var q := Quoted(source,io);
        var reason := Reason(if sm.ok then 20 else sm.err,io);
        err,ok := Text.ParentAttributesError(q,reason),false;
      } else {
        var modeResult := io.GetFileMode(source,true);
        sourceModeOK,sourceModeErr := modeResult.Ok?,C.ResultErrno(modeResult);
        sourceMode := C.ResultValue(modeResult,0 as bv32);
        assert C.GetFileModeSpec(before,io.trustedNativeFailures(),source,true,sourceModeOK,sourceMode,sourceModeErr);
        if !sourceModeOK {
          var q := Quoted(source,io);
          var reason := Reason(sourceModeErr,io);
          err,ok := Text.ParentAttributesError(q,reason),false;
        } else {
          records := [Spec.ParentInfo(source,target,sm,sourceMode,false)];
          if dm.ok {
            if !dm.value.isDir {
              var q := Quoted(target,io);
              err,ok := Spec.ParentNotDirectory(q),false;
            }
          } else {
            var result := io.CreateDirectory(target,Spec.ParentCreationMode(raw,sourceMode));
            createOK,createErr := result.Ok?,C.ResultErrno(result);
            created := io.fs();
            assert C.CreateDirectorySpec(before,io.now(),io.trustedFilesystem(),io.umask(),created,target,Spec.ParentCreationMode(raw,sourceMode),createOK,createErr);
            if !createOK {
              var q := Quoted(target,io);
              var reason := Reason(createErr,io);
              err,ok := Text.ParentCreateError(q,reason),false;
            } else {
              out := if raw.policy.verbose then Text.ParentVerbose(source,target) else [];
              createdMetadata := Metadata(target,false,io);
              if !createdMetadata.ok {
                var q := Quoted(target,io);
                var reason := Reason(createdMetadata.err,io);
                err,ok := Text.ParentAttributesError(q,reason),false;
              } else {
                var modeResult := io.GetFileMode(target,false);
                createdModeOK,createdModeErr := modeResult.Ok?,C.ResultErrno(modeResult);
                createdMode := C.ResultValue(modeResult,0 as bv32);
                assert C.GetFileModeSpec(created,io.trustedNativeFailures(),target,false,createdModeOK,createdMode,createdModeErr);
                if !createdModeOK {
                  var q := Quoted(target,io);
                  var reason := Reason(createdModeErr,io);
                  err,ok := Text.ParentAttributesError(q,reason),false;
                } else {
                  var restore := !raw.policy.preserveMode && (createdMode & (448 as bv32)) != (448 as bv32);
                  records := [Spec.ParentInfo(source,target,sm,if raw.policy.preserveMode then sourceMode else createdMode,restore)];
                  if (createdMode | (448 as bv32)) != createdMode {
                    var changed := io.SetFileMode(target,false,createdMode | (448 as bv32));
                    changeOK,changeErr := changed.Ok?,C.ResultErrno(changed);
                    assert C.SetFileModeSpec(created,io.now(),io.trustedNativeFailures(),io.fs(),target,false,createdMode | (448 as bv32),changeOK,changeErr);
                    if !changeOK {
                      var q := Quoted(target,io);
                      var reason := Reason(changeErr,io);
                      err,ok := Text.ParentSetModeError(q,reason),false;
                    }
                  }
                }
              }
            }
          }
        }
      }
    } else if !dm.value.isDir {
      var q := Quoted(target,io);
      err,ok := Spec.ParentNotDirectory(q),false;
    }
    ghost var observed := Spec.ParentStepObservation(dm,sm,sourceMode,sourceModeOK,sourceModeErr,created,createOK,createErr,
                                                     createdMetadata,createdMode,createdModeOK,createdModeErr,io.fs(),changeOK,changeErr);
    ParentStepWitness(raw,source,target,before,io.fs(),io.now(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),(out,err,ok,records),observed);
  }

  method ComputeParentOffsets(path: string) returns (offsets: seq<nat>)
    ensures Spec.ParentOffsets(path,offsets)
  {
    offsets := [];
    var i := 0;
    while i < |path|
      invariant 0 <= i <= |path|
      invariant forall j | 0 <= j < |offsets| ::
                  0 < offsets[j] < i && path[offsets[j]] == '/' && path[offsets[j]-1] != '/'
      invariant forall j,k | 0 <= j < k < |offsets| :: offsets[j] < offsets[k]
      invariant forall index | 0 < index < i && path[index] == '/' && path[index-1] != '/' :: index in offsets
      modifies {}
      decreases |path|-i
    {
      if i > 0 && path[i] == '/' && path[i-1] != '/' { offsets := offsets+[i]; }
      i := i+1;
    }
    Proof.ParentOffsetsWitness(path,offsets);
  }

  method PrepareParents(raw: S.CpCmdRaw, source: string, directory: string, target: string, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool, records: seq<Spec.ParentInfo>)
    modifies io.fsRegion
    ensures Spec.ParentPreparation(raw,source,directory,target,old(io.fs()),io.fs(),io.now(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),out,err,ok,records)
  {
    hide *;
    reveal Spec.ParentPreparation(), Spec.ParentGroups();
    ghost var before := io.fs();
    var trimmed := Paths.TrimTrailingSlashes(source);
    Proof.TrimmedSummaryGivesRelation(source,trimmed);
    var offsets := ComputeParentOffsets(trimmed);
    reveal Spec.ParentOffsets();
    var parent := ".";
    var dm := Spec.Metadata(false,0,BW.FileTimeStatus(0,0,0,0,false,false,0,0,0));
    ghost var states := [io.fs()];
    ghost var outputs: seq<BW.Bytes> := [];
    ghost var errors: seq<BW.Bytes> := [];
    ghost var results: seq<bool> := [];
    ghost var groups: seq<seq<Spec.ParentInfo>> := [];
    ghost var targets: seq<string> := [];
    ghost var outputOffsets: seq<nat> := [0];
    ghost var errorOffsets: seq<nat> := [0];
    out,err,ok,records := [],[],true,[];
    if raw.policy.creation.parents && |offsets| > 0 {
      parent := Paths.ComputeDirnameValue(target);
      PathProof.DirnameValueSummaryGivesRelation(target,parent);
      dm := Metadata(parent,true,io);
      if dm.ok {
        if !dm.value.isDir {
          var q := Quoted(parent,io);
          err,ok := Spec.ParentNotDirectory(q),false;
        }
      } else {
        assert Spec.BlockOffsets(errors,err,errorOffsets) by { reveal Spec.BlockOffsets(); }
        assert Spec.BlockOffsets(outputs,out,outputOffsets) by { reveal Spec.BlockOffsets(); }
        var i := 0;
        while i < |offsets| && ok
          invariant Spec.ParentOffsets(trimmed,offsets)
          invariant 0 <= i <= |offsets|
          invariant |states| == i+1 && states[0] == before && states[i] == io.fs()
          invariant |outputs| == i && |errors| == i && |results| == i && |groups| == i && |targets| == i
          invariant forall j | 0 <= j < i ::
                      Spec.ParentsTargetFields(directory,trimmed[..offsets[j]],targets[j]) &&
                      Spec.ParentStep(raw,trimmed[..offsets[j]],targets[j],states[j],states[j+1],io.now(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),outputs[j],errors[j],results[j],groups[j])
          invariant forall j | 0 <= j < i-1 :: results[j]
          invariant i == 0 || ok == results[i-1]
          invariant ok == (forall j | 0 <= j < i :: results[j])
          invariant records == Spec.ParentGroups(groups)
          invariant |outputOffsets| == i+1 && outputOffsets[0] == 0 && outputOffsets[i] == |out|
          invariant |errorOffsets| == i+1 && errorOffsets[0] == 0 && errorOffsets[i] == |err|
          invariant Spec.BlockOffsets(outputs,out,outputOffsets) && Spec.BlockOffsets(errors,err,errorOffsets)
          modifies io.fsRegion
          decreases |offsets|-i
        {
          var src := trimmed[..offsets[i]];
          var destination := ParentsTarget(directory,src);
          var stepOut,stepErr,stepOK,stepRecords := ParentStep(raw,src,destination,io);
          AppendBlocks(outputs,out,outputOffsets,stepOut);
          AppendBlocks(errors,err,errorOffsets,stepErr);
          AllTrueAppend(results,stepOK);
          states := states + [io.fs()];
          outputs,errors,results,groups,targets := outputs+[stepOut],errors+[stepErr],results+[stepOK],groups+[stepRecords],targets+[destination];
          out,err,ok,records := out+stepOut,err+stepErr,stepOK,records+stepRecords;
          outputOffsets,errorOffsets := outputOffsets+[|out|],errorOffsets+[|err|];
          i := i+1;
        }
        assert Spec.Concatenation(outputs,out) by { reveal Spec.Concatenation(); }
        assert Spec.Concatenation(errors,err) by { reveal Spec.Concatenation(); }
      }
    }
    assert Spec.ParentPreparationFields(raw,source,directory,target,before,io.fs(),io.now(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),
                                        (out,err,ok,records),(trimmed,parent,dm,states,outputs,errors,results,groups,targets,offsets)) by {
      hide *;
      reveal Spec.ParentPreparationFields();
    }
  }

  method RestoreParent(raw: S.CpCmdRaw, parent: Spec.ParentInfo, io: BenchIO.IO) returns (err: BW.Bytes, ok: bool)
    modifies io.fsRegion
    ensures Spec.ParentRestoreOne(raw,parent,old(io.fs()),io.fs(),io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),err,ok)
  {
    hide *;
    reveal Spec.ParentRestoreOne();
    ghost var before := io.fs();
    var timeOK,timeErr,modeOK,modeErr := true,0,true,0;
    if raw.policy.preserveTimes {
      var result := io.SetFileTimes(parent.target,true,parent.metadata.value.atimeSec,parent.metadata.value.atimeNsec,
                                    parent.metadata.value.mtimeSec,parent.metadata.value.mtimeNsec);
      timeOK,timeErr := result.Ok?,C.ResultErrno(result);
    }
    ghost var middle := io.fs();
    err,ok := [],timeOK;
    if !timeOK {
      var q := Quoted(parent.target,io);
      var reason := Reason(timeErr,io);
      err := Text.ParentTimeError(q,reason);
    } else if raw.policy.preserveMode || parent.restore {
      var result := io.SetFileMode(parent.target,true,parent.mode);
      modeOK,modeErr := result.Ok?,C.ResultErrno(result);
      ok := modeOK;
      if !modeOK {
        var q := Quoted(parent.target,io);
        var reason := Reason(modeErr,io);
        err := if raw.policy.preserveMode then Text.ModeError(q,reason) else Text.ParentModeError(q,reason);
      }
    }
    assert Spec.ParentRestoreOneFields(raw,parent,before,io.fs(),io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),err,ok,(middle,timeOK,timeErr,modeOK,modeErr)) by {
      hide *;
      reveal Spec.ParentRestoreOneFields();
    }
  }

  method RestoreParents(raw: S.CpCmdRaw, records: seq<Spec.ParentInfo>, io: BenchIO.IO) returns (err: BW.Bytes, ok: bool)
    modifies io.fsRegion
    ensures Spec.ParentRestoration(raw,records,old(io.fs()),io.fs(),io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),err,ok)
  {
    hide *;
    reveal Spec.ParentRestoration();
    ghost var before := io.fs();
    ghost var states := [io.fs()];
    ghost var errors: seq<BW.Bytes> := [];
    ghost var results: seq<bool> := [];
    ghost var errorOffsets: seq<nat> := [0];
    err,ok := [],true;
    assert Spec.BlockOffsets(errors,err,errorOffsets) by { reveal Spec.BlockOffsets(); }
    var i := 0;
    while i < |records| && ok
      invariant 0 <= i <= |records|
      invariant |states| == i+1 && states[0] == before && states[i] == io.fs()
      invariant |errors| == i && |results| == i
      invariant forall j | 0 <= j < i :: Spec.ParentRestoreOne(raw,records[|records|-1-j],states[j],states[j+1],io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),errors[j],results[j])
      invariant forall j | 0 <= j < i-1 :: results[j]
      invariant i == 0 || ok == results[i-1]
      invariant ok == (forall j | 0 <= j < i :: results[j])
      invariant |errorOffsets| == i+1 && errorOffsets[0] == 0 && errorOffsets[i] == |err|
      invariant Spec.BlockOffsets(errors,err,errorOffsets)
      modifies io.fsRegion
      decreases |records|-i
    {
      var stepErr,stepOK := RestoreParent(raw,records[|records|-1-i],io);
      AppendBlocks(errors,err,errorOffsets,stepErr);
      AllTrueAppend(results,stepOK);
      states,errors,results := states+[io.fs()],errors+[stepErr],results+[stepOK];
      err,ok := err+stepErr,stepOK;
      errorOffsets := errorOffsets+[|err|];
      i := i+1;
    }
    assert Spec.Concatenation(errors,err) by { reveal Spec.Concatenation(); }
    assert Spec.ParentRestorationFields(raw,records,before,io.fs(),io.now(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),err,ok,(states,errors,results)) by {
      hide *;
      reveal Spec.ParentRestorationFields();
    }
  }

  method SeenDestination(target: string, meta: Spec.Metadata, seen: Spec.SeenDestinations, io: BenchIO.IO) returns (result: bool)
    ensures Spec.SeenDestination(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),target,meta,seen,result)
  {
    hide *;
    reveal Spec.SeenDestination();
    var matches: seq<bool> := [];
    result := false;
    var i := 0;
    while i < |seen|
      invariant 0 <= i <= |seen| && |matches| == i
      invariant forall j | 0 <= j < i ::
                  if meta.ok && (meta.value.device,meta.value.inode) == (seen[j].1,seen[j].2) then Spec.SameEntryFields(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),target,seen[j].0,matches[j])
                  else !matches[j]
      invariant result == (exists j | 0 <= j < i :: matches[j])
      modifies {}
      decreases |seen|-i
    {
      var same := false;
      if meta.ok && (meta.value.device,meta.value.inode) == (seen[i].1,seen[i].2) { same := SameEntry(target,seen[i].0,io); }
      matches := matches+[same];
      result := result || same;
      i := i+1;
    }
    assert Spec.SeenDestinationFields(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),target,meta,seen,result,matches) by {
      hide *;
      reveal Spec.SeenDestinationFields();
    }
  }

  method RepeatedSource(raw: S.CpCmdRaw, tree: Spec.SourceTree, target: string, previous: seq<Spec.SourceTree>, known: Spec.LinkMap, io: BenchIO.IO)
    returns (repeated: bool)
    ensures Spec.RepeatedSource(raw,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),tree,target,previous,known,repeated)
  {
    hide *;
    reveal Spec.RepeatedSource();
    var matches: seq<bool> := [];
    repeated := false;
    if tree.DirectorySource? && Spec.Identity(tree.metadata) in known {
      repeated := SameEntry(target,known[Spec.Identity(tree.metadata)],io);
    } else if tree.FileSource? && Spec.BackupMode(raw) == "off" {
      var i := 0;
      while i < |previous|
        invariant 0 <= i <= |previous| && |matches| == i
        invariant forall j | 0 <= j < i ::
                    if previous[j].FileSource? && Spec.Identity(tree.metadata) == Spec.Identity(previous[j].metadata) then
                      Spec.SameEntryFields(io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),tree.path,previous[j].path,matches[j])
                    else !matches[j]
        invariant repeated == (exists j | 0 <= j < i :: matches[j])
        modifies {}
        decreases |previous|-i
      {
        var same := false;
        if previous[i].FileSource? && Spec.Identity(tree.metadata) == Spec.Identity(previous[i].metadata) {
          same := SameEntry(tree.path,previous[i].path,io);
        }
        matches := matches+[same];
        repeated := repeated || same;
        i := i+1;
      }
    }
    assert Spec.RepeatedSourceFields(raw,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),tree,target,previous,known,repeated,matches) by {
      hide *;
      reveal Spec.RepeatedSourceFields();
    }
  }

  method DestinationGuard(raw: S.CpCmdRaw, tree: Spec.SourceTree, target: string, seen: Spec.SeenDestinations, io: BenchIO.IO)
    returns (guard: Spec.DestinationGuardResult)
    ensures Spec.DestinationGuard(raw,tree,target,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),seen,guard)
  {
    hide *;
    reveal Spec.DestinationGuard();
    var tm,entry := tree.metadata,tree.metadata;
    var mayCopy,same,seenTarget,seenEntry := false,false,false,false;
    guard := Spec.GuardContinue;
    if tree.FileSource? || tree.DirectorySource? {
      tm := Metadata(target,Spec.FollowDestination(raw,tree),io);
      if tree.FileSource? && Spec.Skip(raw,tree.metadata,tm) { mayCopy := false; }
      else if tm.ok && Spec.Identity(tree.metadata) == Spec.Identity(tm) {
        if tree.FileSource? && !raw.policy.hard &&
           (raw.policy.remove || Spec.BackupMode(raw) != "off" || (tree.metadata.value.isSymlink && tm.value.isSymlink)) {
          same := SameEntry(tree.path,target,io);
          mayCopy := !same && !(tree.metadata.value.isSymlink && tm.value.isSymlink && Spec.BackupMode(raw) == "off");
        }
      } else { mayCopy := !(tm.ok && tree.FileSource? != !tm.value.isDir && Spec.BackupMode(raw) == "off"); }
      assert Spec.MayCopyFields(raw,tree,target,tm,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),mayCopy,same) by {
        hide *;
        reveal Spec.MayCopyFields();
      }
      if mayCopy {
        if tm.ok && !tm.value.isDir && Spec.BackupMode(raw) != "numbered" { seenTarget := SeenDestination(target,tm,seen,io); }
        if seenTarget {
          var qs := Quoted(tree.path,io);
          var qt := Quoted(target,io);
          guard := Spec.GuardStop(Spec.JustCreated(qt,qs));
        } else if Spec.BackupMode(raw) == "off" && !Spec.PreUnlink(raw,tree.metadata,tm) {
          entry := Metadata(target,false,io);
          if entry.ok && entry.value.isSymlink { seenEntry := SeenDestination(target,entry,seen,io); }
          if seenEntry {
            var qs := Quoted(tree.path,io);
            var qt := Quoted(target,io);
            guard := Spec.GuardStop(Spec.JustCreatedSymlink(qt,qs));
          }
        }
      }
    }
    assert Spec.DestinationGuardFields(raw,tree,target,io.fs(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),seen,guard,
                                       Spec.DestinationGuardObservation(tm,entry,mayCopy,same,seenTarget,seenEntry)) by {
      hide *;
      reveal Spec.DestinationGuardFields();
    }
  }

  method CopyOperand(raw: S.CpCmdRaw, source: string, target: string, directory: bool,
                     previous: seq<string>, previousTrees: seq<Spec.SourceTree>, known: Spec.LinkMap, previousSeen: Spec.SeenDestinations, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool, tree: Spec.SourceTree, links: Spec.LinkMap, seen: Spec.SeenDestinations)
    modifies io.fsRegion,io.dirHandlesRegion
    ensures Spec.Operand(raw,source,target,directory,io.cwd(),(old(io.fs()),io.fs()),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                         (out,err,ok,tree),(previous,previousTrees,known,links,previousSeen,seen))
    ensures io.dirHandles() == old(io.dirHandles())
  {
    hide *;
    reveal Spec.Operand();
    ghost var before := io.fs();
    links,seen := known,previousSeen;
    ghost var rootLinks := known;
    var destination := target;
    if directory {
      if raw.policy.creation.parents { destination := ParentsTarget(target,source); }
      else { destination := Target(target,source); }
    }
    var parentOut,parentErr,parentOK,parents := PrepareParents(raw,source,target,destination,io);
    ghost var prepared := io.fs();
    var copyOut: BW.Bytes := [];
    var copyErr: BW.Bytes := [];
    var copyOK := true;
    var record := Spec.CopyReceipt(Spec.NoDestinationRecord,false,false);
    var repeated := false;
    var guard := Spec.GuardContinue;
    var restoreErr: BW.Bytes := [];
    var restoreOK := true;
    ghost var copied := prepared;
    tree := Spec.UncopiedSource(source);
    if !parentOK { out,err,ok := parentOut,parentErr,false; }
    else {
      tree := Discover(raw,source,{},0,io);
      repeated := RepeatedSource(raw,tree,destination,previousTrees,links,io);
      if repeated {
        var q := Quoted(source,io);
        copyErr := if tree.DirectorySource? then Spec.DuplicateDirectory(q) else Spec.Duplicate(q);
      } else {
        guard := DestinationGuard(raw,tree,destination,seen,io);
        if guard.GuardStop? { copyErr,copyOK := guard.error,false; }
        else { copyOut,copyErr,copyOK,links,record := CopyRoot(raw,tree,destination,links,io); }
      }
      rootLinks := links;
      links := Spec.RememberDirectory(tree,destination,record,links);
      seen := Spec.RememberDestination(seen,destination,record);
      copied := io.fs();
      restoreErr,restoreOK := RestoreParents(raw,parents,io);
      out,err,ok := parentOut+copyOut,parentErr+copyErr+restoreErr,copyOK && restoreOK;
    }
    assert Spec.OperandFields(raw,source,target,directory,io.cwd(),(before,io.fs()),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                              (out,err,ok,tree),(previous,previousTrees,known,links,previousSeen,seen),
                              Spec.OperandObservation(destination,prepared,parentOut,parentErr,parentOK,parents,copied,copyOut,copyErr,copyOK,restoreErr,restoreOK,record,repeated,guard,rootLinks)) by {
      hide *;
      reveal Spec.OperandFields();
    }
  }

  method CopyBatch(raw: S.CpCmdRaw, sources: seq<string>, target: string, directory: bool, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool)
    modifies io.fsRegion,io.dirHandlesRegion
    ensures Spec.Batch(raw,sources,target,directory,io.cwd(),old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),
                       io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok)
    ensures io.dirHandles() == old(io.dirHandles())
  {
    hide *;
    reveal Spec.Batch(), Spec.BatchOutcome();
    var links: Spec.LinkMap := map[];
    var seen: Spec.SeenDestinations := [];
    ghost var seens := [seen];
    ghost var before := io.fs();
    ghost var maps := [links];
    ghost var states := [io.fs()];
    var trees: seq<Spec.SourceTree> := [];
    ghost var outputs: seq<BW.Bytes> := [];
    ghost var errors: seq<BW.Bytes> := [];
    ghost var results: seq<bool> := [];
    ghost var outputOffsets: seq<nat> := [0];
    ghost var errorOffsets: seq<nat> := [0];
    out,err,ok := [],[],true;
    assert Spec.BlockOffsets(errors,err,errorOffsets) by { reveal Spec.BlockOffsets(); }
    assert Spec.BlockOffsets(outputs,out,outputOffsets) by { reveal Spec.BlockOffsets(); }
    var i := 0;
    while i < |sources|
      invariant |seens| == i+1 && seens[0] == [] && seens[i] == seen
      invariant |maps| == i+1 && maps[i] == links
      invariant maps[0] == map[]
      invariant 0 <= i <= |sources|
      invariant |states| == i+1 && states[0] == old(io.fs()) && states[i] == io.fs()
      invariant |trees| == i && |outputs| == i && |errors| == i && |results| == i
      invariant (forall j {:trigger trees[j]} | 0 <= j < i ::
                   Spec.Operand(raw,sources[j],target,directory,io.cwd(),(states[j],states[j+1]),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                                (outputs[j],errors[j],results[j],trees[j]),(sources[..j],trees[..j],maps[j],maps[j+1],seens[j],seens[j+1])))
      invariant |outputOffsets| == i+1 && outputOffsets[0] == 0 && outputOffsets[i] == |out|
      invariant |errorOffsets| == i+1 && errorOffsets[0] == 0 && errorOffsets[i] == |err|
      invariant Spec.BlockOffsets(outputs,out,outputOffsets)
      invariant Spec.BlockOffsets(errors,err,errorOffsets)
      invariant ok == (forall j {:trigger results[j]} | 0 <= j < i :: results[j])
      invariant io.dirHandles() == old(io.dirHandles())
      modifies io.fsRegion,io.dirHandlesRegion
      decreases |sources|-i
    {
      ghost var previousI := i;
      ghost var previousStates,previousTrees,previousOutputs,previousErrors,previousResults,previousMaps,previousSeens := states,trees,outputs,errors,results,maps,seens;
      ghost var beforeSource := io.fs();
      var childOut: BW.Bytes;
      var childErr: BW.Bytes;
      var childOK: bool;
      var tree: Spec.SourceTree;
      childOut,childErr,childOK,tree,links,seen := CopyOperand(raw,sources[i],target,directory,sources[..i],trees,links,seen,io);
      AppendBlocks(outputs,out,outputOffsets,childOut);
      AppendBlocks(errors,err,errorOffsets,childErr);
      AllTrueAppend(results,childOK);
      maps := maps + [links];
      seens := seens+[seen];
      states := states + [io.fs()];
      trees := trees + [tree];
      outputs := outputs + [childOut];
      errors := errors + [childErr];
      results := results + [childOK];
      out,err,ok := out + childOut,err + childErr,ok && childOK;
      outputOffsets := outputOffsets + [|out|];
      errorOffsets := errorOffsets + [|err|];
      i := i+1;
      assert forall j {:trigger trees[j]} | 0 <= j < i ::
          Spec.Operand(raw,sources[j],target,directory,io.cwd(),(states[j],states[j+1]),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                       (outputs[j],errors[j],results[j],trees[j]),(sources[..j],trees[..j],maps[j],maps[j+1],seens[j],seens[j+1])) by {
        hide *;
        forall j {:trigger trees[j]} | 0 <= j < i
          ensures Spec.Operand(raw,sources[j],target,directory,io.cwd(),(states[j],states[j+1]),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                               (outputs[j],errors[j],results[j],trees[j]),(sources[..j],trees[..j],maps[j],maps[j+1],seens[j],seens[j+1]))
        {
          if j < previousI {
            assert trees[j] == previousTrees[j] && trees[..j] == previousTrees[..j];
            assert states[j] == previousStates[j] && states[j+1] == previousStates[j+1];
            assert outputs[j] == previousOutputs[j] && errors[j] == previousErrors[j] && results[j] == previousResults[j];
            assert maps[j] == previousMaps[j] && maps[j+1] == previousMaps[j+1];
            assert seens[j] == previousSeens[j] && seens[j+1] == previousSeens[j+1];
          } else {
            assert j == previousI;
            assert trees[j] == tree && trees[..j] == previousTrees;
            assert states[j] == beforeSource;
          }
        }
      }
    }
    assert Spec.Concatenation(outputs,out) by { reveal Spec.Concatenation(); }
    assert Spec.Concatenation(errors,err) by { reveal Spec.Concatenation(); }
    assert Spec.BatchOutcome(raw,sources,target,directory,io.cwd(),before,io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                             (out,err,ok),(states,trees,outputs,errors,results,seq(|sources|, i => target),maps,seens)) by {
      hide *;
      reveal Spec.BatchOutcome();
    }
  }

  method CopySingle(raw: S.CpCmdRaw, source: string, target: string, tm: Spec.Metadata, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool)
    modifies io.fsRegion,io.dirHandlesRegion
    ensures io.dirHandles() == old(io.dirHandles())
    ensures Spec.SingleTarget(raw,source,target,tm,io.cwd(),old(io.fs()),io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok)
  {
    hide *;
    reveal Spec.SingleTarget();
    ghost var before := io.fs();
    var selected,selectionErr := "",0;
    if Spec.SpecialSourceBackup(raw,source,target,tm) {
      selected,selectionErr := BackupName(target,Spec.BackupMode(raw),Spec.BackupSuffix(raw),io);
      if selectionErr != 0 { out,err,ok := [],Spec.MemoryExhausted(),false; }
      else { out,err,ok := CopyBatch(Spec.WithoutBackup(raw),[source],selected,false,io); }
    } else { out,err,ok := CopyBatch(raw,[source],target,false,io); }
    assert Spec.SingleTargetFields(raw,source,target,tm,io.cwd(),before,io.fs(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                                   (out,err,ok),(selected,selectionErr)) by {
      hide *;
      reveal Spec.SingleTargetFields();
    }
  }

  method EnvironmentValue(key: string, io: BenchIO.IO) returns (value: string)
    ensures value == Spec.EnvironmentValue(io.env(),key)
  {
    var result := io.GetEnv(key);
    reveal C.GetEnvSpec(), C.GetEnvContractFields();
    value := if result.Ok? then result.v else "";
  }

  method Configure(raw: S.CpCmdRaw, io: BenchIO.IO) returns (ready: S.CpCmdRaw)
    ensures ready == Spec.EnvironmentCommand(raw,io.env())
  {
    var posix := io.GetEnv("POSIXLY_CORRECT");
    reveal C.GetEnvSpec(), C.GetEnvContractFields();
    var starting := raw.(policy := raw.policy.(creation := raw.policy.creation.(writeDangling := posix.Ok?)));
    if raw.mode != S.Run || raw.error != S.NoError || !raw.policy.creation.backup.enabled { return starting; }
    var version := EnvironmentValue("VERSION_CONTROL",io);
    var suffix := EnvironmentValue("SIMPLE_BACKUP_SUFFIX",io);
    ready := Spec.ConfigureBackup(starting,version,suffix);
  }

  method Command(raw: S.CpCmdRaw, io: BenchIO.IO) returns (out: BW.Bytes, err: BW.Bytes, ok: bool)
    modifies io.fsRegion,io.dirHandlesRegion
    ensures Spec.Command(raw,old(io.fs()),io.fs(),io.cwd(),io.env(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok)
    ensures io.dirHandles() == old(io.dirHandles())
  {
    hide *;
    reveal Spec.Command();
    var ready := Configure(raw,io);
    out,err,ok := NormalizedCommand(ready,io);
  }

  method NormalizedCommand(raw: S.CpCmdRaw, io: BenchIO.IO)
    returns (out: BW.Bytes, err: BW.Bytes, ok: bool)
    modifies io.fsRegion,io.dirHandlesRegion
    ensures Spec.NormalizedCommand(raw,old(io.fs()),io.fs(),io.cwd(),io.props(),io.now(),io.credentials(),io.umask(),
                                   Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok)
    ensures io.dirHandles() == old(io.dirHandles())
  {
    hide *;
    reveal Spec.NormalizedCommand(), Spec.CommandOutcome();
    ghost var before := io.fs();
    if raw.mode == S.Help { return Spec.HelpText(),[],true; }
    if raw.mode == S.Version { return Spec.VersionText(),[],true; }
    if raw.error != S.NoError { return [],Text.ConfigurationDiagnostic(raw.error),false; }
    if |raw.operands| == 0 { return [],Spec.Missing(),false; }
    if raw.target.None? && |raw.operands| == 1 {
      var q := Quoted(raw.operands[0],io);
      return [],Spec.MissingDestination(q),false;
    }
    if raw.noTarget && |raw.operands| > 2 {
      var q := io.QuoteArgument(Utf8.Encode(raw.operands[2]));
      return [],Spec.Extra(q),false;
    }
    var target := if raw.target.Some? then raw.target.value else raw.operands[|raw.operands|-1];
    var sources := if raw.target.Some? then raw.operands else raw.operands[..|raw.operands|-1];
    var tm := Metadata(target,true,io);
    if raw.target.Some? || |sources| > 1 {
      if !tm.ok || !tm.value.isDir {
        var q := Quoted(target,io);
        var reason := Reason(if tm.ok then 20 else tm.err,io);
        assert Spec.CommandOutcome(raw,before,io.fs(),io.cwd(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),
                                   [],(if raw.target.Some? then Spec.DirectoryError(q,reason) else Spec.TargetError(q,reason)),false,tm);
        return [],(if raw.target.Some? then Text.DirectoryError(q,reason) else Text.TargetError(q,reason)),false;
      }
      out,err,ok := CopyBatch(raw,sources,target,true,io);
    } else {
      if raw.policy.creation.parents && (raw.noTarget || !tm.ok || !tm.value.isDir) {
        assert Spec.CommandOutcome(raw,before,io.fs(),io.cwd(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),[],Spec.ParentsRequireDirectory(),false,tm);
        return [],Spec.ParentsRequireDirectory(),false;
      }
      if !raw.noTarget && tm.ok && tm.value.isDir { out,err,ok := CopyBatch(raw,sources,target,true,io); }
      else {
        assert |sources| == 1;
        out,err,ok := CopySingle(raw,sources[0],target,tm,io);
      }
    }
    assert Spec.CommandOutcome(raw,before,io.fs(),io.cwd(),io.props(),io.now(),io.credentials(),io.umask(),Spec.FilesystemProvider(io.trustedFilesystem(),io.trustedNativeFailures()),io.trustedStreams(),out,err,ok,tm);
  }

  twostate predicate CoreSummary(raw: S.CpCmdRaw, io: BenchIO.IO, exit: int)
    reads io.fsRegion,io.dirHandlesRegion,io.propsRegion,io.nowRegion,io.credentialsRegion,
          io.umaskRegion,io.cwdRegion,io.envRegion,io.trustedFilesystemRegion,io.trustedNativeFailuresRegion,io.trustedStreamsRegion,io.stdoutRegion,io.stderrRegion
  { Spec.Spec(raw,io,exit) }

  method RunCore(raw: S.CpCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion,io.dirHandlesRegion,io.stdoutRegion,io.stderrRegion
    ensures CoreSummary(raw,io,exit)
    ensures Spec.Spec(raw,io,exit)
  {
    hide *;
    reveal CoreSummary(), Spec.Spec(), Spec.Concatenation();
    ghost var beforeOut,beforeErr := io.stdout(),io.stderr();
    var out,err,ok := Command(raw,io);
    ghost var originalErr := err;
    reveal Spec.Published(), Spec.PublishedOutcome();
    var writeErr := 0;
    var committed: nat := 0;
    if |out| != 0 {
      var result := io.WriteStdout(out);
      writeErr := C.ResultErrno(result);
      committed := C.WriteResultCommitted(result);
    }
    assert (if |out| == 0 then io.stdout() == beforeOut && committed == 0 && writeErr == 0
            else C.WriteStdoutSpec(beforeOut,io.trustedStreams(),io.stdout(),out,committed,writeErr));
    if writeErr != 0 {
      var reason := Reason(writeErr,io);
      err := err + Text.StdoutError(reason);
    }
    assert err == originalErr + (if writeErr == 0 then [] else Spec.StdoutError(Spec.E(writeErr)));
    var stderrErr := 0;
    var stderrCommitted: nat := 0;
    if |err| != 0 {
      var result := io.WriteStderr(err);
      stderrErr := C.ResultErrno(result);
      stderrCommitted := C.WriteResultCommitted(result);
    }
    assert (if |err| == 0 then io.stderr() == beforeErr && stderrCommitted == 0 && stderrErr == 0
            else C.WriteStderrSpec(beforeErr,io.trustedStreams(),io.stderr(),err,stderrCommitted,stderrErr));
    assert (if |out| == 0 then io.stdout() == beforeOut && committed == 0 && writeErr == 0
            else C.WriteStdoutSpec(beforeOut,io.trustedStreams(),io.stdout(),out,committed,writeErr));
    exit := if ok && writeErr == 0 && stderrErr == 0 then 0 else 1;
    assert Spec.PublishedOutcome(beforeOut,beforeErr,io.stdout(),io.stderr(),io.trustedStreams(),out,originalErr,ok,exit,
                                 (committed,writeErr,stderrCommitted,stderrErr)) by {
      hide *;
      reveal Spec.PublishedOutcome();
    }
    assert Spec.Published(beforeOut,beforeErr,io.stdout(),io.stderr(),io.trustedStreams(),out,originalErr,ok,exit) by {
      hide *;
      reveal Spec.Published();
    }
    assert CoreSummary(raw,io,exit) by {
      hide *;
      reveal CoreSummary(), Spec.Spec();
    }
  }
}
