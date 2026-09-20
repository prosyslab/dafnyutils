
module MvPathCore {

  ghost predicate BasenameValueSummary(path: string, value: string)
  {
    if |path| == 0 then
      value == ""
    else if forall i :: 0 <= i < |path| ==> path[i] == '/' then
      value == "/"
    else
      exists trimEnd: int {:trigger TrimEndSummary(path, trimEnd)} ::
        TrimEndSummary(path, trimEnd) &&
        exists start: int {:trigger BasenameSegmentSummary(path, start, trimEnd, value)} ::
          BasenameSegmentSummary(path, start, trimEnd, value)
  }

  ghost predicate TrimEndSummary(path: string, trimEnd: int)
  {
    0 < trimEnd <= |path| &&
    (forall i :: trimEnd <= i < |path| ==> path[i] == '/') &&
    path[trimEnd - 1] != '/'
  }

  ghost predicate BasenameSegmentSummary(path: string, start: int, trimEnd: int, value: string)
  {
    0 <= start < trimEnd <= |path| &&
    (start == 0 || (0 < start && path[start - 1] == '/')) &&
    (forall i :: start <= i < trimEnd ==> path[i] != '/') &&
    value == path[start..trimEnd]
  }

  method ComputeBasenameValue(path: string) returns (value: string)
    ensures BasenameValueSummary(path, value)
    decreases *
  {
    if |path| == 0 {
      value := "";
      return;
    }

    var trimEnd := |path|;
    while 0 < trimEnd && path[trimEnd - 1] == '/'
      invariant 0 <= trimEnd <= |path|
      invariant forall i {:trigger path[i]} :: trimEnd <= i < |path| ==> path[i] == '/'
      decreases trimEnd
    {
      trimEnd := trimEnd - 1;
    }

    if trimEnd == 0 {
      value := "/";
      assert forall i {:trigger path[i]} :: 0 <= i < |path| ==> path[i] == '/';
      assert BasenameValueSummary(path, value);
      return;
    }

    var start := trimEnd - 1;
    while 0 < start && path[start - 1] != '/'
      invariant 0 <= start < trimEnd
      invariant forall i {:trigger path[i]} :: start <= i < trimEnd ==> path[i] != '/'
      decreases start
    {
      start := start - 1;
    }

    value := path[start..trimEnd];
    assert path[trimEnd - 1] != '/';
    assert TrimEndSummary(path, trimEnd);
    assert BasenameSegmentSummary(path, start, trimEnd, value);
    assert BasenameValueSummary(path, value);
  }

  ghost predicate TrimmedSummary(path: string, trimmed: string)
  {
    if |path| == 0 then
      trimmed == ""
    else if forall i :: 0 <= i < |path| ==> path[i] == '/' then
      trimmed == "/"
    else
      exists end: int ::
        0 < end <= |path| &&
        trimmed == path[..end] &&
        path[end - 1] != '/' &&
        forall i :: end <= i < |path| ==> path[i] == '/'
  }

  ghost predicate LastSlashSummary(path: string, limit: int, slash: int)
    requires 0 <= limit <= |path|
  {
    -1 <= slash < limit &&
    (slash == -1 ==> forall i :: 0 <= i < limit ==> path[i] != '/') &&
    (0 <= slash ==> path[slash] == '/' && forall i :: slash < i < limit ==> path[i] != '/')
  }

  ghost predicate DirnameValueSummary(path: string, value: string)
  {
    if |path| == 0 then
      value == "."
    else
      exists trimmed: string ::
        TrimmedSummary(path, trimmed) &&
        if trimmed == "/" then
          value == "/"
        else
          exists slash: int ::
            LastSlashSummary(trimmed, |trimmed|, slash) &&
            if slash == -1 then
              value == "."
            else if slash == 0 then
              value == "/"
            else
              TrimmedSummary(trimmed[..slash], value)
  }

  method ComputeDirnameValue(path: string) returns (value: string)
    ensures DirnameValueSummary(path, value)
    decreases *
  {
    if |path| == 0 {
      value := ".";
      return;
    }

    var trimmed := TrimTrailingSlashes(path);
    if trimmed == "/" {
      value := "/";
      assert TrimmedSummary(path, trimmed);
      assert DirnameValueSummary(path, value);
      return;
    }

    var slash := LastSlashIndex(trimmed, |trimmed|);
    if slash < 0 {
      value := ".";
      assert TrimmedSummary(path, trimmed);
      assert LastSlashSummary(trimmed, |trimmed|, slash);
      assert DirnameValueSummary(path, value);
      return;
    }

    if slash == 0 {
      value := "/";
      assert TrimmedSummary(path, trimmed);
      assert LastSlashSummary(trimmed, |trimmed|, slash);
      assert DirnameValueSummary(path, value);
      return;
    }

    value := TrimTrailingSlashes(trimmed[..slash]);
    assert TrimmedSummary(path, trimmed);
    assert LastSlashSummary(trimmed, |trimmed|, slash);
    assert TrimmedSummary(trimmed[..slash], value);
    assert DirnameValueSummary(path, value);
  }

  method TrimTrailingSlashes(path: string) returns (trimmed: string)
    ensures TrimmedSummary(path, trimmed)
    decreases *
  {
    if |path| == 0 {
      trimmed := "";
      return;
    }

    var allSlash := true;
    var i := 0;
    while i < |path|
      invariant 0 <= i <= |path|
      invariant allSlash ==> forall j :: 0 <= j < i ==> path[j] == '/'
      invariant !allSlash ==> exists j :: 0 <= j < i && path[j] != '/'
      decreases |path| - i
    {
      if path[i] != '/' {
        allSlash := false;
      }
      i := i + 1;
    }

    if allSlash {
      trimmed := "/";
      return;
    }

    var end := |path|;
    while 0 < end && path[end - 1] == '/'
      invariant 0 < end <= |path|
      invariant forall j :: end <= j < |path| ==> path[j] == '/'
      invariant exists j :: 0 <= j < end && path[j] != '/'
      decreases end
    {
      end := end - 1;
    }

    trimmed := path[..end];
  }

  method LastSlashIndex(path: string, limit: int) returns (slash: int)
    requires 0 <= limit <= |path|
    ensures LastSlashSummary(path, limit, slash)
    decreases *
  {
    slash := -1;
    var i := limit;
    while 0 < i && slash == -1
      invariant 0 <= i <= limit
      invariant -1 <= slash < limit
      invariant slash == -1 ==> forall j :: i <= j < limit ==> path[j] != '/'
      invariant 0 <= slash ==> path[slash] == '/'
      invariant 0 <= slash ==> forall j :: slash < j < limit ==> path[j] != '/'
      decreases i
    {
      i := i - 1;
      if path[i] == '/' {
        assert forall j :: i < j < limit ==> path[j] != '/';
        slash := i;
      }
    }
    if slash == -1 {
      assert forall j :: 0 <= j < limit ==> path[j] != '/';
    } else {
      assert 0 <= slash < limit;
      assert path[slash] == '/';
      assert forall j :: slash < j < limit ==> path[j] != '/';
    }
  }
}
