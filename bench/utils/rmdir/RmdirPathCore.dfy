module RmdirPathCore {

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

  method TrimTrailingSlashes(path: string) returns (trimmed: string)
    ensures TrimmedSummary(path, trimmed)
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
