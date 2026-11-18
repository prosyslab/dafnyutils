
module MvPathSpec {
  /** Checks whether a character is a path separator. */
  function IsSlash(ch: char): bool
  {
    ch == '/'
  }

  /** Requires the text to contain no path separators. */
  predicate SlashFree(text: string)
  {
    forall i :: 0 <= i < |text| ==> !IsSlash(text[i])
  }

  /** Requires every character in the text to be a path separator. */
  predicate SlashesOnly(text: string)
  {
    forall i :: 0 <= i < |text| ==> IsSlash(text[i])
  }

  /** Requires a nonempty final path component preceded by a slash or the start of the text. */
  ghost predicate MaximalSlashFreeSuffix(text: string, suffix: string)
  {
    0 < |suffix| <= |text| &&
    text[|text| - |suffix|..] == suffix &&
    SlashFree(suffix) &&
    (|suffix| == |text| || IsSlash(text[|text| - |suffix| - 1]))
  }

  /** Relates a path to its final component, handling empty paths and paths containing only slashes. */
  ghost predicate BasenameRelation(path: string, base: string)
  {
    if |path| == 0 then
      base == ""
    else if SlashesOnly(path) then
      base == "/"
    else
      exists trimmed: string, prefix: string, trailing: string ::
        path == trimmed + trailing &&
        SlashesOnly(trailing) &&
        0 < |trimmed| &&
        !IsSlash(trimmed[|trimmed| - 1]) &&
        trimmed == prefix + base &&
        MaximalSlashFreeSuffix(trimmed, base)
  }

  /** Splits a path into a nonempty prefix ending in a non-slash character and trailing slashes. */
  ghost predicate PathWithoutTrailingSlashes(
    path: string, trimmed: string, trailing: string
  )
  {
    path == trimmed + trailing &&
    SlashesOnly(trailing) &&
    0 < |trimmed| &&
    !IsSlash(trimmed[|trimmed| - 1])
  }

  /** Splits a trimmed path at its last slash into a directory prefix and final component. */
  ghost predicate MaximalDirnamePrefix(
    trimmed: string, prefix: string, component: string
  )
  {
    trimmed == prefix + "/" + component &&
    0 < |component| &&
    SlashFree(component) &&
    (forall i :: 0 <= i < |trimmed| && IsSlash(trimmed[i]) ==> i <= |prefix|)
  }

  /** Relates a directory prefix to its value without trailing slashes, preserving the root. */
  ghost predicate NormalizedDirnamePrefix(prefix: string, value: string)
  {
    if |prefix| == 0 then
      value == "/"
    else if SlashesOnly(prefix) then
      value == "/"
    else
      exists trailing: string ::
        prefix == value + trailing &&
        SlashesOnly(trailing) &&
        0 < |value| &&
        !IsSlash(value[|value| - 1])
  }

  /** Relates a path to its parent directory, using a dot when no directory component exists. */
  opaque ghost predicate DirnameRelation(path: string, value: string)
  {
    if |path| == 0 then
      value == "."
    else if SlashesOnly(path) then
      value == "/"
    else
      exists trimmed: string, trailing: string ::
        PathWithoutTrailingSlashes(path, trimmed, trailing) &&
        (if SlashFree(trimmed) then
           value == "."
         else
           exists prefix: string, component: string ::
             MaximalDirnamePrefix(trimmed, prefix, component) &&
             NormalizedDirnamePrefix(prefix, value))
  }

  lemma LastMatchingIndexExists(text: string, slash: bool)
    requires exists i :: 0 <= i < |text| && IsSlash(text[i]) == slash
    ensures exists i ::
      0 <= i < |text| && IsSlash(text[i]) == slash &&
      forall j :: i < j < |text| ==> IsSlash(text[j]) != slash
    decreases |text|
  {
    if IsSlash(text[|text| - 1]) != slash {
      LastMatchingIndexExists(text[..|text| - 1], slash);
    }
  }

  /** Establishes that every path has a parent and final component in the relations. */
  lemma EntryNameExists(path: string)
    ensures exists parent: string, leaf: string ::
      DirnameRelation(path, parent) && BasenameRelation(path, leaf)
  {
    reveal DirnameRelation();
    if |path| == 0 {
      assert DirnameRelation(path, ".") && BasenameRelation(path, "");
    } else if SlashesOnly(path) {
      assert DirnameRelation(path, "/") && BasenameRelation(path, "/");
    } else {
      LastMatchingIndexExists(path, false);
      var end :|
        0 <= end < |path| && !IsSlash(path[end]) &&
        forall j :: end < j < |path| ==> IsSlash(path[j]);
      var trimmed := path[..end + 1];
      var trailing := path[end + 1..];
      assert SlashesOnly(trailing);
      assert PathWithoutTrailingSlashes(path, trimmed, trailing);
      if SlashFree(trimmed) {
        assert MaximalSlashFreeSuffix(trimmed, trimmed);
        assert trimmed == "" + trimmed;
        assert DirnameRelation(path, ".") && BasenameRelation(path, trimmed);
      } else {
        LastMatchingIndexExists(trimmed, true);
        var slash :|
          0 <= slash < |trimmed| && IsSlash(trimmed[slash]) &&
          forall j :: slash < j < |trimmed| ==> !IsSlash(trimmed[j]);
        var prefix := trimmed[..slash];
        var leaf := trimmed[slash + 1..];
        assert SlashFree(leaf) by {
          forall i | 0 <= i < |leaf|
            ensures !IsSlash(leaf[i])
          {
            assert leaf[i] == trimmed[slash + 1 + i];
          }
        }
        assert trimmed == prefix + "/" + leaf;
        assert MaximalDirnamePrefix(trimmed, prefix, leaf);
        assert MaximalSlashFreeSuffix(trimmed, leaf);
        assert trimmed == trimmed[..slash + 1] + leaf;
        assert BasenameRelation(path, leaf);
        var parent := "/";
        if |prefix| > 0 && !SlashesOnly(prefix) {
          LastMatchingIndexExists(prefix, false);
          var parentEnd :|
            0 <= parentEnd < |prefix| && !IsSlash(prefix[parentEnd]) &&
            forall j :: parentEnd < j < |prefix| ==> IsSlash(prefix[j]);
          parent := prefix[..parentEnd + 1];
          var parentTrailing := prefix[parentEnd + 1..];
          assert prefix == parent + parentTrailing;
          assert SlashesOnly(parentTrailing);
        }
        assert NormalizedDirnamePrefix(prefix, parent);
        assert DirnameRelation(path, parent);
      }
    }
  }

  /** Returns the decimal character for a digit from zero through nine. */
  function DigitCharSpec(d: nat): char
    requires d < 10
  {
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
  }

  /** Returns the decimal representation of a natural number. */
  function DecimalNatSpec(n: nat): string
    decreases n
  {
    if n < 10 then
      [DigitCharSpec(n)]
    else
      DecimalNatSpec(n / 10) + [DigitCharSpec(n % 10)]
  }

  /** Returns the target path with a numbered backup suffix of the form .~index~. */
  function NumberedBackupPathSpec(target: string, index: nat): string
    requires index >= 1
  {
    target + ".~" + DecimalNatSpec(index) + "~"
  }

  /** Returns the target path with the requested backup suffix appended. */
  function SimpleBackupPathSpec(target: string, suffix: string): string
  {
    target + suffix
  }

}
