include "MvPathSpec.dfy"
include "MvPathCore.dfy"

module MvPathProof {
  import Core = MvPathCore
  import Spec = MvPathSpec

  lemma BasenameValueSummaryGivesRelation(path: string, value: string)
    requires Core.BasenameValueSummary(path, value)
    ensures Spec.BasenameRelation(path, value)
  {
    if |path| == 0 {
    } else if forall i {:trigger path[i]} :: 0 <= i < |path| ==> path[i] == '/' {
      assert Spec.SlashesOnly(path);
    } else {
      var trimEnd :|
        Core.TrimEndSummary(path, trimEnd) &&
        exists start: int ::
          Core.BasenameSegmentSummary(path, start, trimEnd, value);
      var start :| Core.BasenameSegmentSummary(path, start, trimEnd, value);
      var trimmed := path[..trimEnd];
      var prefix := path[..start];
      var trailing := path[trimEnd..];
      assert path == trimmed + trailing;
      assert Spec.SlashesOnly(trailing);
      assert trimmed == prefix + value by {
        assert trimmed[..start] == prefix;
        assert trimmed[start..] == value;
        assert trimmed == trimmed[..start] + trimmed[start..];
      }
      assert Spec.SlashFree(value) by {
        forall i | 0 <= i < |value|
          ensures !Spec.IsSlash(value[i])
        {
          assert value[i] == path[start + i];
          assert start <= start + i < trimEnd;
        }
      }
      assert value == trimmed[|trimmed| - |value|..];
      assert |value| == |trimmed| - start;
      assert |value| == |trimmed| || Spec.IsSlash(trimmed[|trimmed| - |value| - 1]);
      assert Spec.MaximalSlashFreeSuffix(trimmed, value);
    }
  }

  lemma DirnameValueSummaryGivesRelation(path: string, value: string)
    requires Core.DirnameValueSummary(path, value)
    ensures Spec.DirnameRelation(path, value)
  {
    reveal Spec.DirnameRelation();
    if |path| == 0 {
    } else if forall i {:trigger path[i]} :: 0 <= i < |path| ==> path[i] == '/' {
      assert Spec.SlashesOnly(path);
    } else {
      var trimmed :|
        Core.TrimmedSummary(path, trimmed) &&
        (if trimmed == "/" then
           value == "/"
         else
           exists slash: int ::
             Core.LastSlashSummary(trimmed, |trimmed|, slash) &&
             (if slash == -1 then
                value == "."
              else if slash == 0 then
                value == "/"
              else
                Core.TrimmedSummary(trimmed[..slash], value)));
      var end :|
        0 < end <= |path| &&
        trimmed == path[..end] &&
        path[end - 1] != '/' &&
        forall i :: end <= i < |path| ==> path[i] == '/';
      var trailing := path[end..];
      assert path == trimmed + trailing;
      assert Spec.SlashesOnly(trailing);
      assert Spec.PathWithoutTrailingSlashes(path, trimmed, trailing);
      assert trimmed != "/";
      var slash :|
        Core.LastSlashSummary(trimmed, |trimmed|, slash) &&
        (if slash == -1 then
           value == "."
         else if slash == 0 then
           value == "/"
         else
           Core.TrimmedSummary(trimmed[..slash], value));
      if slash == -1 {
        assert Spec.SlashFree(trimmed);
      } else {
        var prefix := trimmed[..slash];
        var component := trimmed[slash + 1..];
        assert trimmed == prefix + "/" + component;
        assert 0 < |component|;
        assert Spec.SlashFree(component);
        assert forall i :: 0 <= i < |trimmed| && Spec.IsSlash(trimmed[i]) ==>
                             i <= |prefix|;
        assert Spec.MaximalDirnamePrefix(trimmed, prefix, component);
        if slash == 0 {
          assert Spec.NormalizedDirnamePrefix(prefix, value);
        } else {
          assert Core.TrimmedSummary(prefix, value);
          if forall i {:trigger prefix[i]} :: 0 <= i < |prefix| ==> prefix[i] == '/' {
            assert Spec.SlashesOnly(prefix);
          } else {
            var prefixEnd :|
              0 < prefixEnd <= |prefix| &&
              value == prefix[..prefixEnd] &&
              prefix[prefixEnd - 1] != '/' &&
              forall i :: prefixEnd <= i < |prefix| ==> prefix[i] == '/';
            var prefixTrailing := prefix[prefixEnd..];
            assert prefix == value + prefixTrailing;
            assert Spec.SlashesOnly(prefixTrailing);
          }
          assert Spec.NormalizedDirnamePrefix(prefix, value);
        }
      }
    }
  }
}
