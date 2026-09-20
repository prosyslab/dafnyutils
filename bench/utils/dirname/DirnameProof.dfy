include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "DirnameSchema.dfy"
include "DirnameCore.dfy"
include "DirnameSpec.dfy"

module DirnameProof {
  import Utf8 = Utf8Semantics
  import BenchIO
  import Schema = DirnameSchema
  import Core = DirnameCore
  import Spec = DirnameSpec

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
      assert Spec.SlashesOnly(trailing) by {
        forall i | 0 <= i < |trailing|
          ensures Spec.IsSlash(trailing[i])
        {
          assert trailing[i] == path[end + i];
          assert end <= end + i < |path|;
        }
      }
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
        assert 0 <= slash < |trimmed|;
        assert trimmed[slash] == '/';
        var prefix := trimmed[..slash];
        var component := trimmed[slash + 1..];
        assert trimmed == trimmed[..slash] + [trimmed[slash]] + trimmed[slash + 1..];
        assert trimmed == prefix + "/" + component;
        assert 0 < |component|;
        assert Spec.SlashFree(component);
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
        assert exists prefix: string, component: string ::
          Spec.MaximalDirnamePrefix(trimmed, prefix, component) &&
          Spec.NormalizedDirnamePrefix(prefix, value);
      }
      assert if Spec.SlashFree(trimmed) then
               value == "."
             else
               exists prefix: string, component: string ::
                 Spec.MaximalDirnamePrefix(trimmed, prefix, component) &&
                 Spec.NormalizedDirnamePrefix(prefix, value);
      assert exists trimmed: string, trailing: string ::
        Spec.PathWithoutTrailingSlashes(path, trimmed, trailing) &&
        (if Spec.SlashFree(trimmed) then
           value == "."
         else
           exists prefix: string, component: string ::
             Spec.MaximalDirnamePrefix(trimmed, prefix, component) &&
             Spec.NormalizedDirnamePrefix(prefix, value));
    }
  }

  lemma OperandOutputPartitionElement(
    paths: seq<string>,
    sep: string,
    out: string,
    pieces: seq<string>,
    cuts: seq<nat>,
    i: int
  )
    requires Spec.OperandOutputPartition(paths, sep, out, pieces, cuts)
    requires 0 <= i < |paths|
    ensures cuts[i] <= cuts[i + 1] <= |out|
    ensures Spec.DirnameRelation(paths[i], pieces[i])
    ensures out[cuts[i]..cuts[i + 1]] == pieces[i] + sep
  {
    reveal Spec.OperandOutputPartition();
    assert cuts[i] <= cuts[i + 1] <= |out|;
    assert out[cuts[i]..cuts[i + 1]] == pieces[i] + sep;
    assert Spec.DirnameRelation(paths[i], pieces[i]);
  }

  lemma AppendPrefixSlice(left: string, right: string, lo: nat, hi: nat)
    requires lo <= hi <= |left|
    ensures (left + right)[lo..hi] == left[lo..hi]
  {
  }

  lemma AppendSuffixSlice(left: string, middle: string, right: string)
    ensures (left + middle + right)[|left|..] == middle + right
  {
  }

  lemma RenderSummaryGivesRelation(
    paths: seq<string>, sep: string, out: string
  )
    requires Core.RenderSummary(paths, sep, out)
    ensures Spec.OperandOutputRelation(paths, sep, out)
    decreases |paths|
  {
    if |paths| == 0 {
      var pieces: seq<string> := [];
      var cuts: seq<nat> := [0];
      assert Spec.OperandOutputPartition(paths, sep, out, pieces, cuts);
    } else {
      var prior := paths[..|paths| - 1];
      var prefixOut, value :|
        Core.RenderSummary(prior, sep, prefixOut) &&
        Core.DirnameValueSummary(paths[|paths| - 1], value) &&
        out == prefixOut + value + sep;
      RenderSummaryGivesRelation(prior, sep, prefixOut);
      DirnameValueSummaryGivesRelation(paths[|paths| - 1], value);
      var pieces: seq<string>, cuts: seq<nat> :|
        Spec.OperandOutputPartition(prior, sep, prefixOut, pieces, cuts);
      reveal Spec.OperandOutputPartition();
      var nextPieces := pieces + [value];
      var nextCuts := cuts + [|out|];
      assert Spec.OperandOutputRelation(paths, sep, out) by {
        assert |prior| == |paths| - 1;
        assert |nextPieces| == |paths|;
        assert |nextCuts| == |paths| + 1;
        assert nextCuts[0] == 0;
        assert nextCuts[|paths|] == |out|;
        assert forall i {:trigger nextCuts[i], nextCuts[i + 1]} ::
            0 <= i < |paths| ==> nextCuts[i] <= nextCuts[i + 1] <= |out| by {
          forall i {:trigger nextCuts[i]} | 0 <= i < |paths|
            ensures nextCuts[i] <= nextCuts[i + 1] <= |out|
          {
            if i < |paths| - 1 {
              assert nextCuts[i] == cuts[i];
              assert nextCuts[i + 1] == cuts[i + 1];
              assert cuts[i + 1] <= |prefixOut|;
              assert |prefixOut| <= |out|;
            } else {
              assert i == |paths| - 1;
              assert nextCuts[i] == |prefixOut|;
            }
          }
        }
        forall i {:trigger nextPieces[i]} | 0 <= i < |paths| &&
                                            nextCuts[i] <= nextCuts[i + 1] <= |out|
          ensures
            Spec.DirnameRelation(paths[i], nextPieces[i]) &&
            out[nextCuts[i]..nextCuts[i + 1]] == nextPieces[i] + sep
        {
          if i < |paths| - 1 {
            OperandOutputPartitionElement(
              prior, sep, prefixOut, pieces, cuts, i
            );
            assert nextCuts[i] == cuts[i];
            assert nextCuts[i + 1] == cuts[i + 1];
            assert cuts[i] <= cuts[i + 1] <= |prefixOut|;
            assert paths[i] == prior[i];
            assert nextPieces[i] == pieces[i];
            assert Spec.DirnameRelation(prior[i], pieces[i]);
            assert prefixOut[cuts[i]..cuts[i + 1]] == pieces[i] + sep;
            AppendPrefixSlice(prefixOut, value + sep, cuts[i], cuts[i + 1]);
            assert out[nextCuts[i]..nextCuts[i + 1]] ==
                   prefixOut[cuts[i]..cuts[i + 1]];
          } else {
            assert i == |paths| - 1;
            assert nextCuts[i] == |prefixOut|;
            assert nextCuts[i + 1] == |out|;
            assert nextPieces[i] == value;
            AppendSuffixSlice(prefixOut, value, sep);
            assert out[|prefixOut|..|out|] == value + sep;
            assert out[nextCuts[i]..nextCuts[i + 1]] == value + sep;
          }
        }
        assert Spec.OperandOutputPartition(
            paths, sep, out, nextPieces, nextCuts
          );
      }
    }
  }

  lemma RunOutputSummaryGivesRelation(cmd: Core.DirnameCmd, out: string)
    requires Core.RunOutputSummary(cmd, out)
    ensures Spec.CommandOutputRelation(
              cmd.zeroTerminated, cmd.operands, out
            )
  {
    RenderSummaryGivesRelation(
      cmd.operands, if cmd.zeroTerminated then ['\0'] else "\n", out
    );
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.DirnameCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var cmd := Core.Command(raw);
    if cmd.mode == Core.ModeHelp {
    } else if cmd.mode == Core.ModeVersion {
    } else if |cmd.operands| == 0 {
    } else {
      var out :|
        Core.RunOutputSummary(cmd, out) &&
        io.stdout() == old(io.stdout()) + Utf8.Encode(out);
      RunOutputSummaryGivesRelation(cmd, out);
    }
  }
}
