include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "BasenameSchema.dfy"
include "BasenameCore.dfy"
include "BasenameSpec.dfy"

module BasenameProof {
  import Utf8 = Utf8Semantics
  import BenchIO
  import Schema = BasenameSchema
  import Core = BasenameCore
  import Spec = BasenameSpec

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
      var trailing := path[trimEnd..];
      assert path == trimmed + trailing;
      assert Spec.SlashesOnly(trailing);
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
      assert exists trimmed: string, trailing: string ::
        path == trimmed + trailing &&
        Spec.SlashesOnly(trailing) &&
        0 < |trimmed| &&
        !Spec.IsSlash(trimmed[|trimmed| - 1]) &&
        Spec.MaximalSlashFreeSuffix(trimmed, value);
    }
  }

  lemma RemoveSuffixSummaryGivesRelation(
    base: string, suffixText: string, hasSuffix: bool, value: string
  )
    requires Core.RemoveSuffixSummary(base, suffixText, hasSuffix, value)
    ensures Spec.SuffixRemovalRelation(base, suffixText, hasSuffix, value)
  {
  }

  lemma BasenamePieceSummaryGivesRelation(
    path: string, suffixText: string, hasSuffix: bool, value: string
  )
    requires Core.BasenamePieceSummary(path, suffixText, hasSuffix, value)
    ensures Spec.BasenamePieceRelation(path, suffixText, hasSuffix, value)
  {
    var base :|
      Core.BasenameValueSummary(path, base) &&
      Core.RemoveSuffixSummary(base, suffixText, hasSuffix, value);
    BasenameValueSummaryGivesRelation(path, base);
    RemoveSuffixSummaryGivesRelation(base, suffixText, hasSuffix, value);
  }

  lemma OperandOutputPartitionElement(
    paths: seq<string>,
    suffixText: string,
    hasSuffix: bool,
    sep: string,
    out: string,
    pieces: seq<string>,
    cuts: seq<nat>,
    i: int
  )
    requires Spec.OperandOutputPartition(
               paths, suffixText, hasSuffix, sep, out, pieces, cuts
             )
    requires 0 <= i < |paths|
    ensures cuts[i] <= cuts[i + 1] <= |out|
    ensures Spec.BasenamePieceRelation(
              paths[i], suffixText, hasSuffix, pieces[i]
            )
    ensures out[cuts[i]..cuts[i + 1]] == pieces[i] + sep
  {
    reveal Spec.OperandOutputPartition();
    assert cuts[i] <= cuts[i + 1] <= |out|;
    assert out[cuts[i]..cuts[i + 1]] == pieces[i] + sep;
    assert Spec.BasenamePieceRelation(
        paths[i], suffixText, hasSuffix, pieces[i]
      );
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
    paths: seq<string>, suffixText: string, hasSuffix: bool, sep: string, out: string
  )
    requires Core.RenderSummary(paths, suffixText, hasSuffix, sep, out)
    ensures Spec.OperandOutputRelation(paths, suffixText, hasSuffix, sep, out)
    decreases |paths|
  {
    if |paths| == 0 {
      assert out == "";
      assert Spec.OperandOutputRelation(paths, suffixText, hasSuffix, sep, out) by {
        var pieces: seq<string> := [];
        var cuts: seq<nat> := [0];
        assert Spec.OperandOutputPartition(
            paths, suffixText, hasSuffix, sep, out, pieces, cuts
          );
      }
    } else {
      var prior := paths[..|paths| - 1];
      var prefixOut, value :|
        Core.RenderSummary(prior, suffixText, hasSuffix, sep, prefixOut) &&
        Core.BasenamePieceSummary(paths[|paths| - 1], suffixText, hasSuffix, value) &&
        out == prefixOut + value + sep;
      RenderSummaryGivesRelation(prior, suffixText, hasSuffix, sep, prefixOut);
      BasenamePieceSummaryGivesRelation(
        paths[|paths| - 1], suffixText, hasSuffix, value
      );
      assert Spec.OperandOutputRelation(prior, suffixText, hasSuffix, sep, prefixOut);
      var pieces: seq<string>, cuts: seq<nat> :|
        Spec.OperandOutputPartition(
          prior, suffixText, hasSuffix, sep, prefixOut, pieces, cuts
        );
      reveal Spec.OperandOutputPartition();
      var nextPieces := pieces + [value];
      var nextCuts := cuts + [|out|];
      assert Spec.OperandOutputRelation(paths, suffixText, hasSuffix, sep, out) by {
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
            Spec.BasenamePieceRelation(paths[i], suffixText, hasSuffix, nextPieces[i]) &&
            out[nextCuts[i]..nextCuts[i + 1]] == nextPieces[i] + sep
        {
          if i < |paths| - 1 {
            OperandOutputPartitionElement(
              prior, suffixText, hasSuffix, sep, prefixOut, pieces, cuts, i
            );
            assert nextCuts[i] == cuts[i];
            assert nextCuts[i + 1] == cuts[i + 1];
            assert cuts[i] <= cuts[i + 1] <= |prefixOut|;
            assert paths[i] == prior[i];
            assert nextPieces[i] == pieces[i];
            assert Spec.BasenamePieceRelation(
                prior[i], suffixText, hasSuffix, pieces[i]
              );
            assert prefixOut[cuts[i]..cuts[i + 1]] == pieces[i] + sep;
            AppendPrefixSlice(
              prefixOut, value + sep, cuts[i], cuts[i + 1]
            );
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
            paths, suffixText, hasSuffix, sep, out, nextPieces, nextCuts
          );
      }
    }
  }

  lemma RunOutputSummaryGivesRelation(cmd: Schema.BasenameCmd, out: string)
    requires Core.RunOutputSummary(cmd, out)
    ensures Spec.CommandOutputRelation(cmd, out)
  {
    var sep := if cmd.zeroTerminated then ['\0'] else "\n";
    if |cmd.operands| == 0 {
    } else if cmd.multiple {
      match cmd.suffix
      case Some(s) =>
        RenderSummaryGivesRelation(cmd.operands, s, true, sep, out);
      case None =>
        RenderSummaryGivesRelation(cmd.operands, "", false, sep, out);
    } else if |cmd.operands| == 2 {
      var piece :|
        Core.BasenamePieceSummary(cmd.operands[0], cmd.operands[1], true, piece) &&
        out == piece + sep;
      BasenamePieceSummaryGivesRelation(
        cmd.operands[0], cmd.operands[1], true, piece
      );
    } else {
      var piece :|
        Core.BasenamePieceSummary(cmd.operands[0], "", false, piece) &&
        out == piece + sep;
      BasenamePieceSummaryGivesRelation(cmd.operands[0], "", false, piece);
    }
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.BasenameCmdRaw, io: BenchIO.IO, exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
    } else if cmd.mode == Schema.ModeVersion {
    } else if |cmd.operands| == 0 {
    } else if !cmd.multiple && |cmd.operands| > 2 {
    } else {
      var out :|
        Core.RunOutputSummary(cmd, out) &&
        io.stdout() == old(io.stdout()) + Utf8.Encode(out);
      RunOutputSummaryGivesRelation(cmd, out);
    }
  }
}
