include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "BasenameSchema.dfy"
include "BasenameSpec.dfy"

module BasenameCore {
  import Utf8 = Utf8Semantics
  import BenchIO
  import Schema = BasenameSchema
  import BenchWorld
  import Spec = BasenameSpec

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

  ghost predicate RemoveSuffixSummary(base: string, suffixText: string, hasSuffix: bool, value: string)
  {
    if hasSuffix && 0 < |suffixText| < |base| && base[|base| - |suffixText|..] == suffixText then
      value == base[..|base| - |suffixText|]
    else
      value == base
  }

  ghost predicate BasenamePieceSummary(path: string, suffixText: string, hasSuffix: bool, value: string)
  {
    exists base: string ::
      BasenameValueSummary(path, base) &&
      RemoveSuffixSummary(base, suffixText, hasSuffix, value)
  }

  ghost predicate RenderSummary(paths: seq<string>, suffixText: string, hasSuffix: bool, sep: string, out: string)
    decreases |paths|
  {
    if |paths| == 0 then
      out == ""
    else
      exists prefixOut: string, value: string ::
        RenderSummary(paths[..|paths| - 1], suffixText, hasSuffix, sep, prefixOut) &&
        BasenamePieceSummary(paths[|paths| - 1], suffixText, hasSuffix, value) &&
        out == prefixOut + value + sep
  }

  ghost predicate RunOutputSummary(cmd: Schema.BasenameCmd, out: string)
  {
    var sep := if cmd.zeroTerminated then ['\0'] else "\n";
    if |cmd.operands| == 0 then
      out == ""
    else if cmd.multiple then
      match cmd.suffix
      case Some(s) =>
        RenderSummary(cmd.operands, s, true, sep, out)
      case None =>
        RenderSummary(cmd.operands, "", false, sep, out)
    else if |cmd.operands| == 2 then
      exists piece: string ::
        BasenamePieceSummary(cmd.operands[0], cmd.operands[1], true, piece) &&
        out == piece + sep
    else
      exists piece: string ::
        BasenamePieceSummary(cmd.operands[0], "", false, piece) &&
        out == piece + sep
  }

  twostate predicate CoreSummary(raw: Schema.BasenameCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp then
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if cmd.mode == Schema.ModeVersion then
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if |cmd.operands| == 0 then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MissingOperandMessageSpec() &&
      exit == 1
    else if !cmd.multiple && |cmd.operands| > 2 then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.ExtraOperandMessageSpec(cmd.operands[2]) &&
      exit == 1
    else
      io.stderr() == old(io.stderr()) &&
      exit == 0 &&
      exists out: string ::
        RunOutputSummary(cmd, out) &&
        io.stdout() == old(io.stdout()) + Utf8.Encode(out)
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

  method RemoveSuffixIfNeeded(base: string, suffixText: string, hasSuffix: bool) returns (value: string)
    ensures RemoveSuffixSummary(base, suffixText, hasSuffix, value)
    decreases *
  {
    if !hasSuffix || |suffixText| == 0 || |base| <= |suffixText| {
      value := base;
      return;
    }

    var start := |base| - |suffixText|;
    var same := true;
    var i := 0;
    while i < |suffixText|
      invariant 0 <= i <= |suffixText|
      invariant same <==> (forall j :: 0 <= j < i ==> base[start + j] == suffixText[j])
      decreases |suffixText| - i
    {
      if base[start + i] != suffixText[i] {
        same := false;
      }
      i := i + 1;
    }

    if same {
      value := base[..start];
    } else {
      value := base;
    }
  }

  method BuildPiece(path: string, suffixText: string, hasSuffix: bool) returns (piece: string)
    ensures BasenamePieceSummary(path, suffixText, hasSuffix, piece)
    decreases *
  {
    var base := ComputeBasenameValue(path);
    piece := RemoveSuffixIfNeeded(base, suffixText, hasSuffix);
  }

  method BuildManyOutput(
    paths: seq<string>, suffixText: string, hasSuffix: bool, sep: string
  ) returns (out: string)
    ensures RenderSummary(paths, suffixText, hasSuffix, sep, out)
    decreases *
  {
    out := "";
    var i := 0;
    while i < |paths|
      invariant 0 <= i <= |paths|
      invariant RenderSummary(paths[..i], suffixText, hasSuffix, sep, out)
      decreases |paths| - i
    {
      var prefixOut := out;
      var piece := BuildPiece(paths[i], suffixText, hasSuffix);
      assert RenderSummary(paths[..i], suffixText, hasSuffix, sep, prefixOut);
      assert BasenamePieceSummary(paths[i], suffixText, hasSuffix, piece);
      out := prefixOut + piece + sep;
      i := i + 1;
      assert paths[..i] == paths[..i - 1] + [paths[i - 1]];
      assert exists prefixOut2: string, value: string ::
          RenderSummary(paths[..i - 1], suffixText, hasSuffix, sep, prefixOut2) &&
          BasenamePieceSummary(paths[i - 1], suffixText, hasSuffix, value) &&
          out == prefixOut2 + value + sep;
      assert RenderSummary(paths[..i], suffixText, hasSuffix, sep, out);
    }
    assert paths[..i] == paths;
    assert RenderSummary(paths, suffixText, hasSuffix, sep, out);
  }

  method {:vcs_split_on_every_assert} BuildRunOutput(cmd: Schema.BasenameCmd) returns (out: string)
    requires |cmd.operands| > 0
    ensures RunOutputSummary(cmd, out)
    decreases *
  {
    var sep := if cmd.zeroTerminated then ['\0'] else "\n";
    if cmd.multiple {
      match cmd.suffix
      case Some(s) =>
        out := BuildManyOutput(cmd.operands, s, true, sep);
      case None =>
        out := BuildManyOutput(cmd.operands, "", false, sep);
    } else if |cmd.operands| == 2 {
      var piece := BuildPiece(cmd.operands[0], cmd.operands[1], true);
      out := piece + sep;
    } else {
      var piece := BuildPiece(cmd.operands[0], "", false);
      out := piece + sep;
    }
    assert RunOutputSummary(cmd, out);
  }

  method RunCore(raw: Schema.BasenameCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
      var out := Spec.HelpTextSpec();
      io.AppendStdout(out);
      exit := 0;
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := Spec.VersionTextSpec();
      io.AppendStdout(out);
      exit := 0;
      return;
    }

    if |cmd.operands| == 0 {
      var err := Spec.MissingOperandMessageSpec();
      io.AppendStderr(err);
      exit := 1;
      return;
    }

    if !cmd.multiple && |cmd.operands| > 2 {
      var err := Spec.ExtraOperandMessageSpec(cmd.operands[2]);
      io.AppendStderr(err);
      exit := 1;
      return;
    }

    var operandCount := 0;
    while operandCount < |cmd.operands|
      invariant 0 <= operandCount <= |cmd.operands|
      decreases |cmd.operands| - operandCount
    {
      operandCount := operandCount + 1;
    }

    var out := BuildRunOutput(cmd);
    io.AppendStdout(Utf8.Encode(out));
    exit := 0;
  }
}
