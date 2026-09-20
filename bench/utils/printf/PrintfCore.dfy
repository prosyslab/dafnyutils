include "../../core/World.dfy"
include "../../core/IO.dfy"
include "PrintfSchema.dfy"
include "PrintfSpec.dfy"

module PrintfCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import Schema = PrintfSchema
  import Spec = PrintfSpec

  function OctalFragment(
    format: string,
    start: nat,
    nextArg: nat
  ): Spec.FormatFragment
    requires start <= |format|
  {
    if start == |format| || !BenchWorld.IsOctalDigit(format[start]) then
      Spec.FormatFragment(start, nextArg, [0 as char])
    else if start + 1 == |format| || !BenchWorld.IsOctalDigit(format[start + 1]) then
      Spec.FormatFragment(
        start + 1,
        nextArg,
        [BenchWorld.CharToDigit(format[start]) as char])
    else
      Spec.FormatFragment(
        start + 2,
        nextArg,
        [(BenchWorld.CharToDigit(format[start]) * 8 +
          BenchWorld.CharToDigit(format[start + 1])) as char])
  }

  function ClassifyFragment(
    format: string,
    args: seq<string>,
    start: nat,
    nextArg: nat
  ): Spec.FragmentPlan
    requires start < |format|
    requires nextArg <= |args|
  {
    if format[start] == '\\' then
      if start + 1 >= |format| then
        Spec.NoFragment
      else if format[start + 1] == 'n' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, ['\n']))
      else if format[start + 1] == 't' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, ['\t']))
      else if format[start + 1] == '\\' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, ['\\']))
      else if format[start + 1] == '0' then
        Spec.OneFragment(OctalFragment(format, start + 2, nextArg))
      else
        Spec.NoFragment
    else if format[start] == '%' then
      if start + 1 >= |format| then
        Spec.NoFragment
      else if format[start + 1] == '%' then
        Spec.OneFragment(Spec.FormatFragment(start + 2, nextArg, ['%']))
      else if format[start + 1] == 's' then
        Spec.OneFragment(Spec.FormatFragment(
                           start + 2,
                           if nextArg < |args| then nextArg + 1 else nextArg,
                           if nextArg < |args| then Utf8.Encode(args[nextArg]) else []))
      else
        Spec.NoFragment
    else
      Spec.OneFragment(Spec.FormatFragment(start + 1, nextArg, Utf8.EncodeChar(format[start])))
  }

  function RenderPass(format: string, args: seq<string>, i: nat, nextArg: nat):
    (bool, BenchWorld.Bytes, nat, BenchWorld.Bytes)
    requires i <= |format|
    requires nextArg <= |args|
    ensures RenderPass(format, args, i, nextArg).0 ==>
              nextArg <= RenderPass(format, args, i, nextArg).2 <= |args|
    decreases |format| - i
  {
    if i >= |format| then
      (true, [], nextArg, [])
    else
      match ClassifyFragment(format, args, i, nextArg)
      case NoFragment => (false, [], nextArg, Spec.UnsupportedFormatMessage())
      case OneFragment(fragment) =>
        var rest := RenderPass(format, args, fragment.end, fragment.afterArg);
        if rest.0 then
          (true, fragment.output + rest.1, rest.2, [])
        else
          rest
  } by method {
    if i >= |format| {
      return (true, [], nextArg, []);
    } else {
      match ClassifyFragment(format, args, i, nextArg)
      case NoFragment =>
        return (false, [], nextArg, Spec.UnsupportedFormatMessage());
      case OneFragment(fragment) =>
        var rest := RenderPass(format, args, fragment.end, fragment.afterArg);
        if rest.0 {
          return (true, fragment.output + rest.1, rest.2, []);
        } else {
          return rest;
        }
    }
  }

  function RenderRepeatedFrom(format: string, args: seq<string>, startArg: nat):
    (bool, BenchWorld.Bytes, BenchWorld.Bytes)
    requires startArg <= |args|
    decreases |args| - startArg
  {
    var pass := RenderPass(format, args, 0, startArg);
    if !pass.0 then
      (false, [], pass.3)
    else if pass.2 == startArg then
      if startArg == |args| then
        (true, pass.1, [])
      else
        (true, pass.1, Spec.ExcessArgumentsWarning(args[startArg]))
    else if pass.2 >= |args| then
      (true, pass.1, [])
    else
      var rest := RenderRepeatedFrom(format, args, pass.2);
      if rest.0 then (true, pass.1 + rest.1, []) else rest
  } by method {
    var pass := RenderPass(format, args, 0, startArg);
    if !pass.0 {
      return (false, [], pass.3);
    } else if pass.2 == startArg {
      if startArg == |args| {
        return (true, pass.1, []);
      } else {
        return (true, pass.1, Spec.ExcessArgumentsWarning(args[startArg]));
      }
    } else if pass.2 >= |args| {
      return (true, pass.1, []);
    } else {
      assert startArg < pass.2 < |args|;
      var rest := RenderRepeatedFrom(format, args, pass.2);
      if rest.0 {
        return (true, pass.1 + rest.1, []);
      } else {
        return rest;
      }
    }
  }

  function RenderRepeated(format: string, args: seq<string>):
    (bool, BenchWorld.Bytes, BenchWorld.Bytes)
  {
    RenderRepeatedFrom(format, args, 0)
  } by method {
    return RenderRepeatedFrom(format, args, 0);
  }

  function Evaluate(raw: Schema.PrintfCmdRaw): (BenchWorld.Bytes, BenchWorld.Bytes, int)
  {
    if Schema.HelpSelected(raw) then
      (Spec.HelpText(), Spec.RequestExcessWarning(raw), 0)
    else if Schema.VersionSelected(raw) then
      (Spec.VersionText(), Spec.RequestExcessWarning(raw), 0)
    else if |raw.operands| == 0 then
      ([], Spec.MissingOperandMessage(), 1)
    else
      var rendered := RenderRepeated(raw.operands[0], raw.operands[1..]);
      if rendered.0 then
        (rendered.1, rendered.2, 0)
      else
        ([], rendered.2, 1)
  } by method {
    if Schema.HelpSelected(raw) {
      return (Spec.HelpText(), Spec.RequestExcessWarning(raw), 0);
    } else if Schema.VersionSelected(raw) {
      return (Spec.VersionText(), Spec.RequestExcessWarning(raw), 0);
    } else if |raw.operands| == 0 {
      return ([], Spec.MissingOperandMessage(), 1);
    } else {
      var rendered := RenderRepeated(raw.operands[0], raw.operands[1..]);
      if rendered.0 {
        return (rendered.1, rendered.2, 0);
      } else {
        return ([], rendered.2, 1);
      }
    }
  }

  twostate predicate CoreSummary(raw: Schema.PrintfCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    var result := Evaluate(raw);
    io.stdout() == old(io.stdout()) + result.0 &&
    io.stderr() == old(io.stderr()) + result.1 &&
    exit == result.2
  }

  method RunCore(raw: Schema.PrintfCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var result := Evaluate(raw);
    io.AppendStdout(result.0);
    assert io.stdout() == preStdout + result.0;
    io.AppendStderr(result.1);
    assert io.stderr() == preStderr + result.1;
    exit := result.2;
    assert CoreSummary(raw, io, exit);
  }
}
