include "../../core/IO.dfy"
include "LinkSchema.dfy"
include "LinkSpec.dfy"

module LinkCore {
  import BenchIO
  import BenchWorld
  import Schema = LinkSchema
  import Spec = LinkSpec
  import C = IOContract
  import Utf8 = Utf8Semantics

  twostate predicate CoreSummary(raw: Schema.LinkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if raw.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if raw.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if raw.mode != Schema.ModeRun then
      match raw.mode
      case ModeExtraOperand(operand) =>
        io.fs() == old(io.fs()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) +
          Spec.ExtraOperandText(C.QuoteArgumentResult(Utf8.Encode(operand))) &&
        exit == 1
      case _ => false
    else if |raw.operands| == 0 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.MissingOperandText() &&
      exit == 1
    else if |raw.operands| == 1 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) +
        Spec.MissingOperandAfterText(
          C.QuoteArgumentResult(Utf8.Encode(raw.operands[0]))
        ) &&
      exit == 1
    else
      exists ok: bool, err: int ::
        Spec.LinkResult(io, raw.operands[0], raw.operands[1], ok, err) &&
        io.stdout() == old(io.stdout()) &&
        (if ok then
          io.stderr() == old(io.stderr()) && exit == 0
        else
          io.stderr() == old(io.stderr()) +
            Spec.CannotCreateLinkText(
              C.QuoteafPathResult(raw.operands[1]),
              C.QuoteafPathResult(raw.operands[0]),
              C.CLocaleErrnoTextResult(err)
            ) &&
          exit == 1)
  }

  method RunCore(raw: Schema.LinkCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.fsRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
  {
    if raw.mode == Schema.ModeHelp {
      var _, _ := io.WriteStdout(Spec.HelpTextSpec(), BenchWorld.ThrowOnError);
      exit := 0;
    } else if raw.mode == Schema.ModeVersion {
      var _, _ := io.WriteStdout(Spec.VersionTextSpec(), BenchWorld.ThrowOnError);
      exit := 0;
    } else if raw.mode.ModeExtraOperand? {
      var quotedOperand := io.QuoteArgument(Utf8.Encode(raw.mode.operand));
      var _, _ := io.WriteStderr(Spec.ExtraOperandText(quotedOperand), BenchWorld.ThrowOnError);
      exit := 1;
    } else if |raw.operands| == 0 {
      var _, _ := io.WriteStderr(Spec.MissingOperandText(), BenchWorld.ThrowOnError);
      exit := 1;
    } else if |raw.operands| == 1 {
      var quotedSource := io.QuoteArgument(Utf8.Encode(raw.operands[0]));
      var _, _ := io.WriteStderr(
        Spec.MissingOperandAfterText(quotedSource),
        BenchWorld.ThrowOnError
      );
      exit := 1;
    } else {
      var source := raw.operands[0];
      var target := raw.operands[1];
      var ok, err := io.CreateHardLink(source, target);
      assert Spec.LinkResult(io, source, target, ok, err);

      if ok {
        exit := 0;
      } else {
        var reason := io.GetCLocaleErrnoText(err);
        var quotedTarget := io.QuoteafPath(target);
        var quotedSource := io.QuoteafPath(source);
        var _, _ := io.WriteStderr(
          Spec.CannotCreateLinkText(quotedTarget, quotedSource, reason),
          BenchWorld.ThrowOnError
        );
        exit := 1;

        assert C.GetCLocaleErrnoTextSpec(err, reason);
        assert Spec.LinkResult(io, source, target, ok, err);
      }
    }
  }
}
