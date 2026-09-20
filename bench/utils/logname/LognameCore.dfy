include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "LognameSchema.dfy"
include "LognameSpec.dfy"

module LognameCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import IOContract
  import Schema = LognameSchema
  import BenchWorld
  import Spec = LognameSpec

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpTextSpec()
  {
    out := Spec.HelpTextSpec();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionTextSpec()
  {
    out := Spec.VersionTextSpec();
  }

  method GetExtraOperandMessage(op: string) returns (out: BenchWorld.Bytes)
    ensures out == Spec.ExtraOperandMessageSpec(op)
  {
    out := Spec.ExtraOperandMessageSpec(op);
  }

  method GetNoLoginNameMessage() returns (out: BenchWorld.Bytes)
    ensures out == Spec.NoLoginNameMessageSpec()
  {
    out := Spec.NoLoginNameMessageSpec();
  }

  ghost predicate LoginNameResultFields(
    props: map<string, string>,
    login: BenchWorld.Result<string>,
                             preStdout: BenchWorld.Bytes,
                             preStderr: BenchWorld.Bytes,
                             stdout: BenchWorld.Bytes,
                             stderr: BenchWorld.Bytes,
                             exit: int
  )
  {
    IOContract.GetLoginNameContractFields(props, login) &&
    match login
    case Ok(name) =>
      stdout == preStdout + Spec.LoginNameOutput(name) &&
      stderr == preStderr &&
      exit == 0
    case Err(_) =>
      stdout == preStdout &&
      stderr == preStderr + Spec.NoLoginNameMessageSpec() &&
      exit == 1
  }

  twostate predicate CoreSummary(raw: Schema.LognameCmdRaw, io: BenchIO.IO, exit: int)
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
    else if |cmd.operands| > 0 then
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + Spec.ExtraOperandMessageSpec(cmd.operands[0]) &&
      exit == 1
    else
      exists login: BenchWorld.Result<string> ::
        LoginNameResultFields(
          old(io.props()),
          login,
          old(io.stdout()),
          old(io.stderr()),
          io.stdout(),
          io.stderr(),
          exit
        )
  }

  method RunCore(raw: Schema.LognameCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion
    modifies io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preProps := io.props();
    ghost var preStdout := io.stdout();
    ghost var preStderr := io.stderr();
    var cmd := Schema.Command(raw);
    if cmd.mode == Schema.ModeHelp {
      var out := GetHelpText();
      io.AppendStdout(out);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if cmd.mode == Schema.ModeVersion {
      var out := GetVersionText();
      io.AppendStdout(out);
      exit := 0;
      assert CoreSummary(raw, io, exit);
      return;
    }

    if |cmd.operands| > 0 {
      var err := GetExtraOperandMessage(cmd.operands[0]);
      io.AppendStderr(err);
      exit := 1;
      assert CoreSummary(raw, io, exit);
      return;
    }

    var login := io.GetLoginName();
    assert IOContract.GetLoginNameContractFields(preProps, login);
    match login
    case Ok(name) =>
      io.AppendStdout(Spec.LoginNameOutput(name));
      exit := 0;
      assert LoginNameResultFields(
          preProps,
          login,
          preStdout,
          preStderr,
          io.stdout(),
          io.stderr(),
          exit
        );
      assert CoreSummary(raw, io, exit);
    case Err(_) =>
      var err := GetNoLoginNameMessage();
      io.AppendStderr(err);
      exit := 1;
      assert LoginNameResultFields(
          preProps,
          login,
          preStdout,
          preStderr,
          io.stdout(),
          io.stderr(),
          exit
        );
      assert CoreSummary(raw, io, exit);
  }
}
