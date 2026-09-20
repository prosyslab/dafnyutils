include "../../core/World.dfy"
include "../../core/IO.dfy"
include "PrintfSchema.dfy"

module PrintfSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import Schema = PrintfSchema




  function HelpText(): BenchWorld.Bytes
  {
    "Usage: printf FORMAT [ARGUMENT]...\n"
    + "Print ARGUMENT(s) according to FORMAT.\n"
    + "\n"
    + "This verified benchmark supports literal FORMAT text, \\\\n, \\\\t, \\\\\\\\, \\\\0NNN,\n"
    + "%s string directives, %% percent literals, and repeated FORMAT reuse.\n"
    + "      --help     display this help and exit\n"
    + "      --version  output version information and exit\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "printf (GNU coreutils) 9.10.13-2cf49\n"
    + "Written by David MacKenzie.\n"
  }

  function MissingOperandMessage(): BenchWorld.Bytes
  {
    "printf: missing operand\nTry 'printf --help' for more information.\n"
  }

  function UnsupportedFormatMessage(): BenchWorld.Bytes
  {
    "printf: unsupported format in verified subset\n"
  }

  function ExcessArgumentsWarning(arg: string): BenchWorld.Bytes
  {
    Utf8.Encode("printf: warning: ignoring excess arguments, starting with '" + arg + "'\n")
  }

  function RequestExcessWarning(raw: Schema.PrintfCmdRaw): BenchWorld.Bytes
  {
    match raw.excessAfterRequest
    case Some(arg) => ExcessArgumentsWarning(arg)
    case None => []
  }

  datatype FormatFragment = FormatFragment(end: nat, afterArg: nat, output: BenchWorld.Bytes)
  datatype FragmentPlan = NoFragment | OneFragment(fragment: FormatFragment)

  ghost predicate FormatFragmentRelation(
    format: string,
    args: seq<string>,
    start: nat,
    nextArg: nat,
    end: nat,
    afterArg: nat,
    output: BenchWorld.Bytes
  )
  {
    start < |format| &&
    nextArg <= |args| &&
    if format[start] == '\\' then
      start + 1 < |format| &&
      if format[start + 1] == 'n' then
        end == start + 2 && afterArg == nextArg && output == ['\n']
      else if format[start + 1] == 't' then
        end == start + 2 && afterArg == nextArg && output == ['\t']
      else if format[start + 1] == '\\' then
        end == start + 2 && afterArg == nextArg && output == ['\\']
      else if format[start + 1] == '0' then
        afterArg == nextArg &&
        if start + 2 == |format| || !BenchWorld.IsOctalDigit(format[start + 2]) then
          end == start + 2 && output == [0 as char]
        else if start + 3 == |format| || !BenchWorld.IsOctalDigit(format[start + 3]) then
          end == start + 3 &&
          output == [BenchWorld.CharToDigit(format[start + 2]) as char]
        else
          end == start + 4 &&
          output == [(BenchWorld.CharToDigit(format[start + 2]) * 8 +
                      BenchWorld.CharToDigit(format[start + 3])) as char]
      else
        false
    else if format[start] == '%' then
      start + 1 < |format| &&
      if format[start + 1] == '%' then
        end == start + 2 && afterArg == nextArg && output == ['%']
      else if format[start + 1] == 's' then
        end == start + 2 &&
        if nextArg < |args| then
          afterArg == nextArg + 1 && output == Utf8.Encode(args[nextArg])
        else
          afterArg == nextArg && output == []
      else
        false
    else
      end == start + 1 && afterArg == nextArg && output == Utf8.EncodeChar(format[start])
  }

  datatype FormatDerivation =
    FormatDone |
    FormatStep(fragment: FormatFragment, restOutput: BenchWorld.Bytes, rest: FormatDerivation)

  ghost predicate FormatDerivationRelation(
    format: string,
    args: seq<string>,
    start: nat,
    startArg: nat,
    used: nat,
    output: BenchWorld.Bytes,
    derivation: FormatDerivation
  )
    decreases derivation
  {
    start <= |format| &&
    startArg <= used <= |args| &&
    match derivation
    case FormatDone =>
      start == |format| && used == startArg && output == []
    case FormatStep(fragment, restOutput, rest) =>
      FormatFragmentRelation(
        format, args, start, startArg,
        fragment.end, fragment.afterArg, fragment.output) &&
      output == fragment.output + restOutput &&
      FormatDerivationRelation(
        format, args, fragment.end, fragment.afterArg, used, restOutput, rest)
  }

  ghost predicate FormatPassRelation(
    format: string,
    args: seq<string>,
    startArg: nat,
    used: nat,
    output: BenchWorld.Bytes
  )
  {
    exists derivation: FormatDerivation ::
      FormatDerivationRelation(format, args, 0, startArg, used, output, derivation)
  }

  datatype RepeatedDerivation =
    RepeatedDone |
    RepeatedStep(nextArg: nat, passOutput: BenchWorld.Bytes,
                 restOutput: BenchWorld.Bytes, rest: RepeatedDerivation)

  ghost predicate RepeatedPassesFromRelation(
    format: string,
    args: seq<string>,
    startArg: nat,
    output: BenchWorld.Bytes,
    derivation: RepeatedDerivation
  )
    decreases derivation
  {
    match derivation
    case RepeatedDone =>
      startArg == |args| && output == []
    case RepeatedStep(nextArg, passOutput, restOutput, rest) =>
      startArg < nextArg <= |args| &&
      FormatPassRelation(format, args, startArg, nextArg, passOutput) &&
      output == passOutput + restOutput &&
      RepeatedPassesFromRelation(format, args, nextArg, restOutput, rest)
  }

  ghost predicate RenderRelation(
    format: string,
    args: seq<string>,
    ok: bool,
    output: BenchWorld.Bytes,
    stderr: BenchWorld.Bytes
  )
  {
    if exists passOutput: BenchWorld.Bytes, used: nat ::
         FormatPassRelation(format, args, 0, used, passOutput) then
      ok &&
      (exists passOutput: BenchWorld.Bytes, used: nat ::
         FormatPassRelation(format, args, 0, used, passOutput) &&
         (if used == 0 then
            output == passOutput &&
            stderr == (if |args| == 0 then [] else ExcessArgumentsWarning(args[0]))
          else
            stderr == [] &&
            (exists derivation: RepeatedDerivation ::
               RepeatedPassesFromRelation(format, args, 0, output, derivation))))
    else
      !ok && output == [] && stderr == UnsupportedFormatMessage()
  }

  ghost predicate EvaluationRelation(
    raw: Schema.PrintfCmdRaw,
    stdout: BenchWorld.Bytes,
    stderr: BenchWorld.Bytes,
    code: int
  )
  {
    if Schema.HelpSelected(raw) then
      stdout == HelpText() && stderr == RequestExcessWarning(raw) && code == 0
    else if Schema.VersionSelected(raw) then
      stdout == VersionText() && stderr == RequestExcessWarning(raw) && code == 0
    else if |raw.operands| == 0 then
      stdout == [] && stderr == MissingOperandMessage() && code == 1
    else
      (code == 0 || code == 1) &&
      RenderRelation(
        raw.operands[0], raw.operands[1..], code == 0, stdout, stderr
      )
  }

  twostate predicate Spec(raw: Schema.PrintfCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion
  {
    exists stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes ::
      EvaluationRelation(raw, stdout, stderr, exit) &&
      io.stdout() == old(io.stdout()) + stdout &&
      io.stderr() == old(io.stderr()) + stderr
  }
}
