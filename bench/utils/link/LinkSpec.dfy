include "LinkSchema.dfy"
include "../../core/IO.dfy"
include "../../core/Utf8.dfy"
include "../../core/CliModel.dfy"

module LinkSpec {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = LinkSchema
  import Utf8 = Utf8Semantics
  import CliModel
  import C = IOContract

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: link FILE1 FILE2\n"
    + "  or:  link OPTION\n"
    + "Call the link function to create a link named FILE2 to an existing FILE1.\n"
    + "\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
    + "\n"
    + "Report bugs to: bug-coreutils@gnu.org\n"
    + "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n"
    + "General help using GNU software: <https://www.gnu.org/gethelp/>\n"
    + "Report any translation bugs to <https://translationproject.org/team/>\n"
    + "Full documentation <https://www.gnu.org/software/coreutils/link>\n"
    + "or available locally via: info '(coreutils) link invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "link (GNU coreutils) 9.10.13-2cf49\n"
    + "Copyright (C) 2026 Free Software Foundation, Inc.\n"
    + "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n"
    + "This is free software: you are free to change and redistribute it.\n"
    + "There is NO WARRANTY, to the extent permitted by law.\n"
    + "\n"
    + "Written by Michael Stone.\n"
  }

  function LongOptionName(token: string): string
  {
    var eq := CliModel.FindChar(token, '=');
    var name := if eq >= 0 then token[..eq] else token;
    if |name| > 2 && CliModel.HasPrefix(name, "--") then
      var abbreviation := name[2..];
      if CliModel.HasPrefix("help", abbreviation) then "--help"
      else if CliModel.HasPrefix("version", abbreviation) then "--version"
      else name
    else name
  }

  function ParseErrorText(err: CliTypes.ParseError): BenchWorld.Bytes
  {
    var text := if err.kind == CliTypes.UnknownOption then
        if |err.rawToken| > 2 && err.rawToken[0] == '-' && err.rawToken[1] == '-' then
          "link: unrecognized option '" + err.rawToken + "'\n" +
          "Try 'link --help' for more information.\n"
        else if |err.rawToken| > 1 && err.rawToken[0] == '-' then
          "link: invalid option -- '" + [err.rawToken[1]] + "'\n" +
          "Try 'link --help' for more information.\n"
        else
          "link: invalid option\nTry 'link --help' for more information.\n"
      else if err.kind == CliTypes.UnexpectedValue then
        "link: option '" + LongOptionName(err.rawToken) +
        "' doesn't allow an argument\n" +
        "Try 'link --help' for more information.\n"
      else if err.kind == CliTypes.Ambiguous then
        "link: option '" + err.rawToken + "' is ambiguous\n" +
        "Try 'link --help' for more information.\n"
      else
        "link: " +
        (if err.kind == CliTypes.MissingValue
        then "missing option value"
        else "parse error") +
        " at token '" + err.rawToken + "'\n";
    Utf8.Encode(text)
  }

  twostate predicate LinkResult(
    io: BenchIO.IO,
    source: BenchWorld.Path,
    target: BenchWorld.Path,
    ok: bool,
    err: int
  )
    reads io.fsRegion, io.nowRegion, io.trustedFilesystemRegion
  {
    C.CreateHardLinkSpec(
      old(io.fs()),
      old(io.now()),
      old(io.trustedFilesystem()),
      io.fs(),
      source,
      target,
      ok,
      err
    )
  }

  function MissingOperandText(): BenchWorld.Bytes
  {
    "link: missing operand\n"
    + "Try 'link --help' for more information.\n"
  }

  function MissingOperandAfterText(
    quotedSource: BenchWorld.Bytes
  ): BenchWorld.Bytes
  {
    "link: missing operand after " + quotedSource + "\n"
    + "Try 'link --help' for more information.\n"
  }

  function ExtraOperandText(quotedOperand: BenchWorld.Bytes): BenchWorld.Bytes
  {
    "link: extra operand " + quotedOperand + "\n"
    + "Try 'link --help' for more information.\n"
  }

  function CannotCreateLinkText(
    quotedTarget: BenchWorld.Bytes,
    quotedSource: BenchWorld.Bytes,
    reason: string
  ): BenchWorld.Bytes
  {
    "link: cannot create link " + quotedTarget + " to " + quotedSource + ": "
    + Utf8.Encode(reason) + "\n"
  }

  twostate predicate Spec(raw: Schema.LinkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if raw.mode == Schema.ModeHelp then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if raw.mode == Schema.ModeVersion then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if raw.mode != Schema.ModeRun then
      match raw.mode
      case ModeExtraOperand(operand) =>
        io.fs() == old(io.fs()) &&
        io.stdout() == old(io.stdout()) &&
        io.stderr() == old(io.stderr()) +
          ExtraOperandText(C.QuoteArgumentResult(Utf8.Encode(operand))) &&
        exit == 1
      case _ => false
    else if |raw.operands| == 0 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) + MissingOperandText() &&
      exit == 1
    else if |raw.operands| == 1 then
      io.fs() == old(io.fs()) &&
      io.stdout() == old(io.stdout()) &&
      io.stderr() == old(io.stderr()) +
        MissingOperandAfterText(
          C.QuoteArgumentResult(Utf8.Encode(raw.operands[0]))
        ) &&
      exit == 1
    else
      exists ok: bool, err: int ::
        LinkResult(io, raw.operands[0], raw.operands[1], ok, err) &&
        io.stdout() == old(io.stdout()) &&
        (if ok then
          io.stderr() == old(io.stderr()) && exit == 0
        else
          io.stderr() == old(io.stderr()) +
            CannotCreateLinkText(C.QuoteafPathResult(raw.operands[1]), C.QuoteafPathResult(raw.operands[0]), C.CLocaleErrnoTextResult(err)) &&
          exit == 1)
  }
}
