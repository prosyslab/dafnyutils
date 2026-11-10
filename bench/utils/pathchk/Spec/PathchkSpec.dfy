include "../Spec/PathchkSchema.dfy"
include "../../../core/IO.dfy"
include "../../../core/Utf8.dfy"
include "../../../core/StringEscaping.dfy"

module PathchkSpec {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = PathchkSchema
  import Utf8 = Utf8Semantics
  import Quote = StringEscaping
  import StreamContract = IOContract

  const PathByteLimit: nat := 255
  const ComponentByteLimit: nat := 14

  ghost predicate DecimalTextWitness(n: nat, text: BenchWorld.Bytes, values: seq<nat>)
  {
    |text| > 0 &&
    (|text| == 1 || text[0] != '0') &&
    |values| == |text| + 1 && values[0] == 0 && values[|text|] == n &&
    forall i: nat | i < |text| ::
      '0' <= text[i] <= '9' &&
      values[i + 1] == values[i] * 10 + (text[i] as int - '0' as int)
  }

  ghost predicate DecimalText(n: nat, text: BenchWorld.Bytes)
  {
    exists values: seq<nat> :: DecimalTextWitness(n, text, values)
  }

  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: pathchk [OPTION]... NAME...\n" +
    "Diagnose invalid or non-portable file names.\n\n" +
    "  -p     check for most POSIX systems\n" +
    "  -P     check for empty names and leading \"-\"\n" +
    "      --portability\n" +
    "         check for all POSIX systems (equivalent to -p -P)\n" +
    "      --help\n         display this help and exit\n" +
    "      --version\n         output version information and exit\n\n" +
    "Report bugs to: bug-coreutils@gnu.org\n" +
    "GNU coreutils home page: <https://www.gnu.org/software/coreutils/>\n" +
    "General help using GNU software: <https://www.gnu.org/gethelp/>\n" +
    "Report any translation bugs to <https://translationproject.org/team/>\n" +
    "Full documentation <https://www.gnu.org/software/coreutils/pathchk>\n" +
    "or available locally via: info '(coreutils) pathchk invocation'\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "pathchk (GNU coreutils) 9.10.13-2cf49\n" +
    "Copyright (C) 2026 Free Software Foundation, Inc.\n" +
    "License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.\n" +
    "This is free software: you are free to change and redistribute it.\n" +
    "There is NO WARRANTY, to the extent permitted by law.\n\n" +
    "Written by Paul Eggert, David MacKenzie, and Jim Meyering.\n"
  }

  function ShortOptionError(err: CliTypes.ParseError): bool
  {
    err.kind == CliTypes.UnknownOption && |err.rawToken| > 1 && err.rawToken[0] == '-' &&
    !(|err.rawToken| > 2 && err.rawToken[..2] == "--")
  }

  ghost predicate ShortOptionPosition(token: string, index: nat)
  {
    1 <= index < |token| &&
    (forall i: nat | 1 <= i < index :: token[i] in "pP") &&
    (token[index] !in "pP" || index + 1 == |token|)
  }

  function UnknownShortText(byte: BenchWorld.RawByte): BenchWorld.Bytes
  {
    "pathchk: invalid option -- '" + [byte] + "'\n" + TryHelpText()
  }

  function LongOptionName(token: string): string
  {
    if |token| > 2 && token[..2] == "--" then
      if token[2] == 'p' then "--portability"
      else if token[2] == 'h' then "--help"
      else if token[2] == 'v' then "--version"
      else token
    else token
  }

  ghost predicate ParseErrorText(err: CliTypes.ParseError, msg: BenchWorld.Bytes)
  {
    if ShortOptionError(err) then
      exists index: nat :: ShortOptionPosition(err.rawToken, index) &&
                           msg == UnknownShortText(Utf8.EncodeChar(err.rawToken[index])[0])
    else msg == ParseErrorMessage(err, Utf8.Encode(err.rawToken))
  }

  function ParseErrorMessage(err: CliTypes.ParseError, token: BenchWorld.Bytes): BenchWorld.Bytes
    requires !ShortOptionError(err)
  {
    if err.kind == CliTypes.UnknownOption then
      if |err.rawToken| > 2 && err.rawToken[..2] == "--" then
        "pathchk: unrecognized option '" + token + "'\n" + TryHelpText()
      else "pathchk: invalid option\n" + TryHelpText()
    else if err.kind == CliTypes.UnexpectedValue then
      "pathchk: option '" + Utf8.Encode(LongOptionName(err.rawToken)) +
      "' doesn't allow an argument\n" + TryHelpText()
    else if err.kind == CliTypes.Ambiguous then
      "pathchk: option '" + token +
      "' is ambiguous; possibilities: '--portability' '--help' '--version'\n" + TryHelpText()
    else
      "pathchk: " + Utf8.Encode(if err.kind == CliTypes.MissingValue then "missing option value" else "parse error") +
      " at token '" + token + "'\n"
  }

  function TryHelpText(): BenchWorld.Bytes
  { "Try 'pathchk --help' for more information.\n" }

  function MissingOperandText(): BenchWorld.Bytes
  { "pathchk: missing operand\n" + TryHelpText() }

  function EmptyNameText(): BenchWorld.Bytes
  { "pathchk: empty file name\n" }

  function LeadingHyphenText(path: string): BenchWorld.Bytes
  {
    LeadingHyphenMessage(Quote.SpecQuoteAfBytes(Utf8.Encode(path)))
  }

  function LeadingHyphenMessage(quotedPath: BenchWorld.Bytes): BenchWorld.Bytes
  {
    "pathchk: leading '-' in a component of file name " + quotedPath + "\n"
  }

  function NonPortableCharacterText(byte: BenchWorld.RawByte, path: string): BenchWorld.Bytes
  {
    NonPortableCharacterMessage(byte, Quote.SpecQuoteAfBytes(Utf8.Encode(path)))
  }

  function NonPortableCharacterMessage(byte: BenchWorld.RawByte, quotedPath: BenchWorld.Bytes): BenchWorld.Bytes
  {
    "pathchk: non-portable character " + Quote.SpecLocaleQuoteBytes([byte]) +
    " in file name " + quotedPath + "\n"
  }

  function PathLengthText(
    limitText: BenchWorld.Bytes,
    lengthText: BenchWorld.Bytes,
    path: string
  ): BenchWorld.Bytes
  {
    PathLengthMessage(limitText, lengthText, Quote.SpecQuoteAfBytes(Utf8.Encode(path)))
  }

  function PathLengthMessage(
    limitText: BenchWorld.Bytes, lengthText: BenchWorld.Bytes, quotedPath: BenchWorld.Bytes
  ): BenchWorld.Bytes
  {
    "pathchk: limit " + limitText + " exceeded by length " + lengthText +
    " of file name " + quotedPath + "\n"
  }

  function ComponentLengthText(
    limitText: BenchWorld.Bytes,
    lengthText: BenchWorld.Bytes,
    component: BenchWorld.Bytes
  ): BenchWorld.Bytes
  {
    "pathchk: limit " + limitText + " exceeded by length " + lengthText +
    " of file name component " + Quote.SpecLocaleQuoteBytes(component) + "\n"
  }

  function WriteErrorText(reason: string): BenchWorld.Bytes
  { "pathchk: write error: " + Utf8.Encode(reason) + "\n" }

  function PortableByte(byte: BenchWorld.RawByte): bool
  { byte in "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789._-/" }

  ghost predicate LeadingHyphen(data: BenchWorld.Bytes)
  {
    exists i: nat :: i < |data| && data[i] == '-' && (i == 0 || data[i - 1] == '/')
  }

  ghost predicate Component(data: BenchWorld.Bytes, start: nat, end: nat)
  {
    start < end <= |data| &&
    (start == 0 || data[start - 1] == '/') &&
    (end == |data| || data[end] == '/') &&
    (forall i: nat | start <= i < end :: data[i] != '/')
  }

  ghost predicate FirstNonPortableByte(data: BenchWorld.Bytes, index: nat)
  {
    index < |data| && !PortableByte(data[index]) &&
    (forall i: nat | i < index :: PortableByte(data[i]))
  }

  ghost predicate FirstLongComponent(data: BenchWorld.Bytes, start: nat, end: nat)
  {
    Component(data, start, end) && end - start > ComponentByteLimit &&
    (forall first: nat, last: nat | first < last <= |data| && first < start ::
       Component(data, first, last) ==> last - first <= ComponentByteLimit)
  }

  ghost opaque predicate ValidName(data: BenchWorld.Bytes, extra: bool)
  {
    0 < |data| <= PathByteLimit && (!extra || !LeadingHyphen(data)) &&
    (forall i: nat | i < |data| :: PortableByte(data[i])) &&
    (forall start: nat, end: nat | start < end <= |data| ::
       Component(data, start, end) ==> end - start <= ComponentByteLimit)
  }

  ghost opaque predicate NameDiagnostic(path: string, extra: bool, diagnostics: BenchWorld.Bytes)
  {
    var data := Utf8.Encode(path);
    if extra && LeadingHyphen(data) then
      diagnostics == LeadingHyphenText(path)
    else if |data| == 0 then
      diagnostics == EmptyNameText()
    else if exists i: nat :: i < |data| && !PortableByte(data[i]) then
      exists i: nat :: FirstNonPortableByte(data, i) &&
                       diagnostics == NonPortableCharacterText(data[i], path)
    else if |data| > PathByteLimit then
      exists limitText: BenchWorld.Bytes, lengthText: BenchWorld.Bytes ::
        DecimalText(PathByteLimit, limitText) && DecimalText(|data|, lengthText) &&
        diagnostics == PathLengthText(limitText, lengthText, path)
    else if exists start: nat, end: nat ::
              start < end <= |data| && Component(data, start, end) && end - start > ComponentByteLimit
    then
      exists start: nat, end: nat, limitText: BenchWorld.Bytes, lengthText: BenchWorld.Bytes ::
        FirstLongComponent(data, start, end) &&
        DecimalText(ComponentByteLimit, limitText) && DecimalText(end - start, lengthText) &&
        diagnostics == ComponentLengthText(limitText, lengthText, data[start..end])
    else diagnostics == []
  }

  ghost predicate OrderedDiagnostics(
    paths: seq<string>, extra: bool, diagnostics: BenchWorld.Bytes, cuts: seq<nat>
  )
  {
    |cuts| == |paths| + 1 && cuts[0] == 0 && cuts[|paths|] == |diagnostics| &&
    forall i: nat {:trigger cuts[i]} | i < |paths| ::
      cuts[i] <= cuts[i + 1] <= |diagnostics| &&
      NameDiagnostic(paths[i], extra, diagnostics[cuts[i]..cuts[i + 1]])
  }

  ghost predicate PathchkResult(raw: Schema.PathchkCmdRaw, diagnostics: BenchWorld.Bytes, exit: int)
  {
    |raw.operands| > 0 &&
    exists cuts: seq<nat> ::
      OrderedDiagnostics(raw.operands, raw.checkExtraPortability, diagnostics, cuts) &&
      exit == (if forall i: nat | i < |raw.operands| ::
                    ValidName(Utf8.Encode(raw.operands[i]), raw.checkExtraPortability)
               then 0 else 1)
  }

  function AllowedInput(raw: Schema.PathchkCmdRaw): bool
  {
    raw.mode != Schema.ModeRun || |raw.operands| == 0 || raw.checkBasicPortability
  }

  ghost predicate EmissionOutcomeFields(
    beforeOut: BenchWorld.Bytes,
    beforeErr: BenchWorld.Bytes,
    afterOut: BenchWorld.Bytes,
    afterErr: BenchWorld.Bytes,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    output: BenchWorld.Bytes,
    diagnostics: BenchWorld.Bytes,
    normalExit: int,
    exit: int,
    committed: nat,
    outErr: int,
    errCommitted: nat,
    errErr: int
  )
  {
    (if output == [] then afterOut == beforeOut && committed == 0 && outErr == 0
     else StreamContract.WriteStdoutSpec(beforeOut, observations, afterOut, output, committed, outErr)) &&
    var finalDiagnostics := diagnostics +
                            (if outErr == 0 then [] else WriteErrorText(StreamContract.CLocaleErrnoTextResult(outErr)));
    (if finalDiagnostics == [] then afterErr == beforeErr && errCommitted == 0 && errErr == 0
     else StreamContract.WriteStderrSpec(beforeErr, observations, afterErr, finalDiagnostics, errCommitted, errErr)) &&
    exit == (if outErr != 0 || errErr != 0 then 1 else normalExit)
  }

  ghost predicate EmissionFields(
    beforeOut: BenchWorld.Bytes, beforeErr: BenchWorld.Bytes,
    afterOut: BenchWorld.Bytes, afterErr: BenchWorld.Bytes,
    observations: (BenchWorld.TrustedStreamRequest) -> BenchWorld.TrustedStreamResult,
    output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
    normalExit: int, exit: int
  )
  {
    exists committed: nat, outErr: int, errCommitted: nat, errErr: int ::
      EmissionOutcomeFields(beforeOut, beforeErr, afterOut, afterErr, observations,
                            output, diagnostics, normalExit, exit,
                            committed, outErr, errCommitted, errErr)
  }

  ghost predicate PreparedSpec(
    raw: Schema.PathchkCmdRaw,
    exit: int,
    plannedStdout: BenchWorld.Bytes,
    plannedStderr: BenchWorld.Bytes
  )
  {
    if raw.mode == Schema.ModeHelp then
      plannedStdout == HelpTextSpec() && plannedStderr == [] && exit == 0
    else if raw.mode == Schema.ModeVersion then
      plannedStdout == VersionTextSpec() && plannedStderr == [] && exit == 0
    else if raw.mode == Schema.ModeMissingOperand || |raw.operands| == 0 then
      plannedStdout == [] && plannedStderr == MissingOperandText() && exit == 1
    else raw.checkBasicPortability && plannedStdout == [] && PathchkResult(raw, plannedStderr, exit)
  }

  twostate predicate Spec(raw: Schema.PathchkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    AllowedInput(raw) ==>
      exists output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
        PreparedSpec(raw, normalExit, output, diagnostics) &&
        EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                       io.trustedStreams(), output, diagnostics, normalExit, exit)
  }
}
