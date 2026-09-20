include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "FactorSchema.dfy"

module FactorSpec {
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = FactorSchema




  function HelpTextSpec(): BenchWorld.Bytes
  {
    "Usage: factor [OPTION]... [NUMBER]...\n"
    + "Print prime factors for each NUMBER, or read numbers from standard input.\n"
    + "\n"
    + "  -h, --exponents\n"
    + "         print factors as p^e instead of repeating p\n"
    + "      --help\n"
    + "         display this help and exit\n"
    + "      --version\n"
    + "         output version information and exit\n"
  }

  function VersionTextSpec(): BenchWorld.Bytes
  {
    "factor (GNU coreutils) 9.10.13-2cf49\n"
    + "Written by Jim Meyering and the GNU coreutils team.\n"
  }

  function HelpSelected(raw: Schema.FactorCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex)
  }

  function VersionSelected(raw: Schema.FactorCmdRaw): bool
  {
    raw.seenVersion &&
    (!raw.seenHelp || raw.versionTokenIndex < raw.helpTokenIndex)
  }

  function IsWhitespace(ch: char): bool
  {
    ch == ' ' || ch == '\t' || ch == '\n'
  }

  function IsDigit(ch: char): bool
  {
    '0' <= ch && ch <= '9'
  }

  ghost predicate WhitespaceOnly(text: string)
  {
    forall i :: 0 <= i < |text| ==> IsWhitespace(text[i])
  }

  ghost predicate TrimmedTokenRelation(token: string, trimmed: string)
  {
    exists leading: string, trailing: string ::
      token == leading + trimmed + trailing &&
      WhitespaceOnly(leading) &&
      WhitespaceOnly(trailing) &&
      (|trimmed| == 0 ||
       (!IsWhitespace(trimmed[0]) &&
        !IsWhitespace(trimmed[|trimmed| - 1])))
  }

  ghost predicate DecimalTrace(
    text: string,
    start: nat,
    value: int,
    prefixes: seq<int>
  )
  {
    start < |text| &&
    |prefixes| == |text| - start + 1 &&
    prefixes[0] == 0 &&
    prefixes[|prefixes| - 1] == value &&
    (forall i {:trigger text[start + i]} :: 0 <= i < |text| - start ==>
                                              IsDigit(text[start + i])) &&
    forall i {:trigger prefixes[i + 1]} :: 0 <= i < |text| - start ==>
                                             prefixes[i + 1] ==
                                             prefixes[i] * 10 + (text[start + i] as int - '0' as int)
  }

  ghost predicate DecimalRelation(text: string, start: nat, value: int)
  {
    exists prefixes: seq<int> :: DecimalTrace(text, start, value, prefixes)
  }

  ghost predicate CanonicalDecimalRelation(value: int, text: string)
  {
    0 <= value &&
    DecimalRelation(text, 0, value) &&
    (|text| == 1 || text[0] != '0')
  }

  function Product(values: seq<int>): int
    decreases |values|
  {
    if |values| == 0 then 1 else values[0] * Product(values[1..])
  }

  ghost predicate Divides(divisor: int, value: int)
  {
    0 < divisor &&
    exists quotient: nat :: value == divisor * quotient
  }

  ghost predicate Prime(value: int)
  {
    2 <= value &&
    forall divisor :: 2 <= divisor && divisor * divisor <= value ==>
                        !Divides(divisor, value)
  }

  ghost predicate Nondecreasing(values: seq<int>)
  {
    forall i :: 0 <= i && i + 1 < |values| ==> values[i] <= values[i + 1]
  }

  ghost predicate SuffixMinimums(values: seq<int>)
  {
    forall i, j :: 0 <= i <= j < |values| ==> values[i] <= values[j]
  }

  ghost predicate PrimeFactorizationRelation(value: int, factors: seq<int>)
  {
    |factors| > 0 &&
    Product(factors) == value &&
    (forall i :: 0 <= i < |factors| ==> Prime(factors[i])) &&
    Nondecreasing(factors)
  }

  ghost predicate FragmentsConcatenate(
    fragments: seq<BenchWorld.Bytes>,
    combined: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|cuts| - 1] == |combined| &&
    forall i {:trigger cuts[i]} :: 0 <= i < |fragments| ==>
                                     cuts[i] <= cuts[i + 1] &&
                                     cuts[i + 1] <= |combined| &&
                                     cuts[i + 1] == cuts[i] + |fragments[i]| &&
                                     combined[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate FactorPieceRelation(
    factors: seq<int>,
    lo: nat,
    hi: nat,
    exponents: bool,
    piece: BenchWorld.Bytes
  )
  {
    lo < hi <= |factors| &&
    if !exponents then
      hi == lo + 1 &&
      CanonicalDecimalRelation(factors[lo], piece)
    else
      (forall i :: lo <= i < hi ==> factors[i] == factors[lo]) &&
      (lo == 0 || factors[lo - 1] != factors[lo]) &&
      (hi == |factors| || factors[hi] != factors[lo]) &&
      exists primeText: BenchWorld.Bytes ::
        CanonicalDecimalRelation(factors[lo], primeText) &&
        if hi - lo == 1 then
          piece == primeText
        else
          exists countText: BenchWorld.Bytes ::
            CanonicalDecimalRelation(hi - lo, countText) &&
            piece == primeText + ['^'] + countText
  }

  ghost predicate FactorOutputPartition(
    factors: seq<int>,
    exponents: bool,
    output: BenchWorld.Bytes,
    factorCuts: seq<nat>,
    pieces: seq<BenchWorld.Bytes>,
    outputCuts: seq<nat>,
    fragments: seq<BenchWorld.Bytes>
  )
  {
    |factorCuts| == |pieces| + 1 &&
    factorCuts[0] == 0 &&
    factorCuts[|factorCuts| - 1] == |factors| &&
    (forall i :: 0 <= i < |pieces| ==> factorCuts[i] < factorCuts[i + 1]) &&
    (forall i :: 0 <= i < |pieces| ==>
                   FactorPieceRelation(
                     factors, factorCuts[i], factorCuts[i + 1], exponents, pieces[i]
                   )) &&
    |fragments| == |pieces| &&
    (forall i :: 0 <= i < |pieces| ==>
                   fragments[i] == pieces[i] +
                   (if i + 1 < |pieces| then [' '] else [])) &&
    FragmentsConcatenate(fragments, output, outputCuts)
  }

  ghost predicate FactorOutputRelation(
    factors: seq<int>,
    exponents: bool,
    output: BenchWorld.Bytes
  )
  {
    exists factorCuts: seq<nat>,
      pieces: seq<BenchWorld.Bytes>,
      outputCuts: seq<nat>,
      fragments: seq<BenchWorld.Bytes> ::
      FactorOutputPartition(
        factors, exponents, output,
        factorCuts, pieces, outputCuts, fragments
      )
  }

  ghost predicate ValueOutputRelation(
    value: int,
    exponents: bool,
    output: BenchWorld.Bytes
  )
  {
    exists valueText: BenchWorld.Bytes ::
      CanonicalDecimalRelation(value, valueText) &&
      if value <= 1 then
        output == valueText + [':', '\n']
      else
        exists factors: seq<int>, factorText: BenchWorld.Bytes ::
          PrimeFactorizationRelation(value, factors) &&
          FactorOutputRelation(factors, exponents, factorText) &&
          output == valueText + [':', ' '] + factorText + ['\n']
  }

  function InvalidTokenMessage(token: string): BenchWorld.Bytes
  {
    "factor: " + QuoteDiagnosticToken(token) + " is not a valid positive integer\n"
  }

  function QuoteDiagnosticToken(token: string): BenchWorld.Bytes
  {
    "'" + EscapeDiagnosticToken(token) + "'"
  }

  function OctalDigit(d: int): char
  {
    if 0 <= d && d < 8 then
      (d + ('0' as int)) as char
    else
      '0'
  }

  function OctalEscape(ch: char): BenchWorld.Bytes
  {
    var code := ch as int;
    "\\" + [OctalDigit((code / 64) % 8), OctalDigit((code / 8) % 8), OctalDigit(code % 8)]
  }

  function ShouldOctalEscape(ch: char): bool
  {
    (ch as int) < 32 || 126 < (ch as int)
  }

  function HasNamedEscape(ch: char): bool
  {
    var code := ch as int;
    7 <= code <= 13
  }

  function NamedEscape(ch: char): BenchWorld.Bytes
  {
    var code := ch as int;
    if code == 7 then
      "\\a"
    else if code == 8 then
      "\\b"
    else if code == 9 then
      "\\t"
    else if code == 10 then
      "\\n"
    else if code == 11 then
      "\\v"
    else if code == 12 then
      "\\f"
    else if code == 13 then
      "\\r"
    else
      []
  }

  function EscapeDiagnosticToken(token: string): BenchWorld.Bytes
    decreases |token|
  {
    if |token| == 0 then
      []
    else if HasNamedEscape(token[0]) then
      NamedEscape(token[0]) + EscapeDiagnosticToken(token[1..])
    else if ShouldOctalEscape(token[0]) then
      OctalEscape(token[0]) + EscapeDiagnosticToken(token[1..])
    else if token[0] == "\\"[0] || token[0] == "'"[0] then
      "\\" + [token[0]] + EscapeDiagnosticToken(token[1..])
    else
      [token[0]] + EscapeDiagnosticToken(token[1..])
  }

  ghost predicate DigitsFrom(text: string, start: nat)
  {
    start < |text| &&
    forall i :: start <= i < |text| ==> IsDigit(text[i])
  }

  ghost predicate TokenRelation(
    token: string,
    exponents: bool,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool
  )
  {
    exists trimmed: string ::
      TrimmedTokenRelation(token, trimmed) &&
      if |trimmed| == 0 || trimmed[0] == '-' then
        output == [] &&
        errorOutput == InvalidTokenMessage(trimmed) &&
        hadError
      else
        var start: nat := if trimmed[0] == '+' then 1 else 0;
        if !DigitsFrom(trimmed, start) then
          output == [] &&
          errorOutput == InvalidTokenMessage(trimmed) &&
          hadError
        else
          exists value: int ::
            DecimalRelation(trimmed, start, value) &&
            ValueOutputRelation(value, exponents, output) &&
            errorOutput == [] &&
            !hadError
  }

  ghost predicate NulTailRelation(
    text: BenchWorld.Bytes,
    nulIndex: nat,
    next: nat
  )
  {
    nulIndex < next <= |text| &&
    ((next == |text| &&
      (forall i :: nulIndex <= i < next ==>
                     !IsWhitespace(text[i]))) ||
     (IsWhitespace(text[next - 1]) &&
      (forall i :: nulIndex <= i < next - 1 ==>
                     !IsWhitespace(text[i])))
    )
  }

  ghost predicate InputTokenItemRelation(
    text: BenchWorld.Bytes,
    token: string,
    cursor: nat,
    start: nat,
    end: nat,
    next: nat
  )
  {
    cursor <= start <= end <= |text| &&
    (forall j :: cursor <= j < start ==>
                   IsWhitespace(text[j])) &&
    start < |text| &&
    !IsWhitespace(text[start]) &&
    (if text[start] == '\0' then
       end == start &&
       token == "" &&
       NulTailRelation(text, start, next)
     else
       start < end &&
       token == text[start..end] &&
       (forall j :: start <= j < end ==>
                      !IsWhitespace(text[j]) && text[j] != '\0') &&
       (end == |text| ||
        IsWhitespace(text[end]) ||
        text[end] == '\0') &&
       (if end < |text| && text[end] == '\0'
        then NulTailRelation(text, end, next)
        else next == end))
  }

  ghost predicate InputTokenPartitionFrom(
    text: BenchWorld.Bytes,
    initial: nat,
    tokens: seq<string>,
    cursors: seq<nat>,
    starts: seq<nat>,
    ends: seq<nat>
  )
  {
    |cursors| == |tokens| + 1 &&
    |starts| == |tokens| &&
    |ends| == |tokens| &&
    cursors[0] == initial &&
    (forall i :: 0 <= i < |tokens| ==>
                   InputTokenItemRelation(
                     text, tokens[i],
                     cursors[i], starts[i], ends[i], cursors[i + 1]
                   )) &&
    cursors[|tokens|] <= |text| &&
    (forall i :: cursors[|tokens|] <= i < |text| ==>
                   IsWhitespace(text[i]))
  }

  ghost predicate InputTokensFromRelation(
    text: BenchWorld.Bytes,
    initial: nat,
    tokens: seq<string>
  )
  {
    exists cursors: seq<nat>, starts: seq<nat>, ends: seq<nat> ::
      InputTokenPartitionFrom(
        text, initial, tokens, cursors, starts, ends
      )
  }

  ghost predicate InputTokensRelation(
    text: BenchWorld.Bytes,
    tokens: seq<string>
  )
  {
    InputTokensFromRelation(text, 0, tokens)
  }

  ghost predicate RunRelation(
    tokens: seq<string>,
    exponents: bool,
    output: BenchWorld.Bytes,
    errorOutput: BenchWorld.Bytes,
    hadError: bool
  )
    decreases |tokens|
  {
    if |tokens| == 0 then
      output == [] && errorOutput == [] && !hadError
    else
      exists headOutput: BenchWorld.Bytes,
        headError: BenchWorld.Bytes,
        headHadError: bool,
        tailOutput: BenchWorld.Bytes,
        tailError: BenchWorld.Bytes,
        tailHadError: bool ::
        TokenRelation(
          tokens[0], exponents,
          headOutput, headError, headHadError
        ) &&
        RunRelation(
          tokens[1..], exponents,
          tailOutput, tailError, tailHadError
        ) &&
        output == headOutput + tailOutput &&
        errorOutput == headError + tailError &&
        hadError == (headHadError || tailHadError)
  }

  twostate predicate Spec(raw: Schema.FactorCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if HelpSelected(raw) then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if VersionSelected(raw) then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      io.stdin() ==
      (if |raw.operands| > 0
       then old(io.stdin())
       else IOContract.AfterReadStdinFields(old(io.stdin()))) &&
      exists tokens: seq<string>,
        output: BenchWorld.Bytes,
        errorOutput: BenchWorld.Bytes,
        hadError: bool ::
        (if |raw.operands| > 0
         then tokens == raw.operands
         else InputTokensRelation(old(io.stdin()), tokens)) &&
        RunRelation(tokens, raw.seenExponents, output, errorOutput, hadError) &&
        io.stdout() == old(io.stdout()) + output &&
        io.stderr() == old(io.stderr()) + errorOutput &&
        exit == (if hadError then 1 else 0)
  }
}
