include "../../core/World.dfy"
include "../../core/IO.dfy"
include "SeqSchema.dfy"

module SeqSpec {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import SeqSchema

  datatype Decimal = Decimal(raw: string, value: int, scale: nat, negativeZero: bool)
  datatype DecimalParse = DecimalOk(number: Decimal) | DecimalErr(token: string)
  datatype NumberPlan =
    | NumbersOk(first: Decimal, step: Decimal, last: Decimal)
    | NumbersErr(stderr: BenchWorld.Bytes)



  function HelpText(): BenchWorld.Bytes
  {
    "Usage: seq [OPTION]... LAST\n"
    + "  or:  seq [OPTION]... FIRST LAST\n"
    + "  or:  seq [OPTION]... FIRST INCREMENT LAST\n"
    + "Print fixed-point decimal sequences in this benchmark model.\n"
    + "\n"
    + "  -s, --separator=STRING   use STRING to separate numbers (default: \\n)\n"
    + "  -w, --equal-width        equalize width by padding with leading zeroes\n"
    + "      --help               display this help and exit\n"
    + "      --version            output version information and exit\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "seq (GNU coreutils) 9.10.13-2cf49\n"
    + "Written by Ulrich Drepper.\n"
  }

  function HelpSelected(raw: SeqSchema.SeqCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex)
  }

  function VersionSelected(raw: SeqSchema.SeqCmdRaw): bool
  {
    raw.seenVersion &&
    (!raw.seenHelp || raw.versionTokenIndex < raw.helpTokenIndex)
  }

  function TryHelp(): BenchWorld.Bytes
  {
    "Try 'seq --help' for more information.\n"
  }

  function Separator(raw: SeqSchema.SeqCmdRaw): BenchWorld.Bytes
  {
    match raw.separator
    case Some(value) => Utf8.Encode(value)
    case None => ['\n']
  }

  function IsDigit(ch: char): bool
  {
    '0' <= ch && ch <= '9'
  }

  function DigitAt(ch: char): int
  {
    (ch as int) - ('0' as int)
  }

  ghost predicate DigitRange(text: string, start: nat, end: nat)
  {
    start <= end <= |text| &&
    forall i: nat | start <= i < end :: IsDigit(text[i])
  }

  function IntSequenceSum(values: seq<int>): int
    decreases |values|
  {
    if |values| == 0 then 0 else values[0] + IntSequenceSum(values[1..])
  }

  function DigitContributions(
    text: string,
    start: nat,
    end: nat,
    dot: int
  ): seq<int>
    requires start <= end <= |text|
    requires dot == -1 || 0 <= dot < end
  {
    seq(end - start, offset requires 0 <= offset < end - start =>
      var position := (start + offset) as nat;
      if position == dot then 0 else
      DigitAt(text[position]) *
      Pow10(end - position - 1 - (if position < dot then 1 else 0)))
  }

  ghost predicate ExponentMarkerRelation(text: string, start: nat, marker: int)
  {
    start <= |text| &&
    if marker == -1 then
      forall position: nat {:trigger text[position]} | start <= position < |text| ::
        text[position] != 'e' && text[position] != 'E'
    else
      start <= marker < |text| &&
      (text[marker] == 'e' || text[marker] == 'E') &&
      forall position: nat {:trigger text[position]} | start <= position < |text| ::
        position == marker || (text[position] != 'e' && text[position] != 'E')
  }

  ghost predicate DotMarkerRelation(
    text: string,
    start: nat,
    end: nat,
    dot: int
  )
  {
    start < end <= |text| &&
    if dot == -1 then
      forall position: nat {:trigger text[position]} | start <= position < end ::
        text[position] != '.'
    else
      start <= dot < end &&
      text[dot] == '.' &&
      start < end - 1 &&
      forall position: nat {:trigger text[position]} | start <= position < end ::
        position == dot || text[position] != '.'
  }

  ghost predicate PositionalValueRelation(
    text: string,
    start: nat,
    end: nat,
    dot: int,
    value: int
  )
  {
    start < end <= |text| &&
    (dot == -1 || start <= dot < end) &&
    value == IntSequenceSum(DigitContributions(text, start, end, dot))
  }

  ghost predicate MantissaRelation(
    text: string,
    start: nat,
    end: nat,
    mantissa: int,
    scale: nat
  )
  {
    start < end <= |text| &&
    exists dot: int ::
      DotMarkerRelation(text, start, end, dot) &&
      (forall position: nat {:trigger text[position]} | start <= position < end ::
         position == dot || IsDigit(text[position])) &&
      PositionalValueRelation(text, start, end, dot, mantissa) &&
      scale == (if dot == -1 then 0 else end - dot - 1)
  }

  ghost predicate ExponentRelation(
    text: string,
    start: nat,
    end: nat,
    exponent: int
  )
  {
    start < end <= |text| &&
    var digitStart := if text[start] == '-' || text[start] == '+' then start + 1 else start;
    digitStart < end &&
    (forall position: nat {:trigger text[position]} | digitStart <= position < end ::
       IsDigit(text[position])) &&
    exists magnitude: int ::
      PositionalValueRelation(text, digitStart, end, -1, magnitude) &&
      exponent == (if text[start] == '-' then -magnitude else magnitude)
  }

  function ApplyExponent(token: string, value: int, scale: nat, negativeZero: bool, exponent: int): Decimal
  {
    if exponent >= 0 then
      var positiveExponent := exponent as nat;
      if positiveExponent <= scale then
        Decimal(token, value, scale - positiveExponent, negativeZero)
      else
        Decimal(token, value * Pow10(positiveExponent - scale), 0, negativeZero)
    else
      Decimal(token, value, scale + ((-exponent) as nat), negativeZero)
  }

  ghost predicate DecimalValueRelation(token: string, number: Decimal)
  {
    exists evidence: DecimalValueWitness
      {:trigger DecimalValueWitnessRelation(token, number, evidence)} ::
      DecimalValueWitnessRelation(token, number, evidence)
  }

  datatype DecimalValueWitness = DecimalValueWitness(
    exponentMarker: int,
    dot: int,
    mantissa: int,
    exponent: int
  )

  ghost predicate DecimalValueWitnessRelation(
    token: string,
    number: Decimal,
    evidence: DecimalValueWitness
  )
  {
    |token| > 0 &&
    var negative := token[0] == '-';
    var start := if token[0] == '-' || token[0] == '+' then 1 else 0;
    start < |token| &&
    ExponentMarkerRelation(token, start, evidence.exponentMarker) &&
    var mantissaText :=
      if evidence.exponentMarker == -1 then token else token[..evidence.exponentMarker];
    DotMarkerRelation(mantissaText, start, |mantissaText|, evidence.dot) &&
    (forall position: nat {:trigger mantissaText[position]}
       | start <= position < |mantissaText| ::
       position == evidence.dot || IsDigit(mantissaText[position])) &&
    PositionalValueRelation(
      mantissaText, start, |mantissaText|, evidence.dot, evidence.mantissa
    ) &&
    var scale :=
      if evidence.dot == -1 then 0 else |mantissaText| - evidence.dot - 1;
    if evidence.exponentMarker == -1 then
      number == Decimal(
        token,
        if negative then -evidence.mantissa else evidence.mantissa,
        scale,
        negative && evidence.mantissa == 0
      )
    else
      var exponentText := token[evidence.exponentMarker + 1..];
      ExponentRelation(
        exponentText, 0, |exponentText|, evidence.exponent
      ) &&
      number == ApplyExponent(
        token,
        if negative then -evidence.mantissa else evidence.mantissa,
        scale,
        negative && evidence.mantissa == 0,
        evidence.exponent
      )
  }

  ghost predicate DecimalParseRelation(token: string, parsed: DecimalParse)
  {
    match parsed
    case DecimalOk(number) => DecimalValueRelation(token, number)
    case DecimalErr(errorToken) =>
      errorToken == token &&
      !(exists number: Decimal :: DecimalValueRelation(token, number))
  }

  function MissingOperandMessage(): BenchWorld.Bytes
  {
    "seq: missing operand\n" + TryHelp()
  }

  function ExtraOperandMessage(token: string): BenchWorld.Bytes
  {
    "seq: extra operand '" + Utf8.Encode(token) + "'\n" + TryHelp()
  }

  function InvalidNumberMessage(token: string): BenchWorld.Bytes
  {
    "seq: invalid floating point argument: '" + Utf8.Encode(token) + "'\n" + TryHelp()
  }

  function ZeroIncrementMessage(token: string): BenchWorld.Bytes
  {
    "seq: invalid Zero increment value: '" + Utf8.Encode(token) + "'\n" + TryHelp()
  }

  ghost predicate NumberPlanRelation(args: seq<string>, plan: NumberPlan)
  {
    if |args| == 0 then
      plan == NumbersErr(MissingOperandMessage())
    else if |args| > 3 then
      plan == NumbersErr(ExtraOperandMessage(args[3]))
    else
      var firstText := if |args| == 1 then "1" else args[0];
      var stepText := if |args| == 3 then args[1] else "1";
      var lastText := if |args| == 1 then args[0] else if |args| == 2 then args[1] else args[2];
      exists firstParse: DecimalParse ::
        DecimalParseRelation(firstText, firstParse) &&
        match firstParse
        case DecimalErr(token) =>
          plan == NumbersErr(InvalidNumberMessage(token))
        case DecimalOk(first) =>
          exists stepParse: DecimalParse ::
            DecimalParseRelation(stepText, stepParse) &&
            match stepParse
            case DecimalErr(token) =>
              plan == NumbersErr(InvalidNumberMessage(token))
            case DecimalOk(step) =>
              if step.value == 0 then
                plan == NumbersErr(ZeroIncrementMessage(step.raw))
              else
                exists lastParse: DecimalParse ::
                  DecimalParseRelation(lastText, lastParse) &&
                  match lastParse
                  case DecimalErr(token) =>
                    plan == NumbersErr(InvalidNumberMessage(token))
                  case DecimalOk(last) =>
                    plan == NumbersOk(first, step, last)
  }

  function MaxNat(a: nat, b: nat): nat
  {
    if a < b then b else a
  }

  function MaxScale(first: Decimal, step: Decimal, last: Decimal): nat
  {
    MaxNat(first.scale, MaxNat(step.scale, last.scale))
  }

  function Pow10(n: nat): int
    ensures 1 <= Pow10(n)
    decreases n
  {
    if n == 0 then
      1
    else
      10 * Pow10(n - 1)
  }

  function Rescale(d: Decimal, scale: nat): int
    requires d.scale <= scale
  {
    d.value * Pow10(scale - d.scale)
  }

  function TermCount(first: int, step: int, last: int): nat
    requires step != 0
  {
    if step > 0 then
      if first > last then
        0
      else
        ((last - first) / step) as nat + 1
    else
    if first < last then
      0
    else
      ((first - last) / (-step)) as nat + 1
  }

  function DigitChar(d: int): char
  {
    if 0 <= d && d < 10 then
      (d + ('0' as int)) as char
    else
      '0'
  }

  function DigitsUnsigned(n: int): BenchWorld.Bytes
    requires 0 <= n
    decreases n
  {
    if n < 10 then
      [DigitChar(n)]
    else
      DigitsUnsigned(n / 10) + [DigitChar(n % 10)]
  }

  function Zeros(n: nat): BenchWorld.Bytes
    decreases n
  {
    if n == 0 then [] else ['0'] + Zeros(n - 1)
  }

  function LeftPadZeros(text: BenchWorld.Bytes, width: nat): BenchWorld.Bytes
  {
    if width <= |text| then
      text
    else
      Zeros(width - |text|) + text
  }

  lemma DivNonnegative(numerator: int, denominator: int)
    requires 0 <= numerator
    requires 0 < denominator
    ensures 0 <= numerator / denominator
  {
  }

  function RenderMagnitude(magnitude: int, scale: nat): BenchWorld.Bytes
    requires 0 <= magnitude
  {
    if scale == 0 then
      DigitsUnsigned(magnitude)
    else
      var divisor := Pow10(scale);
      DivNonnegative(magnitude, divisor);
      var integerPart := magnitude / divisor;
      var fractionalPart := magnitude % divisor;
      DigitsUnsigned(integerPart) + ['.'] + LeftPadZeros(DigitsUnsigned(fractionalPart), scale)
  }

  function RenderFixed(value: int, scale: nat, negativeZero: bool): BenchWorld.Bytes
  {
    if value < 0 then
      ['-'] + RenderMagnitude(-value, scale)
    else if value == 0 && negativeZero then
      ['-'] + RenderMagnitude(value, scale)
    else
      RenderMagnitude(value, scale)
  }

  function PadNumber(text: BenchWorld.Bytes, width: nat): BenchWorld.Bytes
  {
    if width <= |text| then
      text
    else if |text| > 0 && text[0] == '-' then
      ['-'] + Zeros(width - |text|) + text[1..]
    else
      Zeros(width - |text|) + text
  }

  ghost predicate WidthRelation(items: seq<BenchWorld.Bytes>, width: nat)
  {
    (|items| == 0 && width == 0) ||
    (|items| > 0 &&
     (forall i: nat | i < |items| :: |items[i]| <= width) &&
     exists i: nat :: i < |items| && |items[i]| == width)
  }

  ghost predicate SequenceItemsRelation(
    first: Decimal,
    step: Decimal,
    last: Decimal,
    equalWidth: bool,
    rendered: seq<BenchWorld.Bytes>,
    items: seq<BenchWorld.Bytes>,
    width: nat
  )
    requires step.value != 0
  {
    var scale := MaxScale(first, step, last);
    var firstValue := Rescale(first, scale);
    var stepValue := Rescale(step, scale);
    var lastValue := Rescale(last, scale);
    var count := TermCount(firstValue, stepValue, lastValue);
    rendered == seq(count, i requires 0 <= i < count =>
      RenderFixed(
        firstValue + i * stepValue,
        scale,
        i == 0 && first.negativeZero && first.value == 0
      )) &&
    WidthRelation(rendered, width) &&
    items == seq(count, i requires 0 <= i < count =>
      if equalWidth then PadNumber(rendered[i], width) else rendered[i])
  }

  ghost predicate FragmentCutsRelation(
    fragments: seq<BenchWorld.Bytes>,
    output: BenchWorld.Bytes,
    cuts: seq<nat>
  )
  {
    |cuts| == |fragments| + 1 &&
    cuts[0] == 0 &&
    cuts[|fragments|] == |output| &&
    forall i: nat {:trigger cuts[i], cuts[i + 1]} | i < |fragments| ::
      cuts[i] <= cuts[i + 1] <= |output| &&
      output[cuts[i]..cuts[i + 1]] == fragments[i]
  }

  ghost predicate SequenceOutputWitnessRelation(
    first: Decimal,
    step: Decimal,
    last: Decimal,
    equalWidth: bool,
    separator: BenchWorld.Bytes,
    output: BenchWorld.Bytes,
    rendered: seq<BenchWorld.Bytes>,
    items: seq<BenchWorld.Bytes>,
    width: nat,
    fragments: seq<BenchWorld.Bytes>,
    cuts: seq<nat>
  )
    requires step.value != 0
  {
    SequenceItemsRelation(first, step, last, equalWidth, rendered, items, width) &&
    fragments == seq(|items|, i requires 0 <= i < |items| =>
      items[i] + (if i + 1 == |items| then ['\n'] else separator)) &&
    FragmentCutsRelation(fragments, output, cuts)
  }

  ghost predicate SequenceOutputRelation(
    first: Decimal,
    step: Decimal,
    last: Decimal,
    equalWidth: bool,
    separator: BenchWorld.Bytes,
    output: BenchWorld.Bytes
  )
    requires step.value != 0
  {
    exists rendered: seq<BenchWorld.Bytes>,
      items: seq<BenchWorld.Bytes>,
      width: nat,
      fragments: seq<BenchWorld.Bytes>,
      cuts: seq<nat> ::
      SequenceOutputWitnessRelation(
        first,
        step,
        last,
        equalWidth,
        separator,
        output,
        rendered,
        items,
        width,
        fragments,
        cuts
      )
  }

  twostate predicate Spec(raw: SeqSchema.SeqCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if HelpSelected(raw) then
      io.stdout() == old(io.stdout()) + HelpText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if VersionSelected(raw) then
      io.stdout() == old(io.stdout()) + VersionText() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      exists plan: NumberPlan ::
        NumberPlanRelation(raw.operands, plan) &&
        match plan
        case NumbersErr(stderr) =>
          io.stdout() == old(io.stdout()) &&
          io.stderr() == old(io.stderr()) + stderr &&
          exit == 1
        case NumbersOk(first, step, last) =>
          exists stdout: BenchWorld.Bytes ::
            SequenceOutputRelation(
              first,
              step,
              last,
              raw.equalWidth,
              Separator(raw),
              stdout
            ) &&
            io.stdout() == old(io.stdout()) + stdout &&
            io.stderr() == old(io.stderr()) &&
            exit == 0
  }
}
