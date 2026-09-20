include "../../core/World.dfy"
include "../../core/IO.dfy"
include "SeqSchema.dfy"
include "SeqSpec.dfy"

module SeqCore {
  import BenchIO
  import Utf8 = Utf8Semantics
  import BenchWorld
  import SeqSchema
  import Spec = SeqSpec

  datatype Decimal = Decimal(raw: string, value: int, scale: nat, negativeZero: bool)
  datatype DecimalParse = DecimalOk(number: Decimal) | DecimalErr(token: string)
  datatype Scan = Scan(ok: bool, sawDigit: bool, sawDot: bool, mantissa: int, scale: nat)
  datatype NatScan = NatScan(ok: bool, sawDigit: bool, value: nat)
  datatype ExponentParse = ExponentOk(value: int) | ExponentErr
  datatype NumberPlan =
    | NumbersOk(first: Decimal, step: Decimal, last: Decimal)
    | NumbersErr(stderr: BenchWorld.Bytes)
  datatype RunResult = RunResult(stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes, exit: int)

  function HelpSelected(raw: SeqSchema.SeqCmdRaw): bool
  {
    raw.seenHelp &&
    (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex)
  } by method
  {
    return raw.seenHelp &&
           (!raw.seenVersion || raw.helpTokenIndex <= raw.versionTokenIndex);
  }

  function VersionSelected(raw: SeqSchema.SeqCmdRaw): bool
  {
    raw.seenVersion &&
    (!raw.seenHelp || raw.versionTokenIndex < raw.helpTokenIndex)
  } by method
  {
    return raw.seenVersion &&
           (!raw.seenHelp || raw.versionTokenIndex < raw.helpTokenIndex);
  }

  function Separator(raw: SeqSchema.SeqCmdRaw): BenchWorld.Bytes
  {
    match raw.separator
    case Some(value) => Utf8.Encode(value)
    case None => ['\n']
  } by method
  {
    match raw.separator
    case Some(value) =>
      return Utf8.Encode(value);
    case None =>
      return ['\n'];
  }

  function IsDigit(ch: char): bool
  {
    '0' <= ch && ch <= '9'
  }

  function DigitValue(ch: char): int
    requires IsDigit(ch)
    ensures 0 <= DigitValue(ch) < 10
  {
    (ch as int) - ('0' as int)
  }

  function ScanDecimal(text: string, i: nat, sawDot: bool, sawDigit: bool, mantissa: int, scale: nat): Scan
    requires i <= |text|
    requires 0 <= mantissa
    decreases |text| - i
  {
    if i >= |text| then
      Scan(true, sawDigit, sawDot, mantissa, scale)
    else if IsDigit(text[i]) then
      ScanDecimal(
        text,
        i + 1,
        sawDot,
        true,
        mantissa * 10 + DigitValue(text[i]),
        if sawDot then scale + 1 else scale
      )
    else if text[i] == '.' && !sawDot then
      ScanDecimal(text, i + 1, true, sawDigit, mantissa, scale)
    else
      Scan(false, sawDigit, sawDot, mantissa, scale)
  } by method
  {
    if i >= |text| {
      return Scan(true, sawDigit, sawDot, mantissa, scale);
    } else if '0' <= text[i] <= '9' {
      return ScanDecimal(
          text,
          i + 1,
          sawDot,
          true,
          mantissa * 10 + ((text[i] as int) - ('0' as int)),
          if sawDot then scale + 1 else scale
        );
    } else if text[i] == '.' && !sawDot {
      return ScanDecimal(text, i + 1, true, sawDigit, mantissa, scale);
    } else {
      return Scan(false, sawDigit, sawDot, mantissa, scale);
    }
  }


  function ExponentIndex(text: string, i: nat): int
    requires i <= |text|
    ensures ExponentIndex(text, i) == -1 || i <= ExponentIndex(text, i) < |text|
    decreases |text| - i
  {
    if i >= |text| then
      -1
    else if text[i] == 'e' || text[i] == 'E' then
      i
    else
      ExponentIndex(text, i + 1)
  } by method
  {
    if i >= |text| {
      return -1;
    } else if text[i] == 'e' || text[i] == 'E' {
      return i;
    } else {
      return ExponentIndex(text, i + 1);
    }
  }

  function ScanNat(text: string, i: nat, sawDigit: bool, value: nat): NatScan
    requires i <= |text|
    decreases |text| - i
  {
    if i >= |text| then
      NatScan(true, sawDigit, value)
    else if IsDigit(text[i]) then
      ScanNat(text, i + 1, true, (value * 10 + DigitValue(text[i])) as nat)
    else
      NatScan(false, sawDigit, value)
  } by method
  {
    if i >= |text| {
      return NatScan(true, sawDigit, value);
    } else if '0' <= text[i] <= '9' {
      var digit := (text[i] as int) - ('0' as int);
      return ScanNat(text, i + 1, true, (value * 10 + digit) as nat);
    } else {
      return NatScan(false, sawDigit, value);
    }
  }

  function ParseExponent(text: string): ExponentParse
  {
    if |text| == 0 then
      ExponentErr
    else
      var negative := text[0] == '-';
      var start := if text[0] == '-' || text[0] == '+' then 1 else 0;
      if start >= |text| then
        ExponentErr
      else
        var scanned := ScanNat(text, start, false, 0);
        if scanned.ok && scanned.sawDigit then
          ExponentOk(if negative then -(scanned.value as int) else scanned.value as int)
        else
          ExponentErr
  } by method
  {
    if |text| == 0 {
      return ExponentErr;
    }
    var negative := text[0] == '-';
    var start := if text[0] == '-' || text[0] == '+' then 1 else 0;
    if start >= |text| {
      return ExponentErr;
    }
    var scanned := ScanNat(text, start, false, 0);
    if scanned.ok && scanned.sawDigit {
      return ExponentOk(if negative then -(scanned.value as int) else scanned.value as int);
    }
    return ExponentErr;
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
  } by method
  {
    if exponent >= 0 {
      var positiveExponent := exponent as nat;
      if positiveExponent <= scale {
        return Decimal(token, value, scale - positiveExponent, negativeZero);
      }
      var factor := Pow10(positiveExponent - scale);
      return Decimal(token, value * factor, 0, negativeZero);
    }
    return Decimal(token, value, scale + ((-exponent) as nat), negativeZero);
  }

  function ParseDecimal(token: string): DecimalParse
  {
    if |token| == 0 then
      DecimalErr(token)
    else
      var negative := token[0] == '-';
      var start := if token[0] == '-' || token[0] == '+' then 1 else 0;
      if start >= |token| then
        DecimalErr(token)
      else
        var exponentIndex := ExponentIndex(token, start);
        var mantissaText := if exponentIndex < 0 then token else token[..exponentIndex];
        var scanned := ScanDecimal(mantissaText, start, false, false, 0, 0);
        if scanned.ok && scanned.sawDigit then
          var value := if negative then -scanned.mantissa else scanned.mantissa;
          var negativeZero := negative && scanned.mantissa == 0;
          if exponentIndex < 0 then
            DecimalOk(Decimal(token, value, scanned.scale, negativeZero))
          else
            var exponentText := token[exponentIndex + 1..];
            var exponentParse := ParseExponent(exponentText);
            match exponentParse
            case ExponentErr =>
              DecimalErr(token)
            case ExponentOk(exponent) =>
              DecimalOk(ApplyExponent(token, value, scanned.scale, negativeZero, exponent))
        else
          DecimalErr(token)
  } by method
  {
    if |token| == 0 {
      return DecimalErr(token);
    }
    var negative := token[0] == '-';
    var start := if token[0] == '-' || token[0] == '+' then 1 else 0;
    if start >= |token| {
      return DecimalErr(token);
    }
    var exponentIndex := ExponentIndex(token, start);
    var mantissaText := if exponentIndex < 0 then token else token[..exponentIndex];
    var scanned := ScanDecimal(mantissaText, start, false, false, 0, 0);
    if !scanned.ok || !scanned.sawDigit {
      return DecimalErr(token);
    }
    var value := if negative then -scanned.mantissa else scanned.mantissa;
    var negativeZero := negative && scanned.mantissa == 0;
    if exponentIndex < 0 {
      return DecimalOk(Decimal(token, value, scanned.scale, negativeZero));
    }
    var exponentText := token[exponentIndex + 1..];
    match ParseExponent(exponentText)
    case ExponentErr =>
      return DecimalErr(token);
    case ExponentOk(exponent) =>
      return DecimalOk(ApplyExponent(token, value, scanned.scale, negativeZero, exponent));
  }

  function ParseNumbers(args: seq<string>): NumberPlan
  {
    if |args| == 0 then
      NumbersErr(Spec.MissingOperandMessage())
    else if |args| > 3 then
      NumbersErr(Spec.ExtraOperandMessage(args[3]))
    else
      var firstText := if |args| == 1 then "1" else args[0];
      var stepText := if |args| == 3 then args[1] else "1";
      var lastText := if |args| == 1 then args[0] else if |args| == 2 then args[1] else args[2];
      var firstParse := ParseDecimal(firstText);
      match firstParse
      case DecimalErr(token) =>
        NumbersErr(Spec.InvalidNumberMessage(token))
      case DecimalOk(first) =>
        var stepParse := ParseDecimal(stepText);
        match stepParse
        case DecimalErr(token) =>
          NumbersErr(Spec.InvalidNumberMessage(token))
        case DecimalOk(step) =>
          if step.value == 0 then
            NumbersErr(Spec.ZeroIncrementMessage(step.raw))
          else
            var lastParse := ParseDecimal(lastText);
            match lastParse
            case DecimalErr(token) =>
              NumbersErr(Spec.InvalidNumberMessage(token))
            case DecimalOk(last) =>
              NumbersOk(first, step, last)
  } by method
  {
    if |args| == 0 {
      var message := MissingOperandMessageRuntime();
      return NumbersErr(message);
    }
    if |args| > 3 {
      var message := ExtraOperandMessageRuntime(args[3]);
      return NumbersErr(message);
    }
    var firstText := if |args| == 1 then "1" else args[0];
    var stepText := if |args| == 3 then args[1] else "1";
    var lastText := if |args| == 1 then args[0] else if |args| == 2 then args[1] else args[2];
    match ParseDecimal(firstText)
    case DecimalErr(token) =>
      var message := InvalidNumberMessageRuntime(token);
      return NumbersErr(message);
    case DecimalOk(first) =>
      match ParseDecimal(stepText)
      case DecimalErr(token) =>
        var message := InvalidNumberMessageRuntime(token);
        return NumbersErr(message);
      case DecimalOk(step) =>
        if step.value == 0 {
          var message := ZeroIncrementMessageRuntime(step.raw);
          return NumbersErr(message);
        }
        match ParseDecimal(lastText)
        case DecimalErr(token) =>
          var message := InvalidNumberMessageRuntime(token);
          return NumbersErr(message);
        case DecimalOk(last) =>
          return NumbersOk(first, step, last);
  }

  function MaxNat(a: nat, b: nat): nat
  {
    if a < b then b else a
  } by method
  {
    return if a < b then b else a;
  }

  function MaxScale(first: Decimal, step: Decimal, last: Decimal): nat
  {
    MaxNat(first.scale, MaxNat(step.scale, last.scale))
  } by method
  {
    var stepLast := MaxNat(step.scale, last.scale);
    return MaxNat(first.scale, stepLast);
  }

  function Pow10(n: nat): int
    ensures 1 <= Pow10(n)
    decreases n
  {
    if n == 0 then
      1
    else
      10 * Pow10(n - 1)
  } by method
  {
    if n == 0 {
      return 1;
    }
    return 10 * Pow10(n - 1);
  }

  function Rescale(d: Decimal, scale: nat): int
    requires d.scale <= scale
  {
    d.value * Pow10(scale - d.scale)
  } by method
  {
    return d.value * Pow10(scale - d.scale);
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
  } by method
  {
    if step > 0 {
      if first > last {
        return 0;
      }
      return ((last - first) / step) as nat + 1;
    }
    if first < last {
      return 0;
    }
    return ((first - last) / (-step)) as nat + 1;
  }

  function GenerateValues(current: int, step: int, count: nat): seq<int>
    decreases count
  {
    if count == 0 then
      []
    else
      [current] + GenerateValues(current + step, step, count - 1)
  } by method
  {
    if count == 0 {
      return [];
    }
    return [current] + GenerateValues(current + step, step, count - 1);
  }

  function DigitChar(d: int): char
  {
    if 0 <= d && d < 10 then
      (d + ('0' as int)) as char
    else
      '0'
  } by method
  {
    return if 0 <= d && d < 10 then (d + ('0' as int)) as char else '0';
  }

  function DigitsUnsigned(n: int): BenchWorld.Bytes
    requires 0 <= n
    decreases n
  {
    if n < 10 then
      [DigitChar(n)]
    else
      DigitsUnsigned(n / 10) + [DigitChar(n % 10)]
  } by method
  {
    if n < 10 {
      return [DigitChar(n)];
    }
    return DigitsUnsigned(n / 10) + [DigitChar(n % 10)];
  }

  function Zeros(n: nat): BenchWorld.Bytes
    decreases n
  {
    if n == 0 then [] else ['0'] + Zeros(n - 1)
  } by method
  {
    if n == 0 {
      return [];
    }
    return ['0'] + Zeros(n - 1);
  }

  function LeftPadZeros(text: BenchWorld.Bytes, width: nat): BenchWorld.Bytes
  {
    if width <= |text| then
      text
    else
      Zeros(width - |text|) + text
  } by method
  {
    if width <= |text| {
      return text;
    }
    return Zeros(width - |text|) + text;
  }

  function RenderMagnitude(magnitude: int, scale: nat): BenchWorld.Bytes
    requires 0 <= magnitude
  {
    if scale == 0 then
      DigitsUnsigned(magnitude)
    else
      var divisor := Pow10(scale);
      Spec.DivNonnegative(magnitude, divisor);
      var integerPart := magnitude / divisor;
      var fractionalPart := magnitude % divisor;
      DigitsUnsigned(integerPart) + ['.'] + LeftPadZeros(DigitsUnsigned(fractionalPart), scale)
  } by method
  {
    if scale == 0 {
      return DigitsUnsigned(magnitude);
    }
    var divisor := Pow10(scale);
    var integerPart := magnitude / divisor;
    var fractionalPart := magnitude % divisor;
    Spec.DivNonnegative(magnitude, divisor);
    var integerText := DigitsUnsigned(integerPart);
    var fractionalText := DigitsUnsigned(fractionalPart);
    return integerText + ['.'] + LeftPadZeros(fractionalText, scale);
  }

  function RenderFixed(value: int, scale: nat, negativeZero: bool): BenchWorld.Bytes
  {
    if value < 0 then
      ['-'] + RenderMagnitude(-value, scale)
    else if value == 0 && negativeZero then
      ['-'] + RenderMagnitude(value, scale)
    else
      RenderMagnitude(value, scale)
  } by method
  {
    if value < 0 {
      return ['-'] + RenderMagnitude(-value, scale);
    } else if value == 0 && negativeZero {
      return ['-'] + RenderMagnitude(value, scale);
    }
    return RenderMagnitude(value, scale);
  }

  function RenderValues(values: seq<int>, scale: nat, firstNegativeZero: bool): seq<BenchWorld.Bytes>
    decreases |values|
  {
    if |values| == 0 then
      []
    else
      [RenderFixed(values[0], scale, firstNegativeZero)] + RenderValues(values[1..], scale, false)
  } by method
  {
    if |values| == 0 {
      return [];
    }
    var head := RenderFixed(values[0], scale, firstNegativeZero);
    var tail := RenderValues(values[1..], scale, false);
    return [head] + tail;
  }

  function MaxWidth(items: seq<BenchWorld.Bytes>): nat
    decreases |items|
  {
    if |items| == 0 then
      0
    else
      MaxNat(|items[0]|, MaxWidth(items[1..]))
  } by method
  {
    if |items| == 0 {
      return 0;
    }
    return MaxNat(|items[0]|, MaxWidth(items[1..]));
  }

  function PadNumber(text: BenchWorld.Bytes, width: nat): BenchWorld.Bytes
  {
    if width <= |text| then
      text
    else if |text| > 0 && text[0] == '-' then
      ['-'] + Zeros(width - |text|) + text[1..]
    else
      Zeros(width - |text|) + text
  } by method
  {
    if width <= |text| {
      return text;
    } else if |text| > 0 && text[0] == '-' {
      return ['-'] + Zeros(width - |text|) + text[1..];
    }
    return Zeros(width - |text|) + text;
  }

  function PadValues(items: seq<BenchWorld.Bytes>, width: nat): seq<BenchWorld.Bytes>
    decreases |items|
  {
    if |items| == 0 then
      []
    else
      [PadNumber(items[0], width)] + PadValues(items[1..], width)
  } by method
  {
    if |items| == 0 {
      return [];
    }
    var head := PadNumber(items[0], width);
    var tail := PadValues(items[1..], width);
    return [head] + tail;
  }

  function JoinItems(items: seq<BenchWorld.Bytes>, separator: BenchWorld.Bytes): BenchWorld.Bytes
    decreases |items|
  {
    if |items| == 0 then
      []
    else if |items| == 1 then
      items[0] + ['\n']
    else
      items[0] + separator + JoinItems(items[1..], separator)
  } by method
  {
    if |items| == 0 {
      return [];
    } else if |items| == 1 {
      return items[0] + ['\n'];
    }
    return items[0] + separator + JoinItems(items[1..], separator);
  }

  function RenderSequence(first: Decimal, step: Decimal, last: Decimal, equalWidth: bool, separator: BenchWorld.Bytes): BenchWorld.Bytes
    requires step.value != 0
  {
    var scale := MaxScale(first, step, last);
    var firstValue := Rescale(first, scale);
    var stepValue := Rescale(step, scale);
    var lastValue := Rescale(last, scale);
    var values := GenerateValues(firstValue, stepValue, TermCount(firstValue, stepValue, lastValue));
    var rendered := RenderValues(values, scale, first.negativeZero && first.value == 0);
    var padded := if equalWidth then PadValues(rendered, MaxWidth(rendered)) else rendered;
    JoinItems(padded, separator)
  } by method
  {
    var scale := MaxScale(first, step, last);
    var firstValue := Rescale(first, scale);
    var stepValue := Rescale(step, scale);
    var lastValue := Rescale(last, scale);
    var count := TermCount(firstValue, stepValue, lastValue);
    var values := GenerateValues(firstValue, stepValue, count);
    var rendered := RenderValues(values, scale, first.negativeZero && first.value == 0);
    var padded := if equalWidth then PadValues(rendered, MaxWidth(rendered)) else rendered;
    return JoinItems(padded, separator);
  }

  function Evaluate(raw: SeqSchema.SeqCmdRaw): RunResult
  {
    if HelpSelected(raw) then
      RunResult(Spec.HelpText(), [], 0)
    else if VersionSelected(raw) then
      RunResult(Spec.VersionText(), [], 0)
    else
      var plan := ParseNumbers(raw.operands);
      match plan
      case NumbersErr(stderr) =>
        RunResult([], stderr, 1)
      case NumbersOk(first, step, last) =>
        RunResult(RenderSequence(first, step, last, raw.equalWidth, Separator(raw)), [], 0)
  } by method
  {
    if HelpSelected(raw) {
      var out := GetHelpText();
      return RunResult(out, [], 0);
    }
    if VersionSelected(raw) {
      var out := GetVersionText();
      return RunResult(out, [], 0);
    }
    match ParseNumbers(raw.operands)
    case NumbersErr(stderr) =>
      return RunResult([], stderr, 1);
    case NumbersOk(first, step, last) =>
      var separator := Separator(raw);
      return RunResult(
          RenderSequence(first, step, last, raw.equalWidth, separator),
          [],
          0
        );
  }

  twostate predicate CoreSummary(raw: SeqSchema.SeqCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var result := Evaluate(raw);
    io.stdout() == old(io.stdout()) + result.stdout &&
    io.stderr() == old(io.stderr()) + result.stderr &&
    exit == result.exit
  }

  method GetHelpText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.HelpText()
  {
    out := Spec.HelpText();
  }

  method GetVersionText() returns (out: BenchWorld.Bytes)
    ensures out == Spec.VersionText()
  {
    out := Spec.VersionText();
  }

  method MissingOperandMessageRuntime() returns (message: BenchWorld.Bytes)
    ensures message == Spec.MissingOperandMessage()
  {
    message := Spec.MissingOperandMessage();
  }

  method ExtraOperandMessageRuntime(token: string) returns (message: BenchWorld.Bytes)
    ensures message == Spec.ExtraOperandMessage(token)
  {
    message := Spec.ExtraOperandMessage(token);
  }

  method InvalidNumberMessageRuntime(token: string) returns (message: BenchWorld.Bytes)
    ensures message == Spec.InvalidNumberMessage(token)
  {
    message := Spec.InvalidNumberMessage(token);
  }

  method ZeroIncrementMessageRuntime(token: string) returns (message: BenchWorld.Bytes)
    ensures message == Spec.ZeroIncrementMessage(token)
  {
    message := Spec.ZeroIncrementMessage(token);
  }

  method RunCore(raw: SeqSchema.SeqCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var result := Evaluate(raw);
    io.AppendStdout(result.stdout);
    io.AppendStderr(result.stderr);
    exit := result.exit;
    assert CoreSummary(raw, io, exit);
  }
}
