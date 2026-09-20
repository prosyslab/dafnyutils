include "../../core/World.dfy"
include "../../core/IO.dfy"
include "../../core/IOContract.dfy"
include "FactorSchema.dfy"
include "FactorSpec.dfy"

module FactorCore {
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = FactorSchema
  import Spec = FactorSpec

  datatype TokenResult = TokenOk(out: BenchWorld.Bytes) | TokenErr(err: BenchWorld.Bytes)
  datatype RunResult = RunResult(stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes, hadError: bool)

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

  function TrimLeftWhitespace(text: string): string
    decreases |text|
  {
    if |text| == 0 then
      text
    else if IsWhitespace(text[0]) then
      TrimLeftWhitespace(text[1..])
    else
      text
  } by method {
    var cursor := 0;
    while cursor < |text| && IsWhitespace(text[cursor])
      invariant 0 <= cursor <= |text|
      invariant TrimLeftWhitespace(text) == TrimLeftWhitespace(text[cursor..])
      decreases |text| - cursor
    {
      cursor := cursor + 1;
    }
    return text[cursor..];
  }

  function TrimRightWhitespace(text: string): string
    decreases |text|
  {
    if |text| == 0 then
      text
    else if IsWhitespace(text[|text| - 1]) then
      TrimRightWhitespace(text[..|text| - 1])
    else
      text
  } by method {
    var end := |text|;
    assert text[..end] == text;
    while 0 < end && IsWhitespace(text[end - 1])
      invariant 0 <= end <= |text|
      invariant TrimRightWhitespace(text) == TrimRightWhitespace(text[..end])
      decreases end
    {
      assert text[..end][..end - 1] == text[..end - 1];
      assert TrimRightWhitespace(text[..end]) ==
             TrimRightWhitespace(text[..end - 1]);
      end := end - 1;
    }
    return text[..end];
  }

  function TrimWhitespace(text: string): string
  {
    TrimLeftWhitespace(TrimRightWhitespace(text))
  }

  function AllDigits(text: string, i: nat): bool
    requires i <= |text|
    decreases |text| - i
  {
    if i >= |text| then
      true
    else if !IsDigit(text[i]) then
      false
    else
      AllDigits(text, i + 1)
  } by method {
    var cursor := i;
    while cursor < |text|
      invariant i <= cursor <= |text|
      invariant AllDigits(text, i) == AllDigits(text, cursor)
      decreases |text| - cursor
    {
      if !IsDigit(text[cursor]) {
        return false;
      }
      cursor := cursor + 1;
    }
    return true;
  }

  function ParseDigits(text: string, i: nat, acc: int): int
    requires i <= |text|
    requires AllDigits(text, i)
    ensures 0 <= acc ==> acc <= ParseDigits(text, i, acc)
    decreases |text| - i
  {
    if i >= |text| then
      acc
    else
      ParseDigits(text, i + 1, acc * 10 + (text[i] as int - '0' as int))
  } by method {
    var cursor := i;
    var value := acc;
    while cursor < |text|
      invariant i <= cursor <= |text|
      invariant AllDigits(text, cursor)
      invariant ParseDigits(text, i, acc) == ParseDigits(text, cursor, value)
      invariant 0 <= acc ==> acc <= value
      decreases |text| - cursor
    {
      value := value * 10 + (text[cursor] as int - '0' as int);
      cursor := cursor + 1;
    }
    return value;
  }

  function DigitChar(d: int): BenchWorld.RawByte
  {
    if 0 <= d && d < 10 then
      (d + ('0' as int)) as char
    else
      '0'
  }

  function Digits(n: int): BenchWorld.Bytes
    decreases if n < 0 then 1 - n else n
  {
    if n < 0 then
      ['-'] + Digits(-n)
    else if n < 10 then
      [DigitChar(n)]
    else
      Digits(n / 10) + [DigitChar(n % 10)]
  } by method {
    if n < 0 {
      return ['-'] + Digits(-n);
    }
    var remaining := n;
    var suffix: BenchWorld.Bytes := [];
    while 10 <= remaining
      invariant 0 <= remaining
      invariant Digits(n) == Digits(remaining) + suffix
      decreases remaining
    {
      suffix := [DigitChar(remaining % 10)] + suffix;
      remaining := remaining / 10;
    }
    return [DigitChar(remaining)] + suffix;
  }

  function FactorizeFrom(n: int, d: int): seq<int>
    requires n >= 0
    requires d >= 2
    decreases n, n - d
  {
    if n <= 1 then
      []
    else if d * d > n then
      [n]
    else if n % d == 0 then
      FactorizeQuotientSmaller(n, d);
      [d] + FactorizeFrom(n / d, 2)
    else if d == 2 then
      FactorizeFrom(n, 3)
    else
      FactorizeFrom(n, d + 2)
  } by method {
    var remaining := n;
    var divisor := d;
    var factors: seq<int> := [];
    while 1 < remaining && divisor * divisor <= remaining
      invariant 0 <= remaining
      invariant 2 <= divisor
      invariant FactorizeFrom(n, d) == factors + FactorizeFrom(remaining, divisor)
      decreases remaining, remaining - divisor
    {
      if remaining % divisor == 0 {
        FactorizeQuotientSmaller(remaining, divisor);
        factors := factors + [divisor];
        remaining := remaining / divisor;
        divisor := 2;
      } else if divisor == 2 {
        divisor := 3;
      } else {
        divisor := divisor + 2;
      }
    }
    if 1 < remaining {
      factors := factors + [remaining];
    }
    return factors;
  }

  lemma FactorizeQuotientSmaller(n: int, d: int)
    requires n >= 0
    requires d >= 2
    requires n > 1
    ensures n / d < n
  {
    var q := n / d;
    var r := n % d;
    assert n == d * q + r;
    assert 0 <= r < d;
    if q >= n {
      assert d * q >= 2 * q;
      assert 2 * q >= 2 * n;
      assert n >= 2 * n;
      assert n < 2 * n;
      assert false;
    }
  }

  function Factorize(n: int): seq<int>
    requires n >= 0
  {
    FactorizeFrom(n, 2)
  }

  function CountPrefix(factors: seq<int>, p: int, i: nat): nat
    requires i <= |factors|
    ensures CountPrefix(factors, p, i) <= |factors| - i
    ensures i < |factors| && factors[i] == p ==>
              1 <= CountPrefix(factors, p, i)
    decreases |factors| - i
  {
    if i >= |factors| || factors[i] != p then
      0
    else
      1 + CountPrefix(factors, p, i + 1)
  } by method {
    var cursor := i;
    while cursor < |factors| && factors[cursor] == p
      invariant i <= cursor <= |factors|
      invariant CountPrefix(factors, p, i) ==
                cursor - i + CountPrefix(factors, p, cursor)
      decreases |factors| - cursor
    {
      cursor := cursor + 1;
    }
    return cursor - i;
  }

  function RenderFactors(factors: seq<int>, exponents: bool): BenchWorld.Bytes
    decreases |factors|
  {
    if |factors| == 0 then
      []
    else if !exponents then
      if |factors| == 1 then
        Digits(factors[0])
      else
        Digits(factors[0]) + [' '] + RenderFactors(factors[1..], false)
    else
      var p := factors[0];
      var count := CountPrefix(factors, p, 0);
      var current :=
        if count == 1 then
          Digits(p)
        else
          Digits(p) + ['^'] + Digits(count);
      if count >= |factors| then
        current
      else
        current + [' '] + RenderFactors(factors[count..], true)
  } by method {
    var remaining := factors;
    var output: BenchWorld.Bytes := [];
    while |remaining| > 0
      invariant RenderFactors(factors, exponents) ==
                output + RenderFactors(remaining, exponents)
      decreases |remaining|
    {
      if !exponents {
        var current := Digits(remaining[0]);
        remaining := remaining[1..];
        output := output + current +
        (if |remaining| > 0 then [' '] else []);
      } else {
        var p := remaining[0];
        var count := CountPrefix(remaining, p, 0);
        assert CountPrefix(remaining, p, 0) ==
               1 + CountPrefix(remaining, p, 1);
        assert 0 < count <= |remaining|;
        var current :=
          if count == 1 then
            Digits(p)
          else
            Digits(p) + ['^'] + Digits(count);
        remaining := remaining[count..];
        output := output + current +
        (if |remaining| > 0 then [' '] else []);
      }
    }
    return output;
  }

  function RenderValidValue(value: int, exponents: bool): BenchWorld.Bytes
  {
    if value <= 1 then
      Digits(value) + [':'] + ['\n']
    else
      Digits(value) + [':', ' '] + RenderFactors(Factorize(value), exponents) + ['\n']
  }

  function ProcessToken(token: string, exponents: bool): TokenResult
  {
    var trimmed := TrimWhitespace(token);
    if |trimmed| == 0 then
      TokenErr(Spec.InvalidTokenMessage(trimmed))
    else if trimmed[0] == '-' then
      TokenErr(Spec.InvalidTokenMessage(trimmed))
    else if trimmed[0] == '+' then
      if |trimmed| == 1 || !AllDigits(trimmed, 1) then
        TokenErr(Spec.InvalidTokenMessage(trimmed))
      else
        TokenOk(RenderValidValue(ParseDigits(trimmed, 1, 0), exponents))
    else if AllDigits(trimmed, 0) then
      TokenOk(RenderValidValue(ParseDigits(trimmed, 0, 0), exponents))
    else
      TokenErr(Spec.InvalidTokenMessage(trimmed))
  }

  function SplitWordsFrom(text: BenchWorld.Bytes, i: nat): seq<string>
    requires i <= |text|
    decreases |text| - i
  {
    if i >= |text| then
      []
    else if IsWhitespace(text[i]) then
      SplitWordsFrom(text, i + 1)
    else if text[i] == '\0' then
      [""] + SplitWordsFrom(text, SkipAfterNul(text, i))
    else
      var j := WordEnd(text, i);
      if j < |text| && text[j] == '\0' then
        [text[i..j]] + SplitWordsFrom(text, SkipAfterNul(text, j))
      else
        [text[i..j]] + SplitWordsFrom(text, j)
  } by method {
    var cursor := i;
    var tokens: seq<string> := [];
    while cursor < |text|
      invariant i <= cursor <= |text|
      invariant SplitWordsFrom(text, i) ==
                tokens + SplitWordsFrom(text, cursor)
      decreases |text| - cursor
    {
      if IsWhitespace(text[cursor]) {
        cursor := cursor + 1;
      } else if text[cursor] == '\0' {
        tokens := tokens + [""];
        cursor := SkipAfterNul(text, cursor);
      } else {
        var end := WordEnd(text, cursor);
        assert cursor < end;
        tokens := tokens + [text[cursor..end]];
        cursor :=
          if end < |text| && text[end] == '\0'
          then SkipAfterNul(text, end)
          else end;
      }
    }
    return tokens;
  }

  function SkipAfterNul(text: BenchWorld.Bytes, i: nat): nat
    requires i <= |text|
    ensures i <= SkipAfterNul(text, i) <= |text|
    ensures i < |text| ==> i < SkipAfterNul(text, i)
    decreases |text| - i
  {
    if i >= |text| then
      i
    else if IsWhitespace(text[i]) then
      i + 1
    else
      SkipAfterNul(text, i + 1)
  } by method {
    var cursor := i;
    while cursor < |text| && !IsWhitespace(text[cursor])
      invariant i <= cursor <= |text|
      invariant SkipAfterNul(text, i) == SkipAfterNul(text, cursor)
      decreases |text| - cursor
    {
      cursor := cursor + 1;
    }
    return if cursor < |text| then cursor + 1 else cursor;
  }

  function WordEnd(text: BenchWorld.Bytes, i: nat): nat
    requires i <= |text|
    ensures i <= WordEnd(text, i) <= |text|
    ensures i < |text| && !IsWhitespace(text[i]) && text[i] != '\0' ==> i < WordEnd(text, i)
    decreases |text| - i
  {
    if i >= |text| then
      i
    else if IsWhitespace(text[i]) || text[i] == '\0' then
      i
    else
      WordEnd(text, i + 1)
  } by method {
    var cursor := i;
    while cursor < |text| &&
      !IsWhitespace(text[cursor]) &&
      text[cursor] != '\0'
      invariant i <= cursor <= |text|
      invariant WordEnd(text, i) == WordEnd(text, cursor)
      decreases |text| - cursor
    {
      cursor := cursor + 1;
    }
    return cursor;
  }

  function SplitWords(text: BenchWorld.Bytes): seq<string>
  {
    SplitWordsFrom(text, 0)
  }

  function RunTokens(tokens: seq<string>, exponents: bool): RunResult
    decreases |tokens|
  {
    if |tokens| == 0 then
      RunResult([], [], false)
    else
      var head := ProcessToken(tokens[0], exponents);
      var tail := RunTokens(tokens[1..], exponents);
      match head
      case TokenOk(out) =>
        RunResult(out + tail.stdout, tail.stderr, tail.hadError)
      case TokenErr(err) =>
        RunResult(tail.stdout, err + tail.stderr, true)
  } by method {
    var cursor := 0;
    var output: BenchWorld.Bytes := [];
    var errorOutput: BenchWorld.Bytes := [];
    var hadError := false;
    while cursor < |tokens|
      invariant 0 <= cursor <= |tokens|
      invariant RunTokens(tokens, exponents).stdout ==
                output + RunTokens(tokens[cursor..], exponents).stdout
      invariant RunTokens(tokens, exponents).stderr ==
                errorOutput + RunTokens(tokens[cursor..], exponents).stderr
      invariant RunTokens(tokens, exponents).hadError ==
                (hadError || RunTokens(tokens[cursor..], exponents).hadError)
      decreases |tokens| - cursor
    {
      var result := ProcessToken(tokens[cursor], exponents);
      if result.TokenOk? {
        output := output + result.out;
      } else {
        errorOutput := errorOutput + result.err;
        hadError := true;
      }
      cursor := cursor + 1;
    }
    return RunResult(output, errorOutput, hadError);
  }

  twostate predicate CoreSummary(raw: Schema.FactorCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    if HelpSelected(raw) then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.HelpTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else if VersionSelected(raw) then
      io.stdin() == old(io.stdin()) &&
      io.stdout() == old(io.stdout()) + Spec.VersionTextSpec() &&
      io.stderr() == old(io.stderr()) &&
      exit == 0
    else
      var tokens := if |raw.operands| > 0 then raw.operands else SplitWords(old(io.stdin()));
      var run := RunTokens(tokens, raw.seenExponents);
      io.stdin() == (if |raw.operands| > 0 then old(io.stdin()) else IOContract.AfterReadStdinFields(old(io.stdin()))) &&
      io.stdout() == old(io.stdout()) + run.stdout &&
      io.stderr() == old(io.stderr()) + run.stderr &&
      exit == (if run.hadError then 1 else 0)
  }

  method RunCore(raw: Schema.FactorCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdinRegion, io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    ghost var preStdin := io.stdin();
    var help := HelpSelected(raw);
    if help {
      var out := Spec.HelpTextSpec();
      io.AppendStdout(out);
      exit := 0;
      return;
    }

    var version := VersionSelected(raw);
    if version {
      var out := Spec.VersionTextSpec();
      io.AppendStdout(out);
      exit := 0;
      return;
    }

    var tokens: seq<string>;
    if |raw.operands| > 0 {
      tokens := raw.operands;
    } else {
      ghost var beforeStdin := io.stdin();
      var stdinBytes := io.ReadStdinAll();
      assert IOContract.ReadStdinAllFields(beforeStdin, io.stdin(), stdinBytes);
      assert beforeStdin == preStdin;
      assert stdinBytes == preStdin;
      assert io.stdin() == IOContract.AfterReadStdinFields(preStdin);
      tokens := SplitWords(stdinBytes);
    }

    var run := RunTokens(tokens, raw.seenExponents);
    io.AppendStdout(run.stdout);
    io.AppendStderr(run.stderr);
    exit := if run.hadError then 1 else 0;
    if |raw.operands| > 0 {
      assert io.stdin() == preStdin;
    }
  }
}
