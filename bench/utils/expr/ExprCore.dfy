include "../../core/World.dfy"
include "../../core/IO.dfy"
include "ExprSchema.dfy"
include "ExprSpec.dfy"

module ExprCore {
  import BenchIO
  import BenchWorld
  import Utf8 = Utf8Semantics
  import ExprSchema
  import Spec = ExprSpec

  function EvalOk(value: string, next: nat): (bool, string, nat, BenchWorld.Bytes)
  {
    (true, value, next, [])
  }

  function EvalErr(message: BenchWorld.Bytes): (bool, string, nat, BenchWorld.Bytes)
  {
    (false, "", 0, message)
  }

  function OpOk(value: string): (bool, string, BenchWorld.Bytes)
  {
    (true, value, [])
  }

  function OpErr(message: BenchWorld.Bytes): (bool, string, BenchWorld.Bytes)
  {
    (false, "", message)
  }

  function IsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function DigitValue(ch: char): int
    requires IsDigit(ch)
  {
    (ch as int) - ('0' as int)
  }

  function AllDigitsFrom(text: string, i: nat): bool
    requires i <= |text|
    decreases |text| - i
  {
    if i >= |text| then
      true
    else
      IsDigit(text[i]) && AllDigitsFrom(text, i + 1)
  }

  function ParseUnsigned(text: string, i: nat, acc: int): int
    requires i <= |text|
    requires AllDigitsFrom(text, i)
    decreases |text| - i
  {
    if i >= |text| then
      acc
    else
      ParseUnsigned(text, i + 1, acc * 10 + DigitValue(text[i]))
  }

  function IsInteger(text: string): bool
  {
    if |text| == 0 then
      false
    else if text[0] == '-' then
      1 < |text| && AllDigitsFrom(text, 1)
    else
      AllDigitsFrom(text, 0)
  }

  function ParseInteger(text: string): int
    requires IsInteger(text)
  {
    if text[0] == '-' then
      -ParseUnsigned(text, 1, 0)
    else
      ParseUnsigned(text, 0, 0)
  }

  function Abs(n: int): int
    ensures 0 <= Abs(n)
  {
    if n < 0 then -n else n
  }

  function DigitChar(d: int): char
  {
    if 0 <= d < 10 then
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

  function Digits(n: int): BenchWorld.Bytes
    decreases if n < 0 then 1 - n else n
  {
    if n < 0 then
      ['-'] + DigitsUnsigned(-n)
    else
      DigitsUnsigned(n)
  }

  function DivTrunc(a: int, b: int): int
    requires b != 0
  {
    var q := Abs(a) / Abs(b);
    if (a < 0 && b > 0) || (a > 0 && b < 0) then -q else q
  }

  function ModTrunc(a: int, b: int): int
    requires b != 0
  {
    a - DivTrunc(a, b) * b
  }

  function ValueIsTrue(value: string): bool
  {
    value != "" && (!IsInteger(value) || ParseInteger(value) != 0)
  }

  function StringLessFrom(a: string, b: string, i: nat): bool
    requires i <= |a|
    requires i <= |b|
    decreases |a| - i, |b| - i
  {
    if i >= |a| then
      i < |b|
    else if i >= |b| then
      false
    else if a[i] < b[i] then
      true
    else if b[i] < a[i] then
      false
    else
      StringLessFrom(a, b, i + 1)
  }

  function StringLess(a: string, b: string): bool
  {
    StringLessFrom(a, b, 0)
  }

  function BoolText(value: bool): string
  {
    if value then "1" else "0"
  }

  function CompareValues(left: string, op: string, right: string): string
  {
    var numeric := IsInteger(left) && IsInteger(right);
    var cmp :=
      if numeric then
        var l := ParseInteger(left);
        var r := ParseInteger(right);
        if op == "<" then l < r
        else if op == "<=" then l <= r
        else if op == "=" || op == "==" then l == r
        else if op == "!=" then l != r
        else if op == ">=" then l >= r
        else l > r
      else if op == "<" then StringLess(left, right)
      else if op == "<=" then left == right || StringLess(left, right)
      else if op == "=" || op == "==" then left == right
      else if op == "!=" then left != right
      else if op == ">=" then left == right || StringLess(right, left)
      else StringLess(right, left);
    BoolText(cmp)
  }

  function IsCompareOp(op: string): bool
  {
    op == "<" || op == "<=" || op == "=" || op == "==" ||
    op == "!=" || op == ">=" || op == ">"
  }

  function ApplyArithmetic(op: string, left: string, right: string): (bool, string, BenchWorld.Bytes)
  {
    if !IsInteger(left) || !IsInteger(right) then
      OpErr(Spec.NonIntegerMessage())
    else
      var l := ParseInteger(left);
      var r := ParseInteger(right);
      if op == "+" then
        OpOk(Digits(l + r))
      else if op == "-" then
        OpOk(Digits(l - r))
      else if op == "*" then
        OpOk(Digits(l * r))
      else if r == 0 then
        OpErr(Spec.DivisionByZeroMessage())
      else if op == "/" then
        OpOk(Digits(DivTrunc(l, r)))
      else
        OpOk(Digits(ModTrunc(l, r)))
  }

  function Take(text: string, count: nat): string
    decreases count, |text|
  {
    if count == 0 || |text| == 0 then
      ""
    else
      [text[0]] + Take(text[1..], count - 1)
  }

  function SubstringValue(text: string, posText: string, lenText: string): string
  {
    if !IsInteger(posText) || !IsInteger(lenText) then
      ""
    else
      var pos := ParseInteger(posText);
      var len := ParseInteger(lenText);
      if pos <= 0 || len <= 0 then
        ""
      else
        var start := (pos - 1) as nat;
        if start >= |text| then
          ""
        else
          Take(text[start..], len as nat)
  }

  function ContainsChar(chars: string, target: char, i: nat): bool
    requires i <= |chars|
    decreases |chars| - i
  {
    if i >= |chars| then
      false
    else
      chars[i] == target || ContainsChar(chars, target, i + 1)
  }

  function FindIndexFrom(text: string, chars: string, i: nat): int
    requires i <= |text|
    decreases |text| - i
  {
    if i >= |text| then
      0
    else if ContainsChar(chars, text[i], 0) then
      i + 1
    else
      FindIndexFrom(text, chars, i + 1)
  }

  function IndexValue(text: string, chars: string): string
  {
    Digits(FindIndexFrom(text, chars, 0))
  }

  function ParseOr(tokens: seq<string>, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParseOr(tokens, i).0 ==> i < ParseOr(tokens, i).2 <= |tokens|
    decreases |tokens| - i, 6
  {
    var left := ParseAnd(tokens, i);
    if !left.0 then
      left
    else
      ParseOrRest(tokens, left.1, left.2)
  }

  function ParseOrRest(tokens: seq<string>, left: string, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParseOrRest(tokens, left, i).0 ==> i <= ParseOrRest(tokens, left, i).2 <= |tokens|
    decreases |tokens| - i, 6
  {
    if i < |tokens| && tokens[i] == "|" then
      var right := ParseAnd(tokens, i + 1);
      if !right.0 then
        right
      else
        ParseOrRest(tokens, if ValueIsTrue(left) then left else right.1, right.2)
    else
      EvalOk(left, i)
  }

  function ParseAnd(tokens: seq<string>, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParseAnd(tokens, i).0 ==> i < ParseAnd(tokens, i).2 <= |tokens|
    decreases |tokens| - i, 5
  {
    var left := ParseCompare(tokens, i);
    if !left.0 then
      left
    else
      ParseAndRest(tokens, left.1, left.2)
  }

  function ParseAndRest(tokens: seq<string>, left: string, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParseAndRest(tokens, left, i).0 ==> i <= ParseAndRest(tokens, left, i).2 <= |tokens|
    decreases |tokens| - i, 5
  {
    if i < |tokens| && tokens[i] == "&" then
      var right := ParseCompare(tokens, i + 1);
      if !right.0 then
        right
      else
        ParseAndRest(
          tokens,
          if ValueIsTrue(left) && ValueIsTrue(right.1) then left else "0",
          right.2
        )
    else
      EvalOk(left, i)
  }

  function ParseCompare(tokens: seq<string>, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParseCompare(tokens, i).0 ==> i < ParseCompare(tokens, i).2 <= |tokens|
    decreases |tokens| - i, 4
  {
    var left := ParseAdd(tokens, i);
    if !left.0 then
      left
    else
      ParseCompareRest(tokens, left.1, left.2)
  }

  function ParseCompareRest(tokens: seq<string>, left: string, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParseCompareRest(tokens, left, i).0 ==>
              i <= ParseCompareRest(tokens, left, i).2 <= |tokens|
    decreases |tokens| - i, 4
  {
    if i < |tokens| && IsCompareOp(tokens[i]) then
      var right := ParseAdd(tokens, i + 1);
      if !right.0 then
        right
      else
        ParseCompareRest(tokens, CompareValues(left, tokens[i], right.1), right.2)
    else
      EvalOk(left, i)
  }

  function ParseAdd(tokens: seq<string>, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParseAdd(tokens, i).0 ==> i < ParseAdd(tokens, i).2 <= |tokens|
    decreases |tokens| - i, 3
  {
    var left := ParseMul(tokens, i);
    if !left.0 then
      left
    else
      ParseAddRest(tokens, left.1, left.2)
  }

  function ParseAddRest(tokens: seq<string>, left: string, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParseAddRest(tokens, left, i).0 ==> i <= ParseAddRest(tokens, left, i).2 <= |tokens|
    decreases |tokens| - i, 3
  {
    if i < |tokens| && (tokens[i] == "+" || tokens[i] == "-") then
      var right := ParseMul(tokens, i + 1);
      if !right.0 then
        right
      else
        var opResult := ApplyArithmetic(tokens[i], left, right.1);
        if !opResult.0 then
          EvalErr(opResult.2)
        else
          ParseAddRest(tokens, opResult.1, right.2)
    else
      EvalOk(left, i)
  }

  function ParseMul(tokens: seq<string>, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParseMul(tokens, i).0 ==> i < ParseMul(tokens, i).2 <= |tokens|
    decreases |tokens| - i, 2
  {
    var left := ParseMatch(tokens, i);
    if !left.0 then
      left
    else
      ParseMulRest(tokens, left.1, left.2)
  }

  function ParseMulRest(tokens: seq<string>, left: string, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParseMulRest(tokens, left, i).0 ==> i <= ParseMulRest(tokens, left, i).2 <= |tokens|
    decreases |tokens| - i, 2
  {
    if i < |tokens| && (tokens[i] == "*" || tokens[i] == "/" || tokens[i] == "%") then
      var right := ParseMatch(tokens, i + 1);
      if !right.0 then
        right
      else
        var opResult := ApplyArithmetic(tokens[i], left, right.1);
        if !opResult.0 then
          EvalErr(opResult.2)
        else
          ParseMulRest(tokens, opResult.1, right.2)
    else
      EvalOk(left, i)
  }

  function ParseMatch(tokens: seq<string>, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParseMatch(tokens, i).0 ==> i < ParseMatch(tokens, i).2 <= |tokens|
    decreases |tokens| - i, 1
  {
    var left := ParsePrimary(tokens, i);
    if !left.0 then
      left
    else if left.2 < |tokens| && tokens[left.2] == ":" then
      EvalErr(Spec.UnsupportedRegexMessage())
    else
      left
  }

  function ParsePrimary(tokens: seq<string>, i: nat): (bool, string, nat, BenchWorld.Bytes)
    requires i <= |tokens|
    ensures ParsePrimary(tokens, i).0 ==> i < ParsePrimary(tokens, i).2 <= |tokens|
    decreases |tokens| - i, 0
  {
    if i >= |tokens| then
      EvalErr(Spec.MissingOperandMessage())
    else if tokens[i] == "(" then
      var inner := ParseOr(tokens, i + 1);
      if !inner.0 then
        inner
      else if inner.2 < |tokens| && tokens[inner.2] == ")" then
        EvalOk(inner.1, inner.2 + 1)
      else
        EvalErr(Spec.MissingCloseMessage())
    else if tokens[i] == ")" then
      EvalErr(Spec.SyntaxErrorMessage())
    else if tokens[i] == "+" then
      if i + 1 < |tokens| then
        EvalOk(tokens[i + 1], i + 2)
      else
        EvalErr(Spec.MissingAfterMessage("+"))
    else if tokens[i] == "length" then
      var arg := ParsePrimary(tokens, i + 1);
      if !arg.0 then arg else EvalOk(Digits(|arg.1|), arg.2)
    else if tokens[i] == "substr" then
      var text := ParsePrimary(tokens, i + 1);
      if !text.0 then
        text
      else
        var pos := ParsePrimary(tokens, text.2);
        if !pos.0 then
          pos
        else
          var len := ParsePrimary(tokens, pos.2);
          if !len.0 then
            len
          else
            EvalOk(SubstringValue(text.1, pos.1, len.1), len.2)
    else if tokens[i] == "index" then
      var text := ParsePrimary(tokens, i + 1);
      if !text.0 then
        text
      else
        var chars := ParsePrimary(tokens, text.2);
        if !chars.0 then
          chars
        else
          EvalOk(IndexValue(text.1, chars.1), chars.2)
    else if tokens[i] == "match" then
      EvalErr(Spec.UnsupportedRegexMessage())
    else
      EvalOk(tokens[i], i + 1)
  }

  function EffectiveArgs(args: seq<string>): seq<string>
  {
    if |args| > 0 && args[0] == "--" then args[1..] else args
  }

  function EvaluateArgs(args: seq<string>): (BenchWorld.Bytes, BenchWorld.Bytes, int)
  {
    if args == ["--help"] then
      (Spec.HelpText(), [], 0)
    else if args == ["--version"] then
      (Spec.VersionText(), [], 0)
    else
      var exprArgs := EffectiveArgs(args);
      if |exprArgs| == 0 then
        ([], Spec.MissingOperandMessage(), 2)
      else
        var parsed := ParseOr(exprArgs, 0);
        if !parsed.0 then
          ([], parsed.3, 2)
        else if parsed.2 != |exprArgs| then
          ([], Spec.SyntaxErrorMessage(), 2)
        else
          (Utf8.Encode(parsed.1) + ['\n'], [], if ValueIsTrue(parsed.1) then 0 else 1)
  }

  twostate predicate CoreSummary(raw: ExprSchema.ExprCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    var result := EvaluateArgs(raw.args);
    io.stdout() == old(io.stdout()) + result.0 &&
    io.stderr() == old(io.stderr()) + result.1 &&
    exit == result.2
  }

  method RunCore(raw: ExprSchema.ExprCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures CoreSummary(raw, io, exit)
    decreases *
  {
    var result := EvaluateArgs(raw.args);
    io.AppendStdout(result.0);
    io.AppendStderr(result.1);
    exit := result.2;
  }
}
