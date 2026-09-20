include "../../core/World.dfy"
include "../../core/IO.dfy"
include "ExprSchema.dfy"

module ExprSpec {
  import BenchIO
  import BenchWorld
  import Utf8 = Utf8Semantics
  import Schema = ExprSchema



  function HelpText(): BenchWorld.Bytes
  {
    "Usage: expr EXPRESSION\n"
    + "  or:  expr OPTION\n"
    + "\n"
    + "Print the value of EXPRESSION to standard output.\n"
    + "\n"
    + "Supported benchmark operators, in increasing precedence groups:\n"
    + "  ARG1 | ARG2       ARG1 if it is neither null nor 0, otherwise ARG2\n"
    + "  ARG1 & ARG2       ARG1 if neither argument is null or 0, otherwise 0\n"
    + "  ARG1 < ARG2       ARG1 is less than ARG2\n"
    + "  ARG1 <= ARG2      ARG1 is less than or equal to ARG2\n"
    + "  ARG1 = ARG2       ARG1 is equal to ARG2\n"
    + "  ARG1 == ARG2      ARG1 is equal to ARG2\n"
    + "  ARG1 != ARG2      ARG1 is unequal to ARG2\n"
    + "  ARG1 >= ARG2      ARG1 is greater than or equal to ARG2\n"
    + "  ARG1 > ARG2       ARG1 is greater than ARG2\n"
    + "  ARG1 + ARG2       arithmetic sum of ARG1 and ARG2\n"
    + "  ARG1 - ARG2       arithmetic difference of ARG1 and ARG2\n"
    + "  ARG1 * ARG2       arithmetic product of ARG1 and ARG2\n"
    + "  ARG1 / ARG2       arithmetic quotient of ARG1 divided by ARG2\n"
    + "  ARG1 % ARG2       arithmetic remainder of ARG1 divided by ARG2\n"
    + "  substr STRING POS LENGTH\n"
    + "  index STRING CHARS\n"
    + "  length STRING\n"
    + "  + TOKEN            interpret TOKEN as a string\n"
    + "  ( EXPRESSION )\n"
    + "\n"
    + "Regular expression matching is outside this benchmark subset.\n"
    + "      --help        display this help and exit\n"
    + "      --version     output version information and exit\n"
  }

  function VersionText(): BenchWorld.Bytes
  {
    "expr (GNU coreutils) 9.10.13-2cf49\n"
    + "Written by Mike Parker, James Youngman, and Paul Eggert.\n"
  }

  function TryHelp(): BenchWorld.Bytes
  {
    "Try 'expr --help' for more information.\n"
  }

  function MissingOperandMessage(): BenchWorld.Bytes
  {
    "expr: missing operand\n" + TryHelp()
  }

  function SyntaxErrorMessage(): BenchWorld.Bytes
  {
    "expr: syntax error\n" + TryHelp()
  }

  function MissingAfterMessage(op: string): BenchWorld.Bytes
  {
    "expr: syntax error: missing argument after '" + op + "'\n"
  }

  function MissingCloseMessage(): BenchWorld.Bytes
  {
    "expr: syntax error: expecting ')' after expression\n"
  }

  function NonIntegerMessage(): BenchWorld.Bytes
  {
    "expr: non-integer argument\n"
  }

  function DivisionByZeroMessage(): BenchWorld.Bytes
  {
    "expr: division by zero\n"
  }

  function UnsupportedRegexMessage(): BenchWorld.Bytes
  {
    "expr: regular expression matching is unsupported in this benchmark\n"
  }

  datatype EvalResult =
    | EvalSuccess(value: string, next: nat)
    | EvalFailure(message: BenchWorld.Bytes)

  function IsDigit(ch: char): bool
  {
    '0' <= ch <= '9'
  }

  function DigitValue(ch: char): int
    requires IsDigit(ch)
  {
    (ch as int) - ('0' as int)
  }

  ghost predicate AllDigits(text: string)
  {
    forall i :: 0 <= i < |text| ==> IsDigit(text[i])
  }

  // The value of a digit string, by structural recursion on the string. The
  // positional weights of the previous form are implicit in the recursion, so
  // no `Pow10` is needed here; the proof module keeps one to bridge Core's
  // left-folding accumulator.
  ghost function DecimalValue(digits: string): int
    requires AllDigits(digits)
    decreases |digits|
  {
    if |digits| == 0 then
      0
    else
      DecimalValue(digits[..|digits| - 1]) * 10 +
      DigitValue(digits[|digits| - 1])
  }

  ghost predicate IntegerValue(text: string, value: int)
  {
    if |text| == 0 then
      false
    else if text[0] == '-' then
      1 < |text| &&
      AllDigits(text[1..]) &&
      value == -DecimalValue(text[1..])
    else
      AllDigits(text) &&
      value == DecimalValue(text)
  }

  ghost predicate CanonicalIntegerText(text: string)
  {
    |text| == 1 ||
    (|text| > 1 && text[0] != '0' &&
     (text[0] != '-' || (|text| > 1 && text[1] != '0')))
  }

  ghost predicate DecimalRepresentation(value: int, text: string)
  {
    IntegerValue(text, value) && CanonicalIntegerText(text)
  }

  ghost predicate ValueTruth(value: string, truth: bool)
  {
    truth == (value != "" && !IntegerValue(value, 0))
  }

  ghost predicate StringLess(a: string, b: string)
  {
    (exists first: nat ::
       first < |a| &&
       first < |b| &&
       a[..first] == b[..first] &&
       a[first] < b[first]) ||
    (|a| < |b| && a == b[..|a|])
  }

  ghost predicate ComparisonRelation(left: string, op: string, right: string, value: string)
  {
    (value == "0" || value == "1") &&
    if exists l: int, r: int :: IntegerValue(left, l) && IntegerValue(right, r) then
      exists l: int, r: int ::
        IntegerValue(left, l) &&
        IntegerValue(right, r) &&
        ((value == "1") <==>
         if op == "<" then l < r
         else if op == "<=" then l <= r
         else if op == "=" || op == "==" then l == r
         else if op == "!=" then l != r
         else if op == ">=" then l >= r
         else l > r)
    else
      (value == "1") <==>
      if op == "<" then StringLess(left, right)
      else if op == "<=" then left == right || StringLess(left, right)
      else if op == "=" || op == "==" then left == right
      else if op == "!=" then left != right
      else if op == ">=" then left == right || StringLess(right, left)
      else StringLess(right, left)
  }

  function IsCompareOp(op: string): bool
  {
    op == "<" || op == "<=" || op == "=" || op == "==" ||
    op == "!=" || op == ">=" || op == ">"
  }

  ghost predicate ArithmeticRelation(
    op: string,
    left: string,
    right: string,
    result: EvalResult
  )
  {
    if !(exists l: int, r: int :: IntegerValue(left, l) && IntegerValue(right, r)) then
      result == EvalFailure(NonIntegerMessage())
    else
      exists l: int, r: int ::
        IntegerValue(left, l) &&
        IntegerValue(right, r) &&
        if (op == "/" || op == "%") && r == 0 then
          result == EvalFailure(DivisionByZeroMessage())
        else
          var value :=
            if op == "+" then l + r
            else if op == "-" then l - r
            else if op == "*" then l * r
            else if op == "/" then
              var q := (if l < 0 then -l else l) /
                       (if r == 0 then 1 else if r < 0 then -r else r);
              if (l < 0 && r > 0) || (l > 0 && r < 0) then -q else q
            else
              var q := (if l < 0 then -l else l) /
                       (if r == 0 then 1 else if r < 0 then -r else r);
              l - (if (l < 0 && r > 0) || (l > 0 && r < 0) then -q else q) * r;
          exists text: string ::
            DecimalRepresentation(value, text) &&
            result == EvalSuccess(text, 0)
  }

  ghost predicate SubstringRelation(
    text: string, posText: string, lenText: string, value: string
  )
  {
    if !(exists pos: int, len: int ::
           IntegerValue(posText, pos) && IntegerValue(lenText, len)) then
      value == ""
    else
      exists pos: int, len: int ::
        IntegerValue(posText, pos) &&
        IntegerValue(lenText, len) &&
        if pos <= 0 || len <= 0 || pos - 1 >= |text| then
          value == ""
        else
          var start := (pos - 1) as nat;
          value ==
          if start + len <= |text| then
            text[start..start + len]
          else
            text[start..]
  }

  ghost predicate IndexRelation(text: string, chars: string, value: string)
  {
    exists index: int ::
      DecimalRepresentation(index, value) &&
      if index == 0 then
        forall i :: 0 <= i < |text| ==> text[i] !in chars
      else
        1 <= index <= |text| &&
        text[index - 1] in chars &&
        (forall i :: 0 <= i < index - 1 ==> text[i] !in chars)
  }

  ghost predicate OrJudgment(tokens: seq<string>, i: nat, result: EvalResult)
    requires i <= |tokens|
    ensures OrJudgment(tokens, i, result) && result.EvalSuccess? ==>
              i < result.next <= |tokens|
    decreases |tokens| - i, 6
  {
    exists left: EvalResult ::
      AndJudgment(tokens, i, left) &&
      match left
      case EvalFailure(_) => result == left
      case EvalSuccess(value, next) => OrTailJudgment(tokens, value, next, result)
  }

  ghost predicate OrTailJudgment(
    tokens: seq<string>, left: string, i: nat, result: EvalResult
  )
    requires i <= |tokens|
    ensures OrTailJudgment(tokens, left, i, result) && result.EvalSuccess? ==>
              i <= result.next <= |tokens|
    decreases |tokens| - i, 6
  {
    if i < |tokens| && tokens[i] == "|" then
      exists right: EvalResult {:trigger AndJudgment(tokens, i + 1, right)} ::
        AndJudgment(tokens, i + 1, right) &&
        match right
        case EvalFailure(_) => result == right
        case EvalSuccess(value, next) =>
          exists truth: bool ::
            ValueTruth(left, truth) &&
            OrTailJudgment(tokens, if truth then left else value, next, result)
    else
      result == EvalSuccess(left, i)
  }

  ghost predicate AndJudgment(tokens: seq<string>, i: nat, result: EvalResult)
    requires i <= |tokens|
    ensures AndJudgment(tokens, i, result) && result.EvalSuccess? ==>
              i < result.next <= |tokens|
    decreases |tokens| - i, 5
  {
    exists left: EvalResult ::
      CompareJudgment(tokens, i, left) &&
      match left
      case EvalFailure(_) => result == left
      case EvalSuccess(value, next) => AndTailJudgment(tokens, value, next, result)
  }

  ghost predicate AndTailJudgment(
    tokens: seq<string>, left: string, i: nat, result: EvalResult
  )
    requires i <= |tokens|
    ensures AndTailJudgment(tokens, left, i, result) && result.EvalSuccess? ==>
              i <= result.next <= |tokens|
    decreases |tokens| - i, 5
  {
    if i < |tokens| && tokens[i] == "&" then
      exists right: EvalResult {:trigger CompareJudgment(tokens, i + 1, right)} ::
        CompareJudgment(tokens, i + 1, right) &&
        match right
        case EvalFailure(_) => result == right
        case EvalSuccess(value, next) =>
          exists leftTruth: bool, rightTruth: bool ::
            ValueTruth(left, leftTruth) &&
            ValueTruth(value, rightTruth) &&
            AndTailJudgment(
              tokens, if leftTruth && rightTruth then left else "0", next, result
            )
    else
      result == EvalSuccess(left, i)
  }

  ghost predicate CompareJudgment(tokens: seq<string>, i: nat, result: EvalResult)
    requires i <= |tokens|
    ensures CompareJudgment(tokens, i, result) && result.EvalSuccess? ==>
              i < result.next <= |tokens|
    decreases |tokens| - i, 4
  {
    exists left: EvalResult ::
      AddJudgment(tokens, i, left) &&
      match left
      case EvalFailure(_) => result == left
      case EvalSuccess(value, next) => CompareTailJudgment(tokens, value, next, result)
  }

  ghost predicate CompareTailJudgment(
    tokens: seq<string>, left: string, i: nat, result: EvalResult
  )
    requires i <= |tokens|
    ensures CompareTailJudgment(tokens, left, i, result) && result.EvalSuccess? ==>
              i <= result.next <= |tokens|
    decreases |tokens| - i, 4
  {
    if i < |tokens| && IsCompareOp(tokens[i]) then
      exists right: EvalResult {:trigger AddJudgment(tokens, i + 1, right)} ::
        AddJudgment(tokens, i + 1, right) &&
        match right
        case EvalFailure(_) => result == right
        case EvalSuccess(value, next) =>
          exists compared: string ::
            ComparisonRelation(left, tokens[i], value, compared) &&
            CompareTailJudgment(tokens, compared, next, result)
    else
      result == EvalSuccess(left, i)
  }

  ghost predicate AddJudgment(tokens: seq<string>, i: nat, result: EvalResult)
    requires i <= |tokens|
    ensures AddJudgment(tokens, i, result) && result.EvalSuccess? ==>
              i < result.next <= |tokens|
    decreases |tokens| - i, 3
  {
    exists left: EvalResult ::
      MulJudgment(tokens, i, left) &&
      match left
      case EvalFailure(_) => result == left
      case EvalSuccess(value, next) => AddTailJudgment(tokens, value, next, result)
  }

  ghost predicate AddTailJudgment(
    tokens: seq<string>, left: string, i: nat, result: EvalResult
  )
    requires i <= |tokens|
    ensures AddTailJudgment(tokens, left, i, result) && result.EvalSuccess? ==>
              i <= result.next <= |tokens|
    decreases |tokens| - i, 3
  {
    if i < |tokens| && (tokens[i] == "+" || tokens[i] == "-") then
      exists right: EvalResult {:trigger MulJudgment(tokens, i + 1, right)} ::
        MulJudgment(tokens, i + 1, right) &&
        match right
        case EvalFailure(_) => result == right
        case EvalSuccess(value, next) =>
          exists applied: EvalResult ::
            ArithmeticRelation(tokens[i], left, value, applied) &&
            match applied
            case EvalFailure(_) => result == applied
            case EvalSuccess(computed, _) =>
              AddTailJudgment(tokens, computed, next, result)
    else
      result == EvalSuccess(left, i)
  }

  ghost predicate MulJudgment(tokens: seq<string>, i: nat, result: EvalResult)
    requires i <= |tokens|
    ensures MulJudgment(tokens, i, result) && result.EvalSuccess? ==>
              i < result.next <= |tokens|
    decreases |tokens| - i, 2
  {
    exists left: EvalResult ::
      MatchJudgment(tokens, i, left) &&
      match left
      case EvalFailure(_) => result == left
      case EvalSuccess(value, next) => MulTailJudgment(tokens, value, next, result)
  }

  ghost predicate MulTailJudgment(
    tokens: seq<string>, left: string, i: nat, result: EvalResult
  )
    requires i <= |tokens|
    ensures MulTailJudgment(tokens, left, i, result) && result.EvalSuccess? ==>
              i <= result.next <= |tokens|
    decreases |tokens| - i, 2
  {
    if i < |tokens| && (tokens[i] == "*" || tokens[i] == "/" || tokens[i] == "%") then
      exists right: EvalResult {:trigger MatchJudgment(tokens, i + 1, right)} ::
        MatchJudgment(tokens, i + 1, right) &&
        match right
        case EvalFailure(_) => result == right
        case EvalSuccess(value, next) =>
          exists applied: EvalResult ::
            ArithmeticRelation(tokens[i], left, value, applied) &&
            match applied
            case EvalFailure(_) => result == applied
            case EvalSuccess(computed, _) =>
              MulTailJudgment(tokens, computed, next, result)
    else
      result == EvalSuccess(left, i)
  }

  ghost predicate MatchJudgment(tokens: seq<string>, i: nat, result: EvalResult)
    requires i <= |tokens|
    ensures MatchJudgment(tokens, i, result) && result.EvalSuccess? ==>
              i < result.next <= |tokens|
    decreases |tokens| - i, 1
  {
    exists primary: EvalResult ::
      PrimaryJudgment(tokens, i, primary) &&
      match primary
      case EvalFailure(_) => result == primary
      case EvalSuccess(value, next) =>
        if next < |tokens| && tokens[next] == ":" then
          result == EvalFailure(UnsupportedRegexMessage())
        else
          result == primary
  }

  ghost predicate PrimaryJudgment(tokens: seq<string>, i: nat, result: EvalResult)
    requires i <= |tokens|
    ensures PrimaryJudgment(tokens, i, result) && result.EvalSuccess? ==>
              i < result.next <= |tokens|
    decreases |tokens| - i, 0
  {
    if i >= |tokens| then
      result == EvalFailure(MissingOperandMessage())
    else if tokens[i] == "(" then
      exists inner: EvalResult {:trigger OrJudgment(tokens, i + 1, inner)} ::
        OrJudgment(tokens, i + 1, inner) &&
        match inner
        case EvalFailure(_) => result == inner
        case EvalSuccess(value, next) =>
          if next < |tokens| && tokens[next] == ")" then
            result == EvalSuccess(value, next + 1)
          else
            result == EvalFailure(MissingCloseMessage())
    else if tokens[i] == ")" then
      result == EvalFailure(SyntaxErrorMessage())
    else if tokens[i] == "+" then
      if i + 1 < |tokens| then
        result == EvalSuccess(tokens[i + 1], i + 2)
      else
        result == EvalFailure(MissingAfterMessage("+"))
    else if tokens[i] == "length" then
      exists arg: EvalResult {:trigger PrimaryJudgment(tokens, i + 1, arg)} ::
        PrimaryJudgment(tokens, i + 1, arg) &&
        match arg
        case EvalFailure(_) => result == arg
        case EvalSuccess(value, next) =>
          exists lengthText: string ::
            DecimalRepresentation(|value|, lengthText) &&
            result == EvalSuccess(lengthText, next)
    else if tokens[i] == "substr" then
      exists textResult: EvalResult {:trigger PrimaryJudgment(tokens, i + 1, textResult)} ::
        PrimaryJudgment(tokens, i + 1, textResult) &&
        match textResult
        case EvalFailure(_) => result == textResult
        case EvalSuccess(text, textNext) =>
          exists posResult: EvalResult ::
            PrimaryJudgment(tokens, textNext, posResult) &&
            match posResult
            case EvalFailure(_) => result == posResult
            case EvalSuccess(pos, posNext) =>
              exists lenResult: EvalResult ::
                PrimaryJudgment(tokens, posNext, lenResult) &&
                match lenResult
                case EvalFailure(_) => result == lenResult
                case EvalSuccess(len, lenNext) =>
                  exists value: string ::
                    SubstringRelation(text, pos, len, value) &&
                    result == EvalSuccess(value, lenNext)
    else if tokens[i] == "index" then
      exists textResult: EvalResult {:trigger PrimaryJudgment(tokens, i + 1, textResult)} ::
        PrimaryJudgment(tokens, i + 1, textResult) &&
        match textResult
        case EvalFailure(_) => result == textResult
        case EvalSuccess(text, textNext) =>
          exists charsResult: EvalResult ::
            PrimaryJudgment(tokens, textNext, charsResult) &&
            match charsResult
            case EvalFailure(_) => result == charsResult
            case EvalSuccess(chars, charsNext) =>
              exists value: string ::
                IndexRelation(text, chars, value) &&
                result == EvalSuccess(value, charsNext)
    else if tokens[i] == "match" then
      result == EvalFailure(UnsupportedRegexMessage())
    else
      result == EvalSuccess(tokens[i], i + 1)
  }

  ghost predicate ExecutionRelation(
    args: seq<string>,
    stdout: BenchWorld.Bytes,
    stderr: BenchWorld.Bytes,
    exit: int
  )
  {
    if args == ["--help"] then
      stdout == HelpText() && stderr == [] && exit == 0
    else if args == ["--version"] then
      stdout == VersionText() && stderr == [] && exit == 0
    else
      var exprArgs := if |args| > 0 && args[0] == "--" then args[1..] else args;
      if |exprArgs| == 0 then
        stdout == [] && stderr == MissingOperandMessage() && exit == 2
      else
        exists parsed: EvalResult ::
          OrJudgment(exprArgs, 0, parsed) &&
          match parsed
          case EvalFailure(message) =>
            stdout == [] && stderr == message && exit == 2
          case EvalSuccess(value, next) =>
            if next != |exprArgs| then
              stdout == [] && stderr == SyntaxErrorMessage() && exit == 2
            else
              exists truth: bool ::
                ValueTruth(value, truth) &&
                stdout == Utf8.Encode(value) + ['\n'] &&
                stderr == [] &&
                exit == (if truth then 0 else 1)
  }

  twostate predicate Spec(raw: Schema.ExprCmdRaw, io: BenchIO.IO, exit: int)
    reads io.Footprint()
  {
    exists stdout: BenchWorld.Bytes, stderr: BenchWorld.Bytes ::
      ExecutionRelation(raw.args, stdout, stderr, exit) &&
      io.stdout() == old(io.stdout()) + stdout &&
      io.stderr() == old(io.stderr()) + stderr
  }
}
