include "../../../core/IO.dfy"
include "../Spec/PathchkSchema.dfy"
include "../Spec/PathchkSpec.dfy"
include "../Proof/PathchkProof.dfy"
include "../../../core/Utf8.dfy"
include "../../../core/StringEscaping.dfy"

module PathchkCore {
  import BenchIO
  import BenchWorld
  import CliTypes
  import Schema = PathchkSchema
  import Spec = PathchkSpec
  import C = IOContract
  import Utf8 = Utf8Semantics
  import Quote = StringEscaping
  import Proof = PathchkProof

  method FormatParseError(err: CliTypes.ParseError) returns (msg: BenchWorld.Bytes)
    ensures Spec.ParseErrorText(err, msg)
  {
    if Spec.ShortOptionError(err) {
      var token := err.rawToken;
      var index: nat := 1;
      while index + 1 < |token| && token[index] in "pP"
        invariant 1 <= index < |token|
        invariant forall i: nat | 1 <= i < index :: token[i] in "pP"
        decreases |token| - index
      {
        index := index + 1;
      }
      assert Spec.ShortOptionPosition(token, index);
      msg := Spec.UnknownShortText(Utf8.EncodeChar(token[index])[0]);
    } else {
      var token := Encode(err.rawToken);
      msg := Spec.ParseErrorMessage(err, token);
    }
  }

  method Decimal(n: nat) returns (text: BenchWorld.Bytes)
    ensures Spec.DecimalText(n, text)
    decreases n
  {
    var prefix: BenchWorld.Bytes := [];
    if n >= 10 {
      prefix := Decimal(n / 10);
    }
    text := prefix + [('0' as int + n % 10) as char];
    Proof.DecimalStep(n, prefix);
  }

  method Encode(text: string) returns (encoded: BenchWorld.Bytes)
    ensures encoded == Utf8.Encode(text)
  {
    var i := |text|;
    encoded := [];
    while i > 0
      invariant 0 <= i <= |text|
      invariant encoded == Utf8.Encode(text[i..])
      decreases i
    {
      i := i - 1;
      assert text[i..][1..] == text[i + 1..];
      encoded := Utf8.EncodeChar(text[i]) + encoded;
    }
  }

  method CQuoteBody(bytes: BenchWorld.Bytes) returns (quoted: BenchWorld.Bytes)
    ensures quoted == Quote.SpecCQuoteBytes(bytes)
  {
    var i := |bytes|;
    quoted := [];
    while i > 0
      invariant 0 <= i <= |bytes|
      invariant quoted == Quote.SpecCQuoteBytes(bytes[i..])
      decreases i
    {
      i := i - 1;
      assert bytes[i..][1..] == bytes[i + 1..];
      quoted := Quote.SpecCQuoteByte(bytes[i]) + quoted;
    }
  }

  method ShellCompatibleTail(bytes: BenchWorld.Bytes) returns (compatible: bool)
    ensures compatible == Quote.SpecShellCompatibleTail(bytes)
  {
    var i := |bytes|;
    compatible := true;
    while i > 0
      invariant 0 <= i <= |bytes|
      invariant compatible == Quote.SpecShellCompatibleTail(bytes[i..])
      decreases i
    {
      i := i - 1;
      assert bytes[i..][1..] == bytes[i + 1..];
      compatible := Quote.SpecShellCompatibleByte(bytes[i], false, false) && compatible;
    }
  }

  method ShellEscapeTail(bytes: BenchWorld.Bytes) returns (plain: BenchWorld.Bytes)
    ensures plain == Quote.SpecShellEscapeTail(bytes, false)
  {
    var i := |bytes|;
    plain := "'";
    var active: BenchWorld.Bytes := "'";
    while i > 0
      invariant 0 <= i <= |bytes|
      invariant plain == Quote.SpecShellEscapeTail(bytes[i..], false)
      invariant active == Quote.SpecShellEscapeTail(bytes[i..], true)
      decreases i
    {
      i := i - 1;
      assert bytes[i..][1..] == bytes[i + 1..];
      var byte := bytes[i];
      if byte == '\'' {
        plain := "'\\''" + plain;
        active := plain;
      } else if Quote.SpecNeedsAnsiEscape(byte) {
        active := Quote.SpecAnsiEscape(byte) + active;
        plain := "'$'" + active;
      } else {
        plain := [byte] + plain;
        active := "''" + plain;
      }
    }
  }

  method QuoteAf(bytes: BenchWorld.Bytes) returns (quoted: BenchWorld.Bytes)
    ensures quoted == Quote.SpecQuoteAfBytes(bytes)
  {
    var compatible := true;
    if |bytes| > 0 {
      compatible := ShellCompatibleTail(bytes[1..]);
      compatible := Quote.SpecShellCompatibleByte(bytes[0], true, |bytes| == 1) && compatible;
    }
    if Quote.SpecContainsApostrophe(bytes) && compatible {
      var body := CQuoteBody(bytes);
      quoted := "\"" + body + "\"";
    } else {
      var body := ShellEscapeTail(bytes);
      quoted := "'" + body;
    }
  }

  method ScanLeadingHyphen(data: BenchWorld.Bytes) returns (found: bool)
    ensures found == Spec.LeadingHyphen(data)
  {
    var i := 0;
    while i < |data|
      invariant 0 <= i <= |data|
      invariant forall j: nat | j < i :: data[j] != '-' || (j > 0 && data[j - 1] != '/')
      decreases |data| - i
    {
      if data[i] == '-' && (i == 0 || data[i - 1] == '/') { return true; }
      i := i + 1;
    }
    return false;
  }

  method ScanPortable(data: BenchWorld.Bytes) returns (index: nat)
    ensures index <= |data|
    ensures forall j: nat | j < index :: Spec.PortableByte(data[j])
    ensures index < |data| ==> !Spec.PortableByte(data[index])
  {
    index := 0;
    while index < |data|
      invariant index <= |data|
      invariant forall j: nat | j < index :: Spec.PortableByte(data[j])
      decreases |data| - index
    {
      if !Spec.PortableByte(data[index]) { return; }
      index := index + 1;
    }
  }

  method ScanComponents(data: BenchWorld.Bytes) returns (start: nat, end: nat, valid: bool)
    ensures valid == (forall first: nat, last: nat | first < last <= |data| ::
                        Spec.Component(data, first, last) ==> last - first <= Spec.ComponentByteLimit)
    ensures !valid ==> Spec.FirstLongComponent(data, start, end)
  {
    start := 0;
    end := 0;
    valid := false;
    while start < |data|
      invariant 0 <= start <= |data|
      invariant start == 0 || start == |data| || data[start] == '/' || data[start - 1] == '/'
      invariant forall first: nat, last: nat | first < last <= |data| && first < start ::
                  Spec.Component(data, first, last) ==> last - first <= Spec.ComponentByteLimit
      decreases |data| - start
    {
      if data[start] == '/' {
        start := start + 1;
      } else {
        end := start + 1;
        while end < |data| && data[end] != '/'
          invariant start < end <= |data|
          invariant forall j: nat | start <= j < end :: data[j] != '/'
          decreases |data| - end
        {
          end := end + 1;
        }
        assert Spec.Component(data, start, end);
        if end - start > Spec.ComponentByteLimit {
          return;
        }
        forall first: nat, last: nat | first < last <= |data| && first < end
          ensures Spec.Component(data, first, last) ==> last - first <= Spec.ComponentByteLimit
        {
          if Spec.Component(data, first, last) && first >= start {
            Proof.ComponentUnique(data, start, end, first, last);
          }
        }
        start := end;
      }
    }
    valid := true;
  }

  method CheckName(path: string, extra: bool) returns (diagnostics: BenchWorld.Bytes, valid: bool)
    ensures Spec.NameDiagnostic(path, extra, diagnostics)
    ensures valid == Spec.ValidName(Utf8.Encode(path), extra)
  {
    reveal Spec.NameDiagnostic(), Spec.ValidName();
    var data := Encode(path);
    valid := false;
    if extra {
      var found := ScanLeadingHyphen(data);
      if found {
        var quotedPath := QuoteAf(data);
        return Spec.LeadingHyphenMessage(quotedPath), false;
      }
    }
    if |data| == 0 { return Spec.EmptyNameText(), false; }
    var index := ScanPortable(data);
    if index < |data| {
      var quotedPath := QuoteAf(data);
      return Spec.NonPortableCharacterMessage(data[index], quotedPath), false;
    }
    if |data| > Spec.PathByteLimit {
      var limitText := Decimal(Spec.PathByteLimit);
      var lengthText := Decimal(|data|);
      var quotedPath := QuoteAf(data);
      return Spec.PathLengthMessage(limitText, lengthText, quotedPath), false;
    }
    var start, end, componentsValid := ScanComponents(data);
    if !componentsValid {
      var limitText := Decimal(Spec.ComponentByteLimit);
      var lengthText := Decimal(end - start);
      return Spec.ComponentLengthText(limitText, lengthText, data[start..end]), false;
    }
    return [], true;
  }

  method {:isolate_assertions} Prepare(raw: Schema.PathchkCmdRaw) returns (
      exit: int, plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes
    )
    requires Spec.AllowedInput(raw)
    ensures Spec.PreparedSpec(raw, exit, plannedStdout, plannedStderr)
  {
    plannedStdout := [];
    plannedStderr := [];
    if raw.mode == Schema.ModeHelp {
      plannedStdout := Spec.HelpTextSpec();
      exit := 0;
    } else if raw.mode == Schema.ModeVersion {
      plannedStdout := Spec.VersionTextSpec();
      exit := 0;
    } else if raw.mode == Schema.ModeMissingOperand || |raw.operands| == 0 {
      plannedStderr := Spec.MissingOperandText();
      exit := 1;
    } else {
      var i := 0;
      var allValid := true;
      ghost var cuts: seq<nat> := [0];
      while i < |raw.operands|
        invariant 0 <= i <= |raw.operands|
        invariant Spec.OrderedDiagnostics(raw.operands[..i], raw.checkExtraPortability,
                                          plannedStderr, cuts)
        invariant allValid == (forall j: nat | j < i ::
                                 Spec.ValidName(Utf8.Encode(raw.operands[j]), raw.checkExtraPortability))
        decreases |raw.operands| - i
      {
        var piece, valid := CheckName(raw.operands[i], raw.checkExtraPortability);
        Proof.ExtendDiagnostics(raw.operands[..i], raw.checkExtraPortability,
                                plannedStderr, cuts, raw.operands[i], piece);
        Proof.ExtendValidity(raw.operands, raw.checkExtraPortability, i);
        assert raw.operands[..i + 1] == raw.operands[..i] + [raw.operands[i]];
        plannedStderr := plannedStderr + piece;
        cuts := cuts + [|plannedStderr|];
        allValid := allValid && valid;
        i := i + 1;
      }
      exit := if allValid then 0 else 1;
      Proof.AssembleResult(raw, plannedStderr, cuts, allValid);
    }
  }

  method Flush(output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes,
               normalExit: int, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                io.trustedStreams(), output, diagnostics, normalExit, exit)
  {
    var committed: nat := 0;
    var outErr := 0;
    if output != [] {
      var result := io.WriteStdout(output);
      committed := C.WriteResultCommitted(result);
      outErr := C.ResultErrno(result);
    }
    var finalDiagnostics := diagnostics;
    if outErr != 0 {
      var reason := io.GetCLocaleErrnoText(outErr);
      finalDiagnostics := diagnostics + Spec.WriteErrorText(reason);
    }
    assert finalDiagnostics == diagnostics +
                               (if outErr == 0 then [] else Spec.WriteErrorText(C.CLocaleErrnoTextResult(outErr)));
    var errCommitted: nat := 0;
    var errErr := 0;
    if finalDiagnostics != [] {
      var result := io.WriteStderr(finalDiagnostics);
      errCommitted := C.WriteResultCommitted(result);
      errErr := C.ResultErrno(result);
      assert C.WriteStderrSpec(old(io.stderr()), io.trustedStreams(), io.stderr(),
                               finalDiagnostics, errCommitted, errErr);
    }
    exit := if outErr != 0 || errErr != 0 then 1 else normalExit;
    assert Spec.EmissionOutcomeFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                      io.trustedStreams(), output, diagnostics, normalExit, exit,
                                      committed, outErr, errCommitted, errErr);
  }

  method RunCore(raw: Schema.PathchkCmdRaw, io: BenchIO.IO) returns (exit: int)
    modifies io.stdoutRegion, io.stderrRegion
    ensures Spec.Spec(raw, io, exit)
  {
    if !Spec.AllowedInput(raw) { return 1; }
    var normalExit, output, diagnostics := Prepare(raw);
    exit := Flush(output, diagnostics, normalExit, io);
    Proof.Complete(raw, io, output, diagnostics, normalExit, exit);
  }
}
