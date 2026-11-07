include "../../../core/IO.dfy"
include "../Spec/PathchkSchema.dfy"
include "../Spec/PathchkSpec.dfy"
include "../../wc/Impl/WcCore.dfy"
include "../../wc/Proof/WcProof.dfy"

module PathchkCore {
  import BenchIO
  import BenchWorld
  import Schema = PathchkSchema
  import Spec = PathchkSpec
  import C = IOContract
  import Utf8 = Utf8Semantics
  import Numbers = WcSpec
  import NumberCore = WcCore
  import NumberProof = WcProof

  ghost opaque predicate PreparedSummary(
    raw: Schema.PathchkCmdRaw, exit: int,
    plannedStdout: BenchWorld.Bytes, plannedStderr: BenchWorld.Bytes
  )
  { Spec.PreparedSpec(raw, exit, plannedStdout, plannedStderr) }

  twostate predicate CoreSummary(raw: Schema.PathchkCmdRaw, io: BenchIO.IO, exit: int)
    reads io.stdoutRegion, io.stderrRegion, io.trustedStreamsRegion
  {
    Spec.AllowedInput(raw) ==>
      exists output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int ::
        PreparedSummary(raw, normalExit, output, diagnostics) &&
        Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                            io.trustedStreams(), output, diagnostics, normalExit, exit)
  }

  method Decimal(n: nat) returns (text: BenchWorld.Bytes)
    ensures Numbers.DecimalText(n, text)
  {
    text := NumberCore.Digits(n);
    ghost var expected, digits, values := NumberProof.DecimalTextForCore(n);
  }

  lemma ComponentUnique(data: BenchWorld.Bytes, start: nat, end: nat, first: nat, last: nat)
    requires Spec.Component(data, start, end) && Spec.Component(data, first, last)
    requires start <= first < end
    ensures first == start && last == end
  {
    if first > start { assert data[first - 1] != '/'; }
    if last < end { assert data[last] != '/'; }
    if end < last { assert data[end] != '/'; }
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
            ComponentUnique(data, start, end, first, last);
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
    var data := Utf8.Encode(path);
    valid := false;
    if extra {
      var found := ScanLeadingHyphen(data);
      if found { return Spec.LeadingHyphenText(path), false; }
    }
    if |data| == 0 { return Spec.EmptyNameText(), false; }
    var index := ScanPortable(data);
    if index < |data| { return Spec.NonPortableCharacterText(data[index], path), false; }
    if |data| > Spec.PathByteLimit {
      var limitText := Decimal(Spec.PathByteLimit);
      var lengthText := Decimal(|data|);
      return Spec.PathLengthText(limitText, lengthText, path), false;
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
    ensures PreparedSummary(raw, exit, plannedStdout, plannedStderr)
  {
    reveal PreparedSummary();
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
        invariant |cuts| == i + 1 && cuts[0] == 0 && cuts[i] == |plannedStderr|
        invariant forall j: nat {:trigger cuts[j]} | j < i ::
                    cuts[j] <= cuts[j + 1] <= |plannedStderr| &&
                    Spec.NameDiagnostic(raw.operands[j], raw.checkExtraPortability,
                                        plannedStderr[cuts[j]..cuts[j + 1]])
        invariant allValid == (forall j: nat | j < i ::
                                 Spec.ValidName(Utf8.Encode(raw.operands[j]), raw.checkExtraPortability))
        decreases |raw.operands| - i
      {
        var piece, valid := CheckName(raw.operands[i], raw.checkExtraPortability);
        ghost var previous := plannedStderr;
        ghost var previousCuts := cuts;
        ghost var previousAllValid := allValid;
        plannedStderr := plannedStderr + piece;
        cuts := cuts + [|plannedStderr|];
        forall j: nat {:trigger cuts[j]} | j < i + 1
          ensures cuts[j] <= cuts[j + 1] <= |plannedStderr|
          ensures Spec.NameDiagnostic(raw.operands[j], raw.checkExtraPortability,
                                      plannedStderr[cuts[j]..cuts[j + 1]])
        {
          if j < i {
            assert cuts[j] == previousCuts[j] && cuts[j + 1] == previousCuts[j + 1];
            assert previousCuts[j] <= previousCuts[j + 1] <= |previous|;
            assert Spec.NameDiagnostic(raw.operands[j], raw.checkExtraPortability,
                                       previous[previousCuts[j]..previousCuts[j + 1]]);
            assert plannedStderr[..|previous|] == previous;
            assert plannedStderr[cuts[j]..cuts[j + 1]] ==
                   previous[previousCuts[j]..previousCuts[j + 1]];
          } else {
            assert plannedStderr[cuts[j]..cuts[j + 1]] == piece;
          }
        }
        allValid := allValid && valid;
        assert allValid == (forall j: nat | j < i + 1 ::
                              Spec.ValidName(Utf8.Encode(raw.operands[j]), raw.checkExtraPortability)) by {
          if allValid {
            forall j: nat | j < i + 1
              ensures Spec.ValidName(Utf8.Encode(raw.operands[j]), raw.checkExtraPortability)
            {
              if j < i {
                assert Spec.ValidName(Utf8.Encode(raw.operands[j]), raw.checkExtraPortability);
              } else { assert j == i; }
            }
          } else if !previousAllValid {
            var j: nat :| j < i && !Spec.ValidName(Utf8.Encode(raw.operands[j]), raw.checkExtraPortability);
            assert j < i + 1;
          } else {
            assert !Spec.ValidName(Utf8.Encode(raw.operands[i]), raw.checkExtraPortability);
          }
        }
        i := i + 1;
      }
      exit := if allValid then 0 else 1;
      assert Spec.PathchkResult(raw, plannedStderr, exit);
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
    ensures CoreSummary(raw, io, exit)
  {
    if !Spec.AllowedInput(raw) { return 1; }
    var normalExit, output, diagnostics := Prepare(raw);
    exit := Flush(output, diagnostics, normalExit, io);
  }
}
