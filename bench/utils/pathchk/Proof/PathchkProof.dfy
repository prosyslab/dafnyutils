include "../Spec/PathchkSpec.dfy"

module PathchkProof {
  import BenchIO
  import BenchWorld
  import Schema = PathchkSchema
  import Spec = PathchkSpec
  import Utf8 = Utf8Semantics

  lemma DecimalStep(n: nat, prefix: BenchWorld.Bytes)
    requires if n < 10 then prefix == [] else Spec.DecimalText(n / 10, prefix)
    ensures Spec.DecimalText(n, prefix + [('0' as int + n % 10) as char])
  {
    var text := prefix + [('0' as int + n % 10) as char];
    var values: seq<nat>;
    if n < 10 {
      values := [0, n];
    } else {
      var prefixValues: seq<nat> :| Spec.DecimalTextWitness(n / 10, prefix, prefixValues);
      values := prefixValues + [n];
      assert prefix[0] != '0';
      assert forall i: nat | i < |text| ::
          '0' <= text[i] <= '9' &&
          values[i + 1] == values[i] * 10 + (text[i] as int - '0' as int) by {
        forall i: nat | i < |text|
          ensures '0' <= text[i] <= '9'
          ensures values[i + 1] == values[i] * 10 + (text[i] as int - '0' as int)
        {
          if i == |prefix| {
            assert values[i] == n / 10;
            assert n == n / 10 * 10 + n % 10;
          }
        }
      }
    }
    assert Spec.DecimalTextWitness(n, text, values);
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

  lemma ExtendDiagnostics(
    paths: seq<string>, extra: bool, diagnostics: BenchWorld.Bytes, cuts: seq<nat>,
    path: string, piece: BenchWorld.Bytes
  )
    requires Spec.OrderedDiagnostics(paths, extra, diagnostics, cuts)
    requires Spec.NameDiagnostic(path, extra, piece)
    ensures Spec.OrderedDiagnostics(paths + [path], extra, diagnostics + piece,
                                    cuts + [|diagnostics| + |piece|])
  {
    hide *;
    reveal Spec.OrderedDiagnostics();
    var nextDiagnostics := diagnostics + piece;
    var nextCuts := cuts + [|nextDiagnostics|];
    forall i: nat {:trigger nextCuts[i]} | i < |paths| + 1
      ensures nextCuts[i] <= nextCuts[i + 1] <= |nextDiagnostics|
      ensures Spec.NameDiagnostic((paths + [path])[i], extra,
                                  nextDiagnostics[nextCuts[i]..nextCuts[i + 1]])
    {
      if i < |paths| {
        assert cuts[i] <= cuts[i + 1] <= |diagnostics|;
        assert Spec.NameDiagnostic(paths[i], extra, diagnostics[cuts[i]..cuts[i + 1]]);
        assert nextCuts[i] == cuts[i] && nextCuts[i + 1] == cuts[i + 1];
        assert nextDiagnostics[..|diagnostics|] == diagnostics;
        assert nextDiagnostics[nextCuts[i]..nextCuts[i + 1]] == diagnostics[cuts[i]..cuts[i + 1]];
      } else {
        assert nextDiagnostics[nextCuts[i]..nextCuts[i + 1]] == piece;
      }
    }
  }

  lemma ExtendValidity(paths: seq<string>, extra: bool, count: nat)
    requires count < |paths|
    ensures (forall i: nat | i < count + 1 :: Spec.ValidName(Utf8.Encode(paths[i]), extra)) <==>
            ((forall i: nat | i < count :: Spec.ValidName(Utf8.Encode(paths[i]), extra)) &&
             Spec.ValidName(Utf8.Encode(paths[count]), extra))
  {
    if (forall i: nat | i < count :: Spec.ValidName(Utf8.Encode(paths[i]), extra)) &&
       Spec.ValidName(Utf8.Encode(paths[count]), extra) {
      forall i: nat | i < count + 1
        ensures Spec.ValidName(Utf8.Encode(paths[i]), extra)
      {
        if i < count {
          assert Spec.ValidName(Utf8.Encode(paths[i]), extra);
        }
      }
    }
    if forall i: nat | i < count + 1 :: Spec.ValidName(Utf8.Encode(paths[i]), extra) {
      assert Spec.ValidName(Utf8.Encode(paths[count]), extra);
      forall i: nat | i < count
        ensures Spec.ValidName(Utf8.Encode(paths[i]), extra)
      {
        assert i < count + 1;
      }
    }
  }

  lemma AssembleResult(
    raw: Schema.PathchkCmdRaw, diagnostics: BenchWorld.Bytes, cuts: seq<nat>, allValid: bool
  )
    requires |raw.operands| > 0
    requires Spec.OrderedDiagnostics(raw.operands, raw.checkExtraPortability, diagnostics, cuts)
    requires allValid == (forall i: nat | i < |raw.operands| ::
                            Spec.ValidName(Utf8.Encode(raw.operands[i]), raw.checkExtraPortability))
    ensures Spec.PathchkResult(raw, diagnostics, if allValid then 0 else 1)
  {
    hide *;
    reveal Spec.PathchkResult();
    assert exists chosenCuts: seq<nat> ::
        Spec.OrderedDiagnostics(raw.operands, raw.checkExtraPortability, diagnostics, chosenCuts) &&
        (if allValid then 0 else 1) ==
        (if forall i: nat | i < |raw.operands| ::
              Spec.ValidName(Utf8.Encode(raw.operands[i]), raw.checkExtraPortability)
         then 0 else 1);
  }

  twostate lemma Complete(
    raw: Schema.PathchkCmdRaw, io: BenchIO.IO,
    output: BenchWorld.Bytes, diagnostics: BenchWorld.Bytes, normalExit: int, exit: int
  )
    requires Spec.PreparedSpec(raw, normalExit, output, diagnostics)
    requires Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                                 io.trustedStreams(), output, diagnostics, normalExit, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    assert exists chosenOutput: BenchWorld.Bytes, chosenDiagnostics: BenchWorld.Bytes, chosenExit: int ::
        Spec.PreparedSpec(raw, chosenExit, chosenOutput, chosenDiagnostics) &&
        Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                            io.trustedStreams(), chosenOutput, chosenDiagnostics, chosenExit, exit);
  }
}
