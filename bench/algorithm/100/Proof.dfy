include "Spec.dfy"
include "Core.dfy"

module Algorithm100Proof {
  import SpecMod = Algorithm100Spec
  import Core = Algorithm100Core

  lemma MinEqual(a: int, b: int)
    ensures Core.Min(a, b) == SpecMod.Min(a, b)
  {
  }

  lemma FramePixelsEqual(r1: int, c1: int, d: int)
    ensures Core.FramePixels(r1, c1, d) == SpecMod.FramePixels(r1, c1, d)
  {
    assert forall p :: p in Core.FramePixels(r1, c1, d) <==> p in SpecMod.FramePixels(r1, c1, d);
  }

  lemma ValidScreenCoreToSpec(n: int, m: int, screen: seq<string>)
    requires Core.ValidScreen(n, m, screen)
    ensures SpecMod.ValidScreen(n, m, screen)
  {
  }

  lemma ValidScreenSpecToCore(n: int, m: int, screen: seq<string>)
    requires SpecMod.ValidScreen(n, m, screen)
    ensures Core.ValidScreen(n, m, screen)
  {
  }

  lemma ValidOutputGridCoreToSpec(n: int, m: int, output_lines: seq<string>)
    requires Core.ValidOutputGrid(n, m, output_lines)
    ensures SpecMod.ValidOutputGrid(n, m, output_lines)
  {
  }

  lemma FrameWithinBoundsCoreToSpec(n: int, m: int, r1: int, c1: int, d: int)
    requires Core.IsFrameWithinBounds(n, m, r1, c1, d)
    ensures SpecMod.IsFrameWithinBounds(n, m, r1, c1, d)
  {
  }

  lemma FrameWithinBoundsSpecToCore(n: int, m: int, r1: int, c1: int, d: int)
    requires SpecMod.IsFrameWithinBounds(n, m, r1, c1, d)
    ensures Core.IsFrameWithinBounds(n, m, r1, c1, d)
  {
  }

  lemma AllWhitesCoreToSpec(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
    requires Core.AllWhitesOnFrame(n, m, screen, r1, c1, d)
    ensures SpecMod.AllWhitesOnFrame(n, m, screen, r1, c1, d)
  {
    ValidScreenCoreToSpec(n, m, screen);
    FrameWithinBoundsCoreToSpec(n, m, r1, c1, d);
    FramePixelsEqual(r1, c1, d);
  }

  lemma AllWhitesSpecToCore(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
    requires SpecMod.AllWhitesOnFrame(n, m, screen, r1, c1, d)
    ensures Core.AllWhitesOnFrame(n, m, screen, r1, c1, d)
  {
    ValidScreenSpecToCore(n, m, screen);
    FrameWithinBoundsSpecToCore(n, m, r1, c1, d);
    FramePixelsEqual(r1, c1, d);
  }

  lemma IsValidFrameCoreToSpec(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
    requires Core.IsValidFrame(n, m, screen, r1, c1, d)
    ensures SpecMod.IsValidFrame(n, m, screen, r1, c1, d)
  {
    ValidScreenCoreToSpec(n, m, screen);
    FrameWithinBoundsCoreToSpec(n, m, r1, c1, d);
    AllWhitesCoreToSpec(n, m, screen, r1, c1, d);
    FramePixelsEqual(r1, c1, d);
  }

  lemma IsValidFrameSpecToCore(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
    requires SpecMod.IsValidFrame(n, m, screen, r1, c1, d)
    ensures Core.IsValidFrame(n, m, screen, r1, c1, d)
  {
    ValidScreenSpecToCore(n, m, screen);
    FrameWithinBoundsSpecToCore(n, m, r1, c1, d);
    AllWhitesSpecToCore(n, m, screen, r1, c1, d);
    FramePixelsEqual(r1, c1, d);
  }

  lemma IsMinimalFrameCoreToSpec(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
    requires Core.IsMinimalFrame(n, m, screen, r1, c1, d)
    ensures SpecMod.IsMinimalFrame(n, m, screen, r1, c1, d)
  {
    IsValidFrameCoreToSpec(n, m, screen, r1, c1, d);
    forall d', r1', c1' |
      1 <= d' < d && 0 <= r1' <= n - d' && 0 <= c1' <= m - d'
      ensures !SpecMod.IsValidFrame(n, m, screen, r1', c1', d')
    {
      if SpecMod.IsValidFrame(n, m, screen, r1', c1', d') {
        IsValidFrameSpecToCore(n, m, screen, r1', c1', d');
        assert false;
      }
    }
  }

  lemma FrameOutputLinesCoreToSpec(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int, output_lines: seq<string>)
    requires Core.FrameOutputLines(n, m, screen, r1, c1, d, output_lines)
    ensures SpecMod.FrameOutputLines(n, m, screen, r1, c1, d, output_lines)
  {
    ValidScreenCoreToSpec(n, m, screen);
    FramePixelsEqual(r1, c1, d);
  }

  lemma CoreSummaryImpliesSpec(n: int, m: int, screen: seq<string>, output_lines: seq<string>)
    ensures Core.CoreSummary(n, m, screen, output_lines) ==>
              SpecMod.Spec(n, m, screen, output_lines)
  {
    if Core.CoreSummary(n, m, screen, output_lines) {
      ValidScreenCoreToSpec(n, m, screen);
      MinEqual(n, m);
      assert Core.RuntimeCoreSummary(n, m, screen, output_lines);
      if output_lines == SpecMod.FailureResult() {
        if Core.ValidOutputGrid(n, m, output_lines) {
          assert n == 1;
          assert output_lines[0] == SpecMod.FailureResult()[0];
          assert |output_lines[0]| == 2;
          assert m == 2;
          assert output_lines[0][0] == '-';
          assert false;
        }
        assert output_lines == SpecMod.FailureResult() &&
               forall r1, c1, d ::
                 0 <= r1 <= n - d && 0 <= c1 <= m - d && 1 <= d <= Core.Min(n, m) ==>
                   !Core.IsValidFrame(n, m, screen, r1, c1, d);
        forall r1, c1, d | 0 <= r1 <= n - d && 0 <= c1 <= m - d && 1 <= d <= SpecMod.Min(n, m)
          ensures !SpecMod.IsValidFrame(n, m, screen, r1, c1, d)
        {
          if SpecMod.IsValidFrame(n, m, screen, r1, c1, d) {
            IsValidFrameSpecToCore(n, m, screen, r1, c1, d);
            assert 0 <= r1 <= n - d;
            assert 0 <= c1 <= m - d;
            assert 1 <= d <= Core.Min(n, m);
            assert !Core.IsValidFrame(n, m, screen, r1, c1, d);
            assert false;
          }
        }
      } else {
        assert exists r1, c1, d ::
            0 <= r1 <= n - d &&
            0 <= c1 <= m - d &&
            1 <= d <= Core.Min(n, m) &&
            Core.IsValidFrame(n, m, screen, r1, c1, d) &&
            Core.IsMinimalFrame(n, m, screen, r1, c1, d) &&
            Core.FrameOutputLines(n, m, screen, r1, c1, d, output_lines);
        var r1, c1, d :|
          0 <= r1 <= n - d &&
          0 <= c1 <= m - d &&
          1 <= d <= Core.Min(n, m) &&
          Core.IsValidFrame(n, m, screen, r1, c1, d) &&
          Core.IsMinimalFrame(n, m, screen, r1, c1, d) &&
          Core.FrameOutputLines(n, m, screen, r1, c1, d, output_lines);
        ValidOutputGridCoreToSpec(n, m, output_lines);
        IsValidFrameCoreToSpec(n, m, screen, r1, c1, d);
        IsMinimalFrameCoreToSpec(n, m, screen, r1, c1, d);
        FrameOutputLinesCoreToSpec(n, m, screen, r1, c1, d, output_lines);
      }
      assert SpecMod.Spec(n, m, screen, output_lines);
    }
  }
}
