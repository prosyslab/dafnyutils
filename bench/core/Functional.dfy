module BenchFunctional {
  opaque function Map<T, R>(f: T ~> R, xs: seq<T>): (result: seq<R>)
    requires forall i: nat :: i < |xs| ==> f.requires(xs[i])
    reads set i, o | 0 <= i < |xs| && o in f.reads(xs[i]) :: o
    ensures |result| == |xs|
    ensures forall i: nat {:trigger result[i]} ::
      i < |xs| ==> result[i] == f(xs[i])
    decreases |xs|
  {
    if |xs| == 0 then []
    else [f(xs[0])] + Map(f, xs[1..])
  }

  opaque function MapIdx<T, R>(
      f: (nat, T) ~> R, xs: seq<T>, offset: nat := 0): (result: seq<R>)
    requires forall i: nat :: i < |xs| ==> f.requires(offset + i, xs[i])
    reads set i, o {:nowarn} |
      0 <= i < |xs| && o in f.reads(offset + i, xs[i]) :: o
    ensures |result| == |xs|
    ensures forall i: nat {:trigger result[i]} ::
      i < |xs| ==> result[i] == f(offset + i, xs[i])
    decreases |xs|
  {
    if |xs| == 0 then []
    else [f(offset, xs[0])] + MapIdx(f, xs[1..], offset + 1)
  }

  opaque function Enumerate<T>(xs: seq<T>): (result: seq<(nat, T)>)
    ensures |result| == |xs|
    ensures forall i: nat {:trigger result[i]} ::
      i < |xs| ==> result[i] == (i, xs[i])
  {
    MapIdx((i: nat, x: T) => (i, x), xs)
  }

  // Count true entries in mask[start..]. The positions remain relative to mask.
  function CountTrue(mask: seq<bool>, start: nat := 0): (count: nat)
    requires start <= |mask|
    ensures count <= |mask| - start
    decreases |mask| - start
  {
    if start == |mask| then 0
    else (if mask[start] then 1 else 0) + CountTrue(mask, start + 1)
  }

  // Exact, strictly increasing enumeration of the selected input positions.
  opaque function SelectedIndices(
      mask: seq<bool>, start: nat := 0): (ids: seq<nat>)
    requires start <= |mask|
    ensures |ids| == CountTrue(mask, start)
    ensures |ids| <= |mask| - start
    ensures forall k: nat {:trigger ids[k]} ::
      k < |ids| ==> start <= ids[k] < |mask| && mask[ids[k]]
    ensures forall j: nat, k: nat {:trigger ids[j], ids[k]} ::
      j < k < |ids| ==> ids[j] < ids[k]
    ensures forall i: nat ::
      (i in ids) <==> (start <= i < |mask| && mask[i])
    decreases |mask| - start
  {
    if start == |mask| then []
    else
      var tail := SelectedIndices(mask, start + 1);
      assert start !in tail;
      if mask[start] then
        var chosen := [start] + tail;
        assert forall j: nat, k: nat ::
          j < k < |chosen| ==> chosen[j] < chosen[k] by {
          forall j: nat, k: nat | j < k < |chosen|
            ensures chosen[j] < chosen[k]
          {
            if j == 0 {
              assert chosen[j] == start;
              assert chosen[k] == tail[k - 1];
            } else {
              assert chosen[j] == tail[j - 1];
              assert chosen[k] == tail[k - 1];
            }
          }
        }
        chosen
      else tail
  }

  // Gather is intentionally allowed to repeat indices; SelectedIndices is not.
  opaque function Gather<T>(xs: seq<T>, ids: seq<nat>): (result: seq<T>)
    requires forall k: nat :: k < |ids| ==> ids[k] < |xs|
    ensures |result| == |ids|
    ensures forall k: nat {:trigger result[k]} ::
      k < |ids| ==> result[k] == xs[ids[k]]
    ensures forall k: nat :: k < |result| ==> result[k] in xs
    ensures forall i: nat :: i in ids ==> i < |xs| && xs[i] in result
  {
    var ys := seq(|ids|, (k: nat)
      requires k < |ids|
      => xs[ids[k]]);
    assert forall i: nat :: i in ids ==> i < |xs| && xs[i] in ys by {
      forall i: nat | i in ids
        ensures i < |xs| && xs[i] in ys
      {
        var k: nat :| k < |ids| && ids[k] == i;
        assert ys[k] == xs[i];
      }
    }
    ys
  }

  // Unary filtering: both the mask and its exact selected positions are specified.
  opaque function Filter<T>(p: T ~> bool, xs: seq<T>): (result: seq<T>)
    requires forall i: nat :: i < |xs| ==> p.requires(xs[i])
    reads set i, o | 0 <= i < |xs| && o in p.reads(xs[i]) :: o
    ensures |result| <= |xs|
    ensures |result| == CountTrue(Map(p, xs))
    ensures |result| == |SelectedIndices(Map(p, xs))|
    ensures forall k: nat {:trigger result[k]} ::
      k < |result| ==> result[k] == xs[SelectedIndices(Map(p, xs))[k]]
    ensures forall k: nat :: k < |result| ==>
      result[k] in xs && p.requires(result[k]) && p(result[k])
    ensures forall i: nat ::
      i < |xs| && p(xs[i]) ==> xs[i] in result
  {
    Gather(xs, SelectedIndices(Map(p, xs)))
  }

  opaque function FilterIndices<T>(
      p: (nat, T) ~> bool, xs: seq<T>, offset: nat := 0): (ids: seq<nat>)
    requires forall i: nat :: i < |xs| ==> p.requires(offset + i, xs[i])
    reads set i, o {:nowarn} |
      0 <= i < |xs| && o in p.reads(offset + i, xs[i]) :: o
    ensures |ids| <= |xs|
    ensures |ids| == CountTrue(MapIdx(p, xs, offset))
    ensures forall k: nat {:trigger ids[k]} :: k < |ids| ==>
      ids[k] < |xs| &&
      p.requires(offset + ids[k], xs[ids[k]]) &&
      p(offset + ids[k], xs[ids[k]])
    ensures forall j: nat, k: nat {:trigger ids[j], ids[k]} ::
      j < k < |ids| ==> ids[j] < ids[k]
    ensures forall i: nat ::
      (i in ids) <==> (i < |xs| && p(offset + i, xs[i]))
  {
    SelectedIndices(MapIdx(p, xs, offset))
  }

  opaque function FilterIdx<T>(
      p: (nat, T) ~> bool, xs: seq<T>, offset: nat := 0): (result: seq<T>)
    requires forall i: nat :: i < |xs| ==> p.requires(offset + i, xs[i])
    reads set i, o {:nowarn} |
      0 <= i < |xs| && o in p.reads(offset + i, xs[i]) :: o
    ensures |result| <= |xs|
    ensures |result| == |FilterIndices(p, xs, offset)|
    ensures |result| == CountTrue(MapIdx(p, xs, offset))
    ensures forall k: nat {:trigger result[k]} :: k < |result| ==>
      result[k] == xs[FilterIndices(p, xs, offset)[k]]
    ensures forall k: nat :: k < |result| ==>
      result[k] in xs &&
      p.requires(offset + FilterIndices(p, xs, offset)[k], result[k]) &&
      p(offset + FilterIndices(p, xs, offset)[k], result[k])
    ensures forall i: nat ::
      i < |xs| && p(offset + i, xs[i]) ==> xs[i] in result
  {
    Gather(xs, FilterIndices(p, xs, offset))
  }

  // Scans expose every accumulator value, including the initial value.
  opaque function ScanLeft<A, T>(
      f: (A, T) -> A, init: A, xs: seq<T>): (states: seq<A>)
    ensures |states| == |xs| + 1
    ensures states[0] == init
    ensures forall i: nat {:trigger states[i]} ::
      i < |xs| ==> states[i + 1] == f(states[i], xs[i])
    decreases |xs|
  {
    if |xs| == 0 then [init]
    else
      var next := f(init, xs[0]);
      var tail := ScanLeft(f, next, xs[1..]);
      var result := [init] + tail;
      forall i: nat | i < |xs|
        ensures result[i + 1] == f(result[i], xs[i])
      {
        if i == 0 {
          assert tail[0] == next;
        } else {
          assert i - 1 < |xs[1..]|;
          assert tail[(i - 1) + 1] == f(tail[i - 1], xs[1..][i - 1]);
          assert xs[1..][i - 1] == xs[i];
        }
      }
      result
  }

  opaque function ScanRight<A, T>(
      f: (T, A) -> A, xs: seq<T>, init: A): (states: seq<A>)
    ensures |states| == |xs| + 1
    ensures states[|xs|] == init
    ensures forall i: nat {:trigger states[i]} ::
      i < |xs| ==> states[i] == f(xs[i], states[i + 1])
    decreases |xs|
  {
    if |xs| == 0 then [init]
    else
      var tail := ScanRight(f, xs[1..], init);
      [f(xs[0], tail[0])] + tail
  }

  opaque function ScanLeftIdx<A, T>(
      f: (A, nat, T) -> A, init: A, xs: seq<T>, offset: nat := 0
    ): (states: seq<A>)
    ensures |states| == |xs| + 1
    ensures states[0] == init
    ensures forall i: nat {:trigger states[i]} ::
      i < |xs| ==> states[i + 1] == f(states[i], offset + i, xs[i])
    decreases |xs|
  {
    if |xs| == 0 then [init]
    else
      var next := f(init, offset, xs[0]);
      var tail := ScanLeftIdx(f, next, xs[1..], offset + 1);
      var result := [init] + tail;
      forall i: nat | i < |xs|
        ensures result[i + 1] == f(result[i], offset + i, xs[i])
      {
        if i == 0 {
          assert tail[0] == next;
        } else {
          assert i - 1 < |xs[1..]|;
          assert tail[(i - 1) + 1] ==
            f(tail[i - 1], offset + 1 + (i - 1), xs[1..][i - 1]);
          assert offset + 1 + (i - 1) == offset + i;
          assert xs[1..][i - 1] == xs[i];
        }
      }
      result
  }

  opaque function ScanRightIdx<A, T>(
      f: (nat, T, A) -> A, xs: seq<T>, init: A, offset: nat := 0
    ): (states: seq<A>)
    ensures |states| == |xs| + 1
    ensures states[|xs|] == init
    ensures forall i: nat {:trigger states[i]} ::
      i < |xs| ==> states[i] == f(offset + i, xs[i], states[i + 1])
    decreases |xs|
  {
    if |xs| == 0 then [init]
    else
      var tail := ScanRightIdx(f, xs[1..], init, offset + 1);
      [f(offset, xs[0], tail[0])] + tail
  }

  // Folds retain their recursive computation; scans occur only in specifications/proofs.
  opaque function FoldLeft<A, T>(
      f: (A, T) -> A, init: A, xs: seq<T>): (result: A)
    ensures |xs| == 0 ==> result == init
    ensures result == ScanLeft(f, init, xs)[|xs|]
    decreases |xs|
  {
    reveal ScanLeft();
    if |xs| == 0 then init
    else FoldLeft(f, f(init, xs[0]), xs[1..])
  }

  opaque function FoldRight<A, T>(
      f: (T, A) -> A, xs: seq<T>, init: A): (result: A)
    ensures |xs| == 0 ==> result == init
    ensures result == ScanRight(f, xs, init)[0]
    decreases |xs|
  {
    reveal ScanRight();
    if |xs| == 0 then init
    else f(xs[0], FoldRight(f, xs[1..], init))
  }

  opaque function FoldLeftIdx<A, T>(
      f: (A, nat, T) -> A, init: A, xs: seq<T>, offset: nat := 0
    ): (result: A)
    ensures |xs| == 0 ==> result == init
    ensures result == ScanLeftIdx(f, init, xs, offset)[|xs|]
    decreases |xs|
  {
    reveal ScanLeftIdx();
    if |xs| == 0 then init
    else FoldLeftIdx(f, f(init, offset, xs[0]), xs[1..], offset + 1)
  }

  opaque function FoldRightIdx<A, T>(
      f: (nat, T, A) -> A, xs: seq<T>, init: A, offset: nat := 0
    ): (result: A)
    ensures |xs| == 0 ==> result == init
    ensures result == ScanRightIdx(f, xs, init, offset)[0]
    decreases |xs|
  {
    reveal ScanRightIdx();
    if |xs| == 0 then init
    else f(offset, xs[0], FoldRightIdx(f, xs[1..], init, offset + 1))
  }

  lemma {:induction false} FoldLeftInvariantStep<A, T>(
      f: (A, T) -> A, xs: seq<T>, inv: (nat, A) -> bool,
      i: nat, a: A)
    requires forall j: nat, b: A ::
      j < |xs| && inv(j, b) ==> inv(j + 1, f(b, xs[j]))
    requires i < |xs|
    requires inv(i, a)
    ensures inv(i + 1, f(a, xs[i]))
  {
  }

  lemma {:induction false} FoldLeftIdxInvariantStep<A, T>(
      f: (A, nat, T) -> A, xs: seq<T>, inv: (nat, A) -> bool,
      offset: nat, i: nat, a: A)
    requires forall j: nat, b: A ::
      j < |xs| && inv(j, b) ==>
        inv(j + 1, f(b, offset + j, xs[j]))
    requires i < |xs|
    requires inv(i, a)
    ensures inv(i + 1, f(a, offset + i, xs[i]))
  {
  }

  lemma {:induction false} FoldRightIdxInvariantStep<A, T>(
      f: (nat, T, A) -> A, xs: seq<T>, inv: (nat, A) -> bool,
      offset: nat, i: nat, a: A)
    requires forall j: nat, b: A {:nowarn} ::
      j < |xs| && inv(j + 1, b) ==>
        inv(j, f(offset + j, xs[j], b))
    requires i < |xs|
    requires inv(i + 1, a)
    ensures inv(i, f(offset + i, xs[i], a))
  {
  }

  // A caller-supplied invariant may depend on the number of processed elements.
  lemma {:induction false} FoldLeftInvariant<A, T>(
      f: (A, T) -> A, init: A, xs: seq<T>, inv: (nat, A) -> bool)
    requires inv(0, init)
    requires forall i: nat, a: A ::
      i < |xs| && inv(i, a) ==> inv(i + 1, f(a, xs[i]))
    ensures inv(|xs|, FoldLeft(f, init, xs))
  {
    var states := ScanLeft(f, init, xs);
    var i: nat := 0;
    while i < |xs|
      invariant i <= |xs|
      invariant inv(i, states[i])
      invariant forall j: nat, a: A {:trigger inv(j, a)} ::
        j < |xs| && inv(j, a) ==> inv(j + 1, f(a, xs[j]))
      decreases |xs| - i
    {
      assert i < |xs|;
      assert inv(i, states[i]);
      assert states[i + 1] == f(states[i], xs[i]);
      FoldLeftInvariantStep(f, xs, inv, i, states[i]);
      assert inv(i + 1, states[i + 1]);
      i := i + 1;
    }
  }

  lemma {:induction false} FoldLeftIdxInvariant<A, T>(
      f: (A, nat, T) -> A, init: A, xs: seq<T>,
      inv: (nat, A) -> bool, offset: nat := 0)
    requires inv(0, init)
    requires forall i: nat, a: A ::
      i < |xs| && inv(i, a) ==> inv(i + 1, f(a, offset + i, xs[i]))
    ensures inv(|xs|, FoldLeftIdx(f, init, xs, offset))
  {
    var states := ScanLeftIdx(f, init, xs, offset);
    var i: nat := 0;
    while i < |xs|
      invariant i <= |xs|
      invariant inv(i, states[i])
      invariant forall j: nat, a: A {:trigger inv(j, a)} ::
        j < |xs| && inv(j, a) ==>
          inv(j + 1, f(a, offset + j, xs[j]))
      decreases |xs| - i
    {
      assert i < |xs|;
      assert inv(i, states[i]);
      assert states[i + 1] == f(states[i], offset + i, xs[i]);
      FoldLeftIdxInvariantStep(f, xs, inv, offset, i, states[i]);
      assert inv(i + 1, states[i + 1]);
      i := i + 1;
    }
  }

  lemma {:induction false} FoldRightIdxInvariant<A, T>(
      f: (nat, T, A) -> A, xs: seq<T>, init: A,
      inv: (nat, A) -> bool, offset: nat := 0)
    requires inv(|xs|, init)
    requires forall i: nat, a: A {:nowarn} ::
      i < |xs| && inv(i + 1, a) ==>
        inv(i, f(offset + i, xs[i], a))
    ensures inv(0, FoldRightIdx(f, xs, init, offset))
  {
    var states := ScanRightIdx(f, xs, init, offset);
    var i: nat := |xs|;
    while i > 0
      invariant i <= |xs|
      invariant inv(i, states[i])
      invariant forall j: nat, a: A {:nowarn} ::
        j < |xs| && inv(j + 1, a) ==>
          inv(j, f(offset + j, xs[j], a))
      decreases i
    {
      assert 0 < i <= |xs|;
      assert inv(i, states[i]);
      assert states[i - 1] == f(offset + i - 1, xs[i - 1], states[i]);
      FoldRightIdxInvariantStep(f, xs, inv, offset, i - 1, states[i]);
      assert inv(i - 1, states[i - 1]);
      i := i - 1;
    }
  }

  // Equality is needed only on the input elements, not on the entire domain T.
  lemma {:induction false} MapCongruence<T, R>(
      f: T ~> R, g: T ~> R, xs: seq<T>)
    requires forall i: nat :: i < |xs| ==>
      f.requires(xs[i]) && g.requires(xs[i]) && f(xs[i]) == g(xs[i])
    ensures Map(f, xs) == Map(g, xs)
  {
    var left := Map(f, xs);
    var right := Map(g, xs);
    forall i: nat | i < |xs|
      ensures left[i] == right[i]
    {
      assert left[i] == f(xs[i]);
      assert right[i] == g(xs[i]);
    }
    assert left == right;
  }
}
