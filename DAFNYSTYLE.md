# Dafny Agent Guidelines

Generation policy for Dafny code and proofs.

For utility benchmarks, also follow [the benchmark rules](bench/AGENTS.md) and
[the specification authoring guide](docs/adding-utilities.md). The generic
examples below do not authorize algorithmic principal specifications, wider
trusted APIs, or changes to an existing task's required behavior.

---

## 1. Contract first

**Rule:** Write the proof boundary before the body.

```dafny
method Find(a: array<int>, key: int) returns (idx: int)
  ensures idx == -1 || 0 <= idx < a.Length
  ensures idx != -1 ==> a[idx] == key
  ensures idx == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
{
  ...
}
```

**Rule:** Order clauses by well-formedness.

```dafny
method Use(a: array<int>?, i: int)
  requires a != null
  requires 0 <= i < a.Length
  requires a[i] >= 0
{
  ...
}
```

**Pattern:** Use named results.

```dafny
returns (idx: int)
ensures idx == -1 || 0 <= idx < a.Length
```

---

## 2. Model state with ghost values

**Rule:** Do not specify mutable state directly when a value model works.

```dafny
predicate Sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method Sort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  ...
}
```

**Pattern:** Use `seq`, `set`, `multiset`, `map`, and ghost predicates as the spec layer.

---

## 3. Use dynamic frames for heap objects

**Rule:** Each mutable object needs an invariant and a footprint.

```dafny
class Box {
  var x: int
  ghost var Repr: set<object>

  predicate Valid()
    reads this, Repr
  {
    this in Repr
  }

  constructor(v: int)
    modifies this
    ensures Valid()
  {
    x := v;
    Repr := {this};
  }

  method Set(v: int)
    requires Valid()
    modifies Repr
    ensures Valid()
    ensures x == v
  {
    x := v;
  }
}
```

**Pattern:** If `Repr` grows, add this postcondition.

```dafny
ensures fresh(Repr - old(Repr))
```

---

## 4. Shrink frames

**Rule:** Use field frames for single-field updates.

```dafny
class Counter {
  var n: int
  var name: string

  method Inc()
    modifies `n
    ensures n == old(n) + 1
    ensures name == old(name)
  {
    n := n + 1;
  }
}
```

**Reject:** `modifies this` when only one field changes.

For benchmark IO, use the exported region footprints. Do not restate invariance
already implied by the frame. Preserve behavioral relations inside a modified
region, such as the exact output suffix or the unaffected inodes in a filesystem.

---

## 5. Loops need proof-state invariants

**Rule:** A loop invariant must cover bounds, processed state, remaining state, frame preservation, and exit facts.

```dafny
method Find(a: array<int>, key: int) returns (idx: int)
  ensures idx == -1 || 0 <= idx < a.Length
  ensures idx != -1 ==> a[idx] == key
  ensures idx == -1 ==> forall j :: 0 <= j < a.Length ==> a[j] != key
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != key
    decreases a.Length - i
  {
    if a[i] == key { return i; }
    i := i + 1;
  }
  return -1;
}
```

**Check:** init, preservation, exit-to-postcondition.

---

## 6. Snapshot arrays before mutation

**Rule:** Use a ghost sequence to prove array-frame facts.

```dafny
method IncAll(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
{
  ghost var before := a[..];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] == before[j] + 1
    invariant forall j :: i <= j < a.Length ==> a[j] == before[j]
    decreases a.Length - i
  {
    a[i] := a[i] + 1;
    i := i + 1;
  }
}
```

**Reject:** Expecting Dafny to infer unchanged array segments.

---

## 7. Always give termination metrics

**Rule:** Add `decreases` to loops, recursive functions, and recursive lemmas.

```dafny
while i < n
  invariant 0 <= i <= n
  decreases n - i
{
  i := i + 1;
}
```

```dafny
lemma Visit(todo: set<Node>, fuel: nat)
  decreases |todo|, fuel
{
  ...
}
```

---

## 8. Localize proofs

**Rule:** Use `assert by` for the fact that fails.

```dafny
assert x <= z by {
  assert x <= y;
  assert y <= z;
}
```

**Rule:** Use `calc` for rewrite chains.

```dafny
calc {
  Sum(xs + [x]);
== { SumSnoc(xs, x); }
  Sum(xs) + x;
== { assert Sum(xs) == n; }
  n + x;
}
```

**Rule:** Use `forall` statements for universal goals.

```dafny
assert forall i :: 0 <= i < |xs| ==> P(xs[i]) by {
  forall i | 0 <= i < |xs|
    ensures P(xs[i])
  {
    ElementLemma(xs, i);
  }
}
```

---

## 9. Bound quantifiers

**Rule:** Every quantified variable needs a finite or structural domain.

```dafny
// Use
forall i :: 0 <= i < |xs| ==> xs[i] >= 0
forall o :: o in Repr ==> Closed(o)
forall k :: k in m.Keys ==> m[k] >= 0

// Reject
forall i :: xs[i] >= 0
```

**Rule:** Split quantifiers by purpose.

```dafny
invariant forall j :: 0 <= j < i ==> a[j] >= 0
invariant forall j :: i <= j < a.Length ==> a[j] == before[j]
```

---

## 10. Put hard facts in lemmas

**Rule:** Use lemmas for recursion, nonlinear arithmetic, quantifier instantiation, and datatype induction.

```dafny
lemma MulMonotone(a: nat, b: nat, c: nat)
  requires b <= c
  ensures a * b <= a * c
{
  ...
}

assert x * y <= x * z by {
  MulMonotone(x, y, z);
}
```

```dafny
lemma SizeNonnegative(t: Tree)
  ensures Size(t) >= 0
  decreases t
{
  match t
  case Leaf =>
  case Node(l, _, r) =>
    SizeNonnegative(l);
    SizeNonnegative(r);
}
```

---

## 11. Control recursive definitions

**Rule:** Make recursive spec functions `opaque` when expansion pollutes proof context.

```dafny
opaque function Sum(xs: seq<int>): int
  decreases |xs|
{
  if |xs| == 0 then 0 else xs[0] + Sum(xs[1..])
}

lemma SumNil()
  ensures Sum([]) == 0
{
  reveal Sum();
}
```

**Rule:** Reveal definitions inside lemmas, not across implementation code.

---

## 12. Align recursive specs with iterative code

**Rule:** Use `function by method` when the spec is recursive and the implementation is iterative.

**Scope:** This technique applies to appropriate implementation helpers. It does
not permit a utility's principal specification to compute its answer using an
accumulator or a control-flow mirror of Core. Keep implementation-only witnesses
in Core and relate them to the declarative Spec in Proof. Supplying a completed
algorithm as a shared helper still changes the task the candidate must solve.

```dafny
function SumUpTo(xs: seq<int>, n: nat): int
  requires n <= |xs|
  decreases n
{
  if n == 0 then 0 else SumUpTo(xs, n - 1) + xs[n - 1]
}

function Sum(xs: seq<int>): int
{
  SumUpTo(xs, |xs|)
} by method {
  var acc := 0;
  var i := 0;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant acc == SumUpTo(xs, i)
    decreases |xs| - i
  {
    acc := acc + xs[i];
    i := i + 1;
  }
  return acc;
}
```

**Pattern:** Choose a spec recursion direction that matches the loop.

---

## 13. Use two-state facts for heap changes

**Rule:** Use `twostate` when the proof compares current heap with `old` heap.

```dafny
twostate predicate SegmentUnchanged(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i :: lo <= i < hi ==> a[i] == old(a[i])
}
```

**Rule:** Use labels when the reference heap is not method entry.

```dafny
label BeforeUpdate:
a[k] := a[k] + 1;
assert old@BeforeUpdate(a[k]) + 1 == a[k];
```

---

## 14. Use types for repeated value constraints

**Rule:** Move common numeric constraints into subset types or newtypes.

```dafny
type Byte = b: int | 0 <= b < 256 witness 0

method WriteByte(b: Byte)
{
  assert 0 <= b < 256;
}
```

---

## 15. Do not hide proof gaps

**Rule:** Do not use unsound shortcuts as proof fixes.

```dafny
assume P;
{:axiom}
{:verify false}
```

**Boundary:** Maintainers own the declared external library contracts. For
coreutils, approved libc/gnulib functions are trusted, including parsing and
stdio internals where supplied. The utility proof covers upper-level behavior
under their contracts, including failures and observable effects. It does not
prove libc/gnulib correctness or require raw ABI, descriptor-state, or syscall
order witnesses. The [runtime interface](docs/core-api.md) identifies the
current boundary and legacy adapter limitations.
Contributions must not add assumptions, trust annotations, or verification skips
to discharge utility obligations. Diagnostic probes, when separately authorized,
must remain outside the submitted benchmark and cannot count as a successful
proof. Every submitted implementation and proof must be checked without them.

---

## 16. Debug by obligation type

| Failure | First edit |
|---|---|
| Precondition | Add caller-side `assert by` or strengthen caller invariant |
| Postcondition | Add exit assertion or strengthen invariant |
| Invariant init | Weaken invariant or initialize ghost state |
| Invariant preservation | Add processed/unprocessed facts or lemma |
| Termination | Add or change `decreases` |
| Quantifier | Bound variables, split formula, add trigger-shaped fact |
| Frame | Add `modifies`, shrink frame, or prove `unchanged` |

---

## 17. Generation order

1. Define ghost model.
2. Write contract and frame.
3. Implement body skeleton.
4. Add loop invariants and `decreases`.
5. Add helper lemmas.
6. Add `assert by`, `calc`, and `forall` blocks.
7. Check all required obligations without assumptions or verification skips.
8. Shrink frames and `reveal` scope.

For a benchmark, retain the direct `RunCore ==> Spec(...)` postcondition and
verify its included Core/Proof closure. State whether the result establishes
termination or only correctness on return; `decreases *` is not a termination
proof. Native extern contracts remain a separate trusted boundary.

---

## 18. Reject these outputs

```dafny
// Missing frame
method M(c: C) { c.x := 1; }

// Missing termination argument
while condition { ... }

// Unbounded quantifier
forall i :: a[i] >= 0

// Proof by assumption
assume false;

// Proof context pollution
reveal F(); reveal G(); reveal H();
```
