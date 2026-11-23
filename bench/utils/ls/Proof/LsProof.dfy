include "../../../core/World.dfy"
include "../Spec/LsSchema.dfy"
include "../Spec/LsSpec.dfy"
include "../Impl/LsCore.dfy"

module LsProof {
  import StreamWorld = BenchWorld
  import StreamContract = IOContract

  import Result = Results
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = LsSchema
  import Spec = LsSpec
  import Core = LsCore
  import Native = LsNativeSpec
  import NativeIO = LsNativeCore

  lemma UnneededDirectoryStatusIsRejected(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, path: BenchWorld.Path,
    observation: Spec.EntryObservation
  )
    requires observation.source.StatusEntryEvidence?
    requires !Spec.EntryStatusRequiredSpec(
               cmd, Spec.ClassifiedDirentKindSpec(observation.entryKind), observation.displayName)
    ensures !Spec.DirectorySourceRelation(cmd, fs, path, observation)
  {
  }

  lemma MismatchedDirectoryKindEvidenceIsRejected(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, path: BenchWorld.Path,
    observation: Spec.EntryObservation
  )
    requires
      (observation.source.DirentEntryEvidence? &&
       observation.source.kind != Spec.ClassifiedDirentKindSpec(observation.entryKind)) ||
      (observation.source.ImpliedDotEntryEvidence? &&
       observation.entryKind != BenchWorld.DirectoryDirentKind)
    ensures !Spec.DirectorySourceRelation(cmd, fs, path, observation)
  {
  }

  lemma NamesOnlyDirectoryConsumesNoEntryStatuses(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, path: BenchWorld.Path,
    firstStatus: nat, afterStatus: nat, complete: bool,
    observations: seq<Spec.EntryObservation>, expected: set<BenchWorld.DirEntry>
  )
    requires !Spec.EntryRenderSortMetadataRequiredSpec(cmd) && !cmd.recursive
    requires Spec.DirectoryObservationRelation(
               cmd,fs,path,firstStatus,afterStatus,complete,observations,expected)
    ensures afterStatus == firstStatus
  {
    var cuts: seq<nat> :|
      |cuts| == |observations| + 1 && cuts[0] == firstStatus &&
      cuts[|observations|] == afterStatus &&
      (forall i: nat | i < |observations| ::
         observations[i].statusOrdinal == cuts[i] &&
         cuts[i + 1] == cuts[i] + Spec.EntryStatusCallCount(observations[i]));
    forall i: nat | i < |observations|
      ensures cuts[i + 1] == cuts[i]
    {
      assert Spec.DirectorySourceRelation(cmd, fs, path, observations[i]);
      assert !observations[i].source.StatusEntryEvidence?;
    }
    var i := 0;
    while i < |observations|
      invariant i <= |observations|
      invariant cuts[i] == firstStatus
      decreases |observations| - i
    {
      i := i + 1;
    }
  }

  lemma DirentRenderingIgnoresStatus(
    cmd: Schema.LsCmd,
    kind: Spec.DirentKindEvidence,
    name: string,
    first: BenchWorld.FileStatus,
    second: BenchWorld.FileStatus
  )
    requires !Spec.EntryStatusRequiredSpec(cmd, kind, name)
    ensures Spec.RenderEntrySpec(cmd, name, first) ==
            Spec.RenderEntrySpec(cmd, name, second)
    ensures Spec.TotalLineSpec(cmd, []) == []
  {
    assert !Spec.EntryRenderSortMetadataRequiredSpec(cmd);
    assert !cmd.numericLong && !cmd.showBlocks;
  }

  lemma DirentSortingIgnoresStatus(
    cmd: Schema.LsCmd,
    kind: Spec.DirentKindEvidence,
    name: string,
    left: Spec.EntryObservation,
    right: Spec.EntryObservation
  )
    requires !Spec.EntryStatusRequiredSpec(cmd, kind, name)
    requires left.ok && right.ok
    ensures Spec.BaseEntryBeforeSpec(cmd, left, right) ==
            Spec.StringLessSpec(left.displayName, right.displayName)
  {
    assert cmd.sortMode == Schema.SortName;
    reveal Spec.BaseEntryBeforeSpec();
  }

  lemma StringLessIrreflexive(value: string)
    ensures !Spec.StringLessSpec(value, value)
    decreases |value|
  {
    reveal Spec.StringLessSpec();
    if |value| != 0 {
      StringLessIrreflexive(value[1..]);
    }
  }

  lemma StringLessAsymmetric(left: string, right: string)
    requires Spec.StringLessSpec(left, right)
    ensures !Spec.StringLessSpec(right, left)
    decreases |left|
  {
    reveal Spec.StringLessSpec();
    if |left| != 0 && |right| != 0 && left[0] == right[0] {
      StringLessAsymmetric(left[1..], right[1..]);
    }
  }

  lemma StringLessTransitive(left: string, middle: string, right: string)
    requires Spec.StringLessSpec(left, middle)
    requires Spec.StringLessSpec(middle, right)
    ensures Spec.StringLessSpec(left, right)
    decreases |left|
  {
    reveal Spec.StringLessSpec();
    if |left| != 0 && |middle| != 0 && |right| != 0 &&
       left[0] == middle[0] && middle[0] == right[0] {
      StringLessTransitive(left[1..], middle[1..], right[1..]);
    }
  }

  lemma EntryBeforeAsymmetric(
    cmd: Schema.LsCmd, left: Spec.EntryObservation, right: Spec.EntryObservation
  )
    requires Spec.EntryBeforeSpec(cmd, left, right)
    ensures !Spec.EntryBeforeSpec(cmd, right, left)
  {
    reveal Spec.EntryBeforeSpec();
    reveal Spec.BaseEntryBeforeSpec();
    StringLessIrreflexive(left.displayName);
    StringLessIrreflexive(right.displayName);
    if Spec.StringLessSpec(left.displayName, right.displayName) {
      StringLessAsymmetric(left.displayName, right.displayName);
    }
    if Spec.StringLessSpec(right.displayName, left.displayName) {
      StringLessAsymmetric(right.displayName, left.displayName);
    }
  }

  lemma EntryBeforeTransitive(
    cmd: Schema.LsCmd,
    left: Spec.EntryObservation,
    middle: Spec.EntryObservation,
    right: Spec.EntryObservation
  )
    requires Spec.EntryBeforeSpec(cmd, left, middle)
    requires Spec.EntryBeforeSpec(cmd, middle, right)
    ensures Spec.EntryBeforeSpec(cmd, left, right)
  {
    reveal Spec.EntryBeforeSpec();
    reveal Spec.BaseEntryBeforeSpec();
    if Spec.StringLessSpec(left.displayName, middle.displayName) &&
       Spec.StringLessSpec(middle.displayName, right.displayName) {
      StringLessTransitive(left.displayName, middle.displayName, right.displayName);
    }
    if Spec.StringLessSpec(right.displayName, middle.displayName) &&
       Spec.StringLessSpec(middle.displayName, left.displayName) {
      StringLessTransitive(right.displayName, middle.displayName, left.displayName);
    }
  }

  lemma InsertSortedPreservesMultiset(
    cmd: Schema.LsCmd,
    entry: Spec.EntryObservation,
    sorted: seq<Spec.EntryObservation>
  )
    ensures multiset(Core.InsertSortedCore(cmd, entry, sorted)) ==
            multiset(sorted) + multiset{entry}
    decreases |sorted|
  {
    reveal Core.InsertSortedCore();
    if |sorted| > 0 {
      if !Spec.EntryBeforeSpec(cmd, entry, sorted[0]) {
        InsertSortedPreservesMultiset(cmd, entry, sorted[1..]);
        assert sorted == [sorted[0]] + sorted[1..];
        assert Core.InsertSortedCore(cmd, entry, sorted) ==
               [sorted[0]] + Core.InsertSortedCore(cmd, entry, sorted[1..]);
      }
    }
  }

  lemma InsertedNoBeforeHead(
    cmd: Schema.LsCmd,
    head: Spec.EntryObservation,
    entry: Spec.EntryObservation,
    sorted: seq<Spec.EntryObservation>
  )
    requires !Spec.EntryBeforeSpec(cmd, entry, head)
    requires forall k: nat :: k < |sorted| ==>
                                !Spec.EntryBeforeSpec(cmd, sorted[k], head)
    ensures forall j: nat :: j < |Core.InsertSortedCore(cmd, entry, sorted)| ==>
                               !Spec.EntryBeforeSpec(
                                 cmd, Core.InsertSortedCore(cmd, entry, sorted)[j], head)
  {
    InsertSortedPreservesMultiset(cmd, entry, sorted);
    forall j: nat | j < |Core.InsertSortedCore(cmd, entry, sorted)|
      ensures !Spec.EntryBeforeSpec(
                cmd, Core.InsertSortedCore(cmd, entry, sorted)[j], head)
    {
      var candidate := Core.InsertSortedCore(cmd, entry, sorted)[j];
      if candidate != entry {
        assert candidate in multiset(Core.InsertSortedCore(cmd, entry, sorted));
        assert candidate in multiset(sorted) + multiset{entry};
        assert candidate !in multiset{entry};
        assert candidate in multiset(sorted);
        assert exists k: nat :: k < |sorted| && sorted[k] == candidate;
        var k: nat :| k < |sorted| && sorted[k] == candidate;
      }
    }
  }

  lemma InsertSortedPreservesOrder(
    cmd: Schema.LsCmd,
    entry: Spec.EntryObservation,
    sorted: seq<Spec.EntryObservation>
  )
    requires Spec.EntriesOrderedRelation(cmd, sorted)
    ensures Spec.EntriesOrderedRelation(
              cmd, Core.InsertSortedCore(cmd, entry, sorted))
    decreases |sorted|
  {
    reveal Core.InsertSortedCore();
    reveal Spec.EntriesOrderedRelation();
    if |sorted| > 0 {
      if Spec.EntryBeforeSpec(cmd, entry, sorted[0]) {
        EntryBeforeAsymmetric(cmd, entry, sorted[0]);
        forall j: nat | j < |sorted|
          ensures !Spec.EntryBeforeSpec(cmd, sorted[j], entry)
        {
          if j > 0 && Spec.EntryBeforeSpec(cmd, sorted[j], entry) {
            EntryBeforeTransitive(cmd, sorted[j], entry, sorted[0]);
          }
        }
      } else {
        assert Spec.EntriesOrderedRelation(cmd, sorted[1..]);
        InsertSortedPreservesOrder(cmd, entry, sorted[1..]);
        InsertedNoBeforeHead(cmd, sorted[0], entry, sorted[1..]);
        var insertedTail := Core.InsertSortedCore(cmd, entry, sorted[1..]);
        assert Core.InsertSortedCore(cmd, entry, sorted) == [sorted[0]] + insertedTail;
        forall i: nat, j: nat | i < j < |[sorted[0]] + insertedTail|
          ensures !Spec.EntryBeforeSpec(
                    cmd, ([sorted[0]] + insertedTail)[j], ([sorted[0]] + insertedTail)[i])
        {
          if i == 0 {
            assert ([sorted[0]] + insertedTail)[i] == sorted[0];
            assert ([sorted[0]] + insertedTail)[j] == insertedTail[j - 1];
          } else {
            assert ([sorted[0]] + insertedTail)[i] == insertedTail[i - 1];
            assert ([sorted[0]] + insertedTail)[j] == insertedTail[j - 1];
          }
        }
      }
    }
  }

  lemma SortEntriesCoreSatisfiesRelation(
    cmd: Schema.LsCmd,
    entries: seq<Spec.EntryObservation>
  )
    ensures Spec.EntrySortingRelation(cmd, entries, Core.SortEntriesCore(cmd, entries))
    decreases |entries|
  {
    reveal Core.SortEntriesCore();
    reveal Spec.EntrySortingRelation();
    if |entries| > 0 {
      SortEntriesCoreSatisfiesRelation(cmd, entries[1..]);
      InsertSortedPreservesMultiset(
        cmd, entries[0], Core.SortEntriesCore(cmd, entries[1..]));
      InsertSortedPreservesOrder(
        cmd, entries[0], Core.SortEntriesCore(cmd, entries[1..]));
      assert entries == [entries[0]] + entries[1..];
    }
  }

  lemma OperandBeforeAsymmetric(
    cmd: Schema.LsCmd,
    left: Spec.OperandObservation,
    right: Spec.OperandObservation
  )
    requires Spec.OperandBeforeSpec(cmd, left, right)
    ensures !Spec.OperandBeforeSpec(cmd, right, left)
  {
    reveal Spec.OperandBeforeSpec();
    if left.operandClass == right.operandClass {
      EntryBeforeAsymmetric(cmd, Spec.OperandAsEntry(left), Spec.OperandAsEntry(right));
    }
  }

  lemma OperandBeforeTransitive(
    cmd: Schema.LsCmd,
    left: Spec.OperandObservation,
    middle: Spec.OperandObservation,
    right: Spec.OperandObservation
  )
    requires Spec.OperandBeforeSpec(cmd, left, middle)
    requires Spec.OperandBeforeSpec(cmd, middle, right)
    ensures Spec.OperandBeforeSpec(cmd, left, right)
  {
    reveal Spec.OperandBeforeSpec();
    if left.operandClass == middle.operandClass &&
       middle.operandClass == right.operandClass {
      EntryBeforeTransitive(
        cmd, Spec.OperandAsEntry(left), Spec.OperandAsEntry(middle),
        Spec.OperandAsEntry(right));
    }
  }

  lemma InsertOperandPreservesMultiset(
    cmd: Schema.LsCmd,
    observation: Spec.OperandObservation,
    sorted: seq<Spec.OperandObservation>
  )
    ensures multiset(Core.InsertOperandSortedCore(cmd, observation, sorted)) ==
            multiset(sorted) + multiset{observation}
    decreases |sorted|
  {
    reveal Core.InsertOperandSortedCore();
    if |sorted| > 0 {
      if !Spec.OperandBeforeSpec(cmd, observation, sorted[0]) {
        InsertOperandPreservesMultiset(cmd, observation, sorted[1..]);
        assert sorted == [sorted[0]] + sorted[1..];
      }
    }
  }

  lemma InsertedOperandNoBeforeHead(
    cmd: Schema.LsCmd,
    head: Spec.OperandObservation,
    observation: Spec.OperandObservation,
    sorted: seq<Spec.OperandObservation>
  )
    requires !Spec.OperandBeforeSpec(cmd, observation, head)
    requires forall k: nat :: k < |sorted| ==>
                                !Spec.OperandBeforeSpec(cmd, sorted[k], head)
    ensures forall j: nat ::
              j < |Core.InsertOperandSortedCore(cmd, observation, sorted)| ==>
                !Spec.OperandBeforeSpec(
                  cmd, Core.InsertOperandSortedCore(cmd, observation, sorted)[j], head)
  {
    InsertOperandPreservesMultiset(cmd, observation, sorted);
    forall j: nat | j < |Core.InsertOperandSortedCore(cmd, observation, sorted)|
      ensures !Spec.OperandBeforeSpec(
                cmd, Core.InsertOperandSortedCore(cmd, observation, sorted)[j], head)
    {
      var candidate := Core.InsertOperandSortedCore(cmd, observation, sorted)[j];
      if candidate != observation {
        assert candidate in multiset(Core.InsertOperandSortedCore(
                              cmd, observation, sorted));
        assert candidate in multiset(sorted) + multiset{observation};
        assert candidate !in multiset{observation};
        assert candidate in multiset(sorted);
        assert exists k: nat :: k < |sorted| && sorted[k] == candidate;
      }
    }
  }

  lemma InsertOperandPreservesOrder(
    cmd: Schema.LsCmd,
    observation: Spec.OperandObservation,
    sorted: seq<Spec.OperandObservation>
  )
    requires Spec.OperandObservationsOrdered(cmd, sorted)
    ensures Spec.OperandObservationsOrdered(
              cmd, Core.InsertOperandSortedCore(cmd, observation, sorted))
    decreases |sorted|
  {
    reveal Core.InsertOperandSortedCore();
    reveal Spec.OperandObservationsOrdered();
    if |sorted| > 0 {
      if Spec.OperandBeforeSpec(cmd, observation, sorted[0]) {
        OperandBeforeAsymmetric(cmd, observation, sorted[0]);
        forall j: nat | j < |sorted|
          ensures !Spec.OperandBeforeSpec(cmd, sorted[j], observation)
        {
          if j > 0 && Spec.OperandBeforeSpec(cmd, sorted[j], observation) {
            OperandBeforeTransitive(cmd, sorted[j], observation, sorted[0]);
          }
        }
      } else {
        assert Spec.OperandObservationsOrdered(cmd, sorted[1..]);
        InsertOperandPreservesOrder(cmd, observation, sorted[1..]);
        InsertedOperandNoBeforeHead(cmd, sorted[0], observation, sorted[1..]);
        var insertedTail := Core.InsertOperandSortedCore(
          cmd, observation, sorted[1..]);
        forall i: nat, j: nat | i < j < |[sorted[0]] + insertedTail|
          ensures !Spec.OperandBeforeSpec(
                    cmd, ([sorted[0]] + insertedTail)[j],
                    ([sorted[0]] + insertedTail)[i])
        {
          if i == 0 {
            assert ([sorted[0]] + insertedTail)[j] == insertedTail[j - 1];
          }
        }
      }
    }
  }

  lemma SortOperandsCoreSatisfiesRelation(
    cmd: Schema.LsCmd,
    observations: seq<Spec.OperandObservation>
  )
    ensures Spec.OperandSortingRelation(
              cmd, observations, Core.SortOperandsCore(cmd, observations))
    decreases |observations|
  {
    reveal Core.SortOperandsCore();
    reveal Spec.OperandSortingRelation();
    if |observations| > 0 {
      SortOperandsCoreSatisfiesRelation(cmd, observations[1..]);
      InsertOperandPreservesMultiset(
        cmd, observations[0], Core.SortOperandsCore(cmd, observations[1..]));
      InsertOperandPreservesOrder(
        cmd, observations[0], Core.SortOperandsCore(cmd, observations[1..]));
      assert observations == [observations[0]] + observations[1..];
    }
  }

  lemma {:fuel Core.DirectPositionsCore, 0, 0} DirectPositionsCoreSuffix(
    sorted: seq<Spec.OperandObservation>, i: nat
  )
    requires i <= |sorted|
    ensures forall k: nat :: k < |Core.DirectPositionsCore(sorted, i)| ==>
                               i <= Core.DirectPositionsCore(sorted, i)[k] < |sorted|
    ensures forall k: nat :: k + 1 < |Core.DirectPositionsCore(sorted, i)| ==>
                               Core.DirectPositionsCore(sorted, i)[k] <
                               Core.DirectPositionsCore(sorted, i)[k + 1]
    ensures forall j: nat :: i <= j < |sorted| ==>
                               (sorted[j].operandClass == Spec.DirectOperand <==>
                                exists k: nat :: k < |Core.DirectPositionsCore(sorted, i)| &&
                                                 Core.DirectPositionsCore(sorted, i)[k] == j)
    decreases |sorted| - i
  {
    if i < |sorted| {
      DirectPositionsCoreSuffix(sorted, i + 1);
      var tail := Core.DirectPositionsCore(sorted, i + 1);
      assert {:fuel Core.DirectPositionsCore, 1, 2} Core.DirectPositionsCore(sorted, i) ==
                                                    (if sorted[i].operandClass == Spec.DirectOperand then [i] else []) + tail;
      forall j: nat | i <= j < |sorted|
        ensures (sorted[j].operandClass == Spec.DirectOperand <==>
                 exists k: nat :: k < |Core.DirectPositionsCore(sorted, i)| &&
                                  Core.DirectPositionsCore(sorted, i)[k] == j)
      {
        if sorted[i].operandClass == Spec.DirectOperand {
          assert Core.DirectPositionsCore(sorted, i) == [i] + tail;
          if j == i {
            assert Core.DirectPositionsCore(sorted, i)[0] == j;
            assert exists k: nat ::
                k < |Core.DirectPositionsCore(sorted, i)| &&
                Core.DirectPositionsCore(sorted, i)[k] == j;
          } else {
            assert i + 1 <= j;
            assert (sorted[j].operandClass == Spec.DirectOperand <==>
                    exists k: nat :: k < |tail| && tail[k] == j);
            if sorted[j].operandClass == Spec.DirectOperand {
              var k: nat :| k < |tail| && tail[k] == j;
              assert Core.DirectPositionsCore(sorted, i)[k + 1] == j;
            }
          }
          if exists k: nat :: k < |Core.DirectPositionsCore(sorted, i)| &&
                              Core.DirectPositionsCore(sorted, i)[k] == j {
            var k: nat :| k < |Core.DirectPositionsCore(sorted, i)| &&
                          Core.DirectPositionsCore(sorted, i)[k] == j;
            if k == 0 {
              assert j == i;
            } else {
              assert tail[k - 1] == j;
            }
          }
        } else {
          assert Core.DirectPositionsCore(sorted, i) == tail;
          if j == i {
            assert !(exists k: nat :: k < |tail| && tail[k] == j);
          } else {
            assert i + 1 <= j;
            assert (sorted[j].operandClass == Spec.DirectOperand <==>
                    exists k: nat :: k < |tail| && tail[k] == j);
          }
        }
      }
    } else {
      assert {:fuel Core.DirectPositionsCore, 1, 2} Core.DirectPositionsCore(sorted, i) == [];
    }
  }

  lemma {:fuel Core.DirectoryPositionsCore, 0, 0} DirectoryPositionsCoreSuffix(
    sorted: seq<Spec.OperandObservation>, i: nat
  )
    requires i <= |sorted|
    ensures forall k: nat :: k < |Core.DirectoryPositionsCore(sorted, i)| ==>
                               i <= Core.DirectoryPositionsCore(sorted, i)[k] < |sorted|
    ensures forall k: nat :: k + 1 < |Core.DirectoryPositionsCore(sorted, i)| ==>
                               Core.DirectoryPositionsCore(sorted, i)[k] <
                               Core.DirectoryPositionsCore(sorted, i)[k + 1]
    ensures forall j: nat :: i <= j < |sorted| ==>
                               ((sorted[j].operandClass == Spec.ExpandedDirectory &&
                                 sorted[j].sectionAvailable) <==>
                                exists k: nat :: k < |Core.DirectoryPositionsCore(sorted, i)| &&
                                                 Core.DirectoryPositionsCore(sorted, i)[k] == j)
    decreases |sorted| - i
  {
    if i < |sorted| {
      DirectoryPositionsCoreSuffix(sorted, i + 1);
      var tail := Core.DirectoryPositionsCore(sorted, i + 1);
      assert {:fuel Core.DirectoryPositionsCore, 1, 2} Core.DirectoryPositionsCore(sorted, i) ==
                                                       (if sorted[i].operandClass == Spec.ExpandedDirectory && sorted[i].sectionAvailable then [i] else []) + tail;
      forall j: nat | i <= j < |sorted|
        ensures ((sorted[j].operandClass == Spec.ExpandedDirectory &&
                  sorted[j].sectionAvailable) <==>
                 exists k: nat :: k < |Core.DirectoryPositionsCore(sorted, i)| &&
                                  Core.DirectoryPositionsCore(sorted, i)[k] == j)
      {
        if sorted[i].operandClass == Spec.ExpandedDirectory &&
           sorted[i].sectionAvailable {
          assert Core.DirectoryPositionsCore(sorted, i) == [i] + tail;
          if j == i {
            assert Core.DirectoryPositionsCore(sorted, i)[0] == j;
          } else if sorted[j].operandClass == Spec.ExpandedDirectory &&
                    sorted[j].sectionAvailable {
            var k: nat :| k < |tail| && tail[k] == j;
            assert Core.DirectoryPositionsCore(sorted, i)[k + 1] == j;
          }
          if exists k: nat :: k < |Core.DirectoryPositionsCore(sorted, i)| &&
                              Core.DirectoryPositionsCore(sorted, i)[k] == j {
            var k: nat :| k < |Core.DirectoryPositionsCore(sorted, i)| &&
                          Core.DirectoryPositionsCore(sorted, i)[k] == j;
            if k == 0 {
              assert j == i;
            } else {
              assert tail[k - 1] == j;
            }
          }
        } else {
          assert Core.DirectoryPositionsCore(sorted, i) == tail;
          if j == i {
            assert !(exists k: nat :: k < |tail| && tail[k] == j);
          }
        }
      }
    } else {
      assert {:fuel Core.DirectoryPositionsCore, 1, 2} Core.DirectoryPositionsCore(sorted, i) == [];
    }
  }

  lemma BodiesAtPositionsConcatenate(
    cmd: Schema.LsCmd, sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ) returns (cuts: seq<nat>)
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    ensures Spec.FragmentsConcatenate(
              Core.BodiesFragmentsPrefixCore(cmd, sorted, positions, processed),
              Core.BodiesAtPositionsPrefixCore(cmd, sorted, positions, processed), cuts)
    decreases processed
  {
    hide Core.RenderOperandCore();
    if processed == 0 {
      cuts := [0];
    } else {
      cuts := BodiesAtPositionsConcatenate(cmd, sorted, positions, processed - 1);
      var fragments := Core.BodiesFragmentsPrefixCore(
        cmd, sorted, positions, processed - 1);
      var combined := Core.BodiesAtPositionsPrefixCore(
        cmd, sorted, positions, processed - 1);
      Core.AppendFragment(
        fragments, combined, cuts, Core.RenderOperandCore(cmd, sorted, positions[processed - 1]));
      cuts := cuts + [|Core.BodiesAtPositionsPrefixCore(
                        cmd, sorted, positions, processed)|];
      assert Core.BodiesFragmentsPrefixCore(cmd, sorted, positions, processed) ==
             fragments + [Core.RenderOperandCore(cmd, sorted, positions[processed - 1])];
    }
  }

  lemma DirectoryGroupsCoreShape(
    sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  )
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    ensures |Core.DirectoryGroupsPrefixCore(sorted, positions, processed)| == processed
    ensures forall k: nat :: k < processed ==>
                               Core.DirectoryGroupsPrefixCore(sorted, positions, processed)[k] ==
                               Spec.OutputGroup(
                                 [sorted[positions[k]].index], sorted[positions[k]].body, true)
    decreases processed
  {
    if processed > 0 {
      DirectoryGroupsCoreShape(sorted, positions, processed - 1);
    }
  }

  lemma {:vcs_split_on_every_assert} OutputGroupsCoreSatisfiesRelation(
    cmd: Schema.LsCmd, sorted: seq<Spec.OperandObservation>
  )
    ensures Spec.OutputGroupsRelation(cmd, sorted, Core.OutputGroupsCore(cmd, sorted))
  {
    var directPositions := Core.DirectPositionsCore(sorted, 0);
    var directoryPositions := Core.DirectoryPositionsCore(sorted, 0);
    DirectPositionsCoreSuffix(sorted, 0);
    DirectoryPositionsCoreSuffix(sorted, 0);
    assert Spec.DirectPositionRelation(sorted, directPositions);
    assert Spec.DirectoryPositionRelation(sorted, directoryPositions);
    var directFragments := Core.BodiesFragmentsPrefixCore(
      cmd, sorted, directPositions, |directPositions|);
    var directIndices := Core.OperandIndicesPrefixCore(
      sorted, directPositions, |directPositions|);
    var directBody := Core.BodiesAtPositionsCore(cmd, sorted, directPositions);
    var directCuts := BodiesAtPositionsConcatenate(
      cmd, sorted, directPositions, |directPositions|);
    DirectoryGroupsCoreShape(
      sorted, directoryPositions, |directoryPositions|);
    assert directFragments == seq(|directPositions|, k requires 0 <= k < |directPositions| =>
      Spec.RenderOperandSpec(cmd, sorted, directPositions[k])) by {
      forall k: nat | k < |directPositions|
        ensures directFragments[k] == Spec.RenderOperandSpec(cmd, sorted, directPositions[k])
      {
      }
    }
    assert directIndices == seq(|directPositions|, k requires 0 <= k < |directPositions| =>
      sorted[directPositions[k]].index);
    assert Core.DirectoryGroupsCore(sorted, directoryPositions) ==
      seq(|directoryPositions|, k requires 0 <= k < |directoryPositions| =>
        Spec.OutputGroup([sorted[directoryPositions[k]].index], sorted[directoryPositions[k]].body, true));
    reveal Spec.OutputGroupsRelation();
  }

  lemma JoinOutputGroupsConcatenate(
    groups: seq<Spec.OutputGroup>, processed: nat
  ) returns (cuts: seq<nat>)
    requires processed <= |groups|
    ensures Spec.FragmentsConcatenate(
              Core.GroupFragmentsPrefixCore(groups, processed),
              Core.JoinOutputGroupsPrefixCore(groups, processed), cuts)
    decreases processed
  {
    if processed == 0 {
      cuts := [0];
    } else {
      cuts := JoinOutputGroupsConcatenate(groups, processed - 1);
      var fragments := Core.GroupFragmentsPrefixCore(groups, processed - 1);
      var tail := (if processed == 1 then [] else "\n") +
      groups[processed - 1].body;
      Core.AppendFragment(
        fragments, Core.JoinOutputGroupsPrefixCore(groups, processed - 1),
        cuts, tail);
      assert Core.JoinOutputGroupsPrefixCore(groups, processed) ==
             Core.JoinOutputGroupsPrefixCore(groups, processed - 1) + tail;
      cuts := cuts + [|Core.JoinOutputGroupsPrefixCore(groups, processed)|];
      assert Core.GroupFragmentsPrefixCore(groups, processed) == fragments + [tail];
      reveal Spec.FragmentsConcatenate();
    }
  }

  lemma JoinOutputGroupsCoreSatisfiesRelation(groups: seq<Spec.OutputGroup>)
    ensures Spec.SeparatedGroupsRelation(
              groups, Core.JoinOutputGroupsCore(groups))
  {
    var cuts := JoinOutputGroupsConcatenate(groups, |groups|);
    assert Core.GroupFragmentsPrefixCore(groups, |groups|) ==
      seq(|groups|, i requires 0 <= i < |groups| =>
        (if i == 0 then [] else "\n") + groups[i].body);
    reveal Spec.SeparatedGroupsRelation();
  }

  lemma AccessErrorsConcatenate(
    observations: seq<Spec.OperandObservation>, processed: nat
  ) returns (cuts: seq<nat>)
    requires processed <= |observations|
    ensures Spec.FragmentsConcatenate(
              Core.AccessErrorFragmentsPrefixCore(observations, processed),
              Core.AccessErrorsPrefixCore(observations, processed), cuts)
    decreases processed
  {
    if processed == 0 {
      cuts := [0];
    } else {
      cuts := AccessErrorsConcatenate(observations, processed - 1);
      var fragments := Core.AccessErrorFragmentsPrefixCore(
        observations, processed - 1);
      Core.AppendFragment(
        fragments, Core.AccessErrorsPrefixCore(observations, processed - 1),
        cuts, observations[processed - 1].accessErrors);
      cuts := cuts + [|Core.AccessErrorsPrefixCore(observations, processed)|];
      assert Core.AccessErrorFragmentsPrefixCore(observations, processed) ==
             fragments + [observations[processed - 1].accessErrors];
    }
  }

  lemma SectionErrorsConcatenate(
    observations: seq<Spec.OperandObservation>, processed: nat
  ) returns (cuts: seq<nat>)
    requires processed <= |observations|
    ensures Spec.FragmentsConcatenate(
              Core.SectionErrorFragmentsPrefixCore(observations, processed),
              Core.SectionErrorsPrefixCore(observations, processed), cuts)
    decreases processed
  {
    if processed == 0 {
      cuts := [0];
    } else {
      cuts := SectionErrorsConcatenate(observations, processed - 1);
      var fragments := Core.SectionErrorFragmentsPrefixCore(
        observations, processed - 1);
      Core.AppendFragment(
        fragments, Core.SectionErrorsPrefixCore(observations, processed - 1),
        cuts, observations[processed - 1].sectionErrors);
      cuts := cuts + [|Core.SectionErrorsPrefixCore(observations, processed)|];
      assert Core.SectionErrorFragmentsPrefixCore(observations, processed) ==
             fragments + [observations[processed - 1].sectionErrors];
    }
  }

  lemma OperandErrorsCoreSatisfiesRelation(
    observations: seq<Spec.OperandObservation>, sorted: seq<Spec.OperandObservation>
  )
    ensures Spec.OperandErrorsRelation(
              observations, sorted,
              Core.AccessErrorsCore(observations) + Core.SectionErrorsCore(sorted))
  {
    var accessCuts := AccessErrorsConcatenate(observations, |observations|);
    var sectionCuts := SectionErrorsConcatenate(sorted, |sorted|);
    assert Core.AccessErrorFragmentsPrefixCore(observations, |observations|) ==
      seq(|observations|, i requires 0 <= i < |observations| => observations[i].accessErrors);
    assert Core.SectionErrorFragmentsPrefixCore(sorted, |sorted|) ==
      seq(|sorted|, i requires 0 <= i < |sorted| => sorted[i].sectionErrors);
    reveal Spec.OperandErrorsRelation();
  }

  lemma ObservationPiecesImpliesSpec(
    cmd: Schema.LsCmd,
    observations: seq<Spec.EntryObservation>,
    outputFragments: seq<BenchWorld.Bytes>
  )
    requires Core.ObservationPiecesSummary(
               cmd, observations, outputFragments)
    ensures Spec.ObservationPiecesRelation(
              cmd, observations, outputFragments)
  {
    forall i: nat | i < |observations|
      ensures outputFragments[i] ==
              (if observations[i].ok
               then Spec.RenderAlignedEntrySpec(cmd, observations[i].renderName, observations[i].status, Spec.ObservationWidthsSpec(cmd, observations))
               else Spec.RenderFailedEntrySpec(cmd, observations[i], Spec.ObservationWidthsSpec(cmd, observations)))
    {
      if observations[i].ok {
      }
    }
  }

  lemma DirectorySummaryImpliesSpec(
    cmd: Schema.LsCmd,
    displayPath: BenchWorld.Path,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    firstStatus: nat,
    afterStatus: nat,
    observations: seq<Spec.EntryObservation>,
    readErr: int,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool, nativeTrace: Spec.DirectoryTrace
  )
    requires Core.DirectoryListingSummary(
               cmd, displayPath, fs, path, firstStatus, afterStatus,
               observations, readErr, output, errors, hadError, nativeTrace)
    ensures Spec.DirectoryListingRelation(
              cmd, displayPath, fs, path, firstStatus, afterStatus,
              observations, readErr, output, errors, hadError, nativeTrace)
  {
    hide *;
    reveal Core.DirectoryListingSummary(), Spec.ReadCloseDirectoryTrace(), Spec.BoundOpenDirectoryTrace();
    var rawObservations: seq<Spec.EntryObservation>,
        outputFragments: seq<BenchWorld.Bytes>, outputCuts: seq<nat>,
        errorFragments: seq<BenchWorld.Bytes>, errorCuts: seq<nat>,
        entryOutput: BenchWorld.Bytes, entryErrors: BenchWorld.Bytes, closeErr: int,
        expectedEntries: set<BenchWorld.DirEntry> :|
      Spec.DirectoryCloseObservation(cmd, fs, path, readErr, closeErr) &&
      Spec.ReadCloseDirectoryTrace(cmd, fs, path, nativeTrace, readErr, closeErr) &&
      nativeTrace.raw == rawObservations && Spec.DirectoryExpectedEntries(nativeTrace,expectedEntries) &&
      Spec.DirectoryObservationRelation(cmd, fs, path, firstStatus, afterStatus,
                                        readErr == 0,rawObservations,expectedEntries) &&
      observations == Core.SortEntriesCore(cmd, rawObservations) &&
      Core.ObservationPiecesSummary(cmd, observations, outputFragments) &&
      Spec.ObservationErrorsRelation(displayPath, rawObservations, errorFragments) &&
      Spec.FragmentsConcatenate(outputFragments, entryOutput, outputCuts) &&
      output == Spec.TotalLineSpec(cmd, rawObservations) + entryOutput &&
      Spec.FragmentsConcatenate(errorFragments, entryErrors, errorCuts) &&
      errors == entryErrors +
      (if readErr == 0 then [] else Spec.ReadDirectoryErrorMessageSpec(displayPath, readErr)) +
      Spec.CloseDirectoryErrorMessageSpec(displayPath, closeErr) &&
      hadError == (readErr != 0 || closeErr != 0 ||
                   exists i: nat :: i < |observations| && Spec.ObservationFailedSpec(observations[i]));
    SortEntriesCoreSatisfiesRelation(cmd, rawObservations);
    ObservationPiecesImpliesSpec(cmd, observations, outputFragments);
    reveal Spec.DirectoryListingRelation();
  }

  lemma RecursiveOutputPrefixConcatenates(
    tree: Spec.RecursiveWitness, processed: nat
  ) returns (cuts: seq<nat>)
    requires processed <= |tree.observations|
    ensures Spec.FragmentsConcatenate(
              Spec.RecursiveOutputFragments(tree)[..processed],
              Core.RecursiveChildOutputPrefixCore(
                tree.observations, tree.children, processed), cuts)
    decreases processed
  {
    if processed == 0 {
      cuts := [0];
    } else {
      cuts := RecursiveOutputPrefixConcatenates(tree, processed - 1);
      var fragments := Spec.RecursiveOutputFragments(tree)[..processed - 1];
      var combined := Core.RecursiveChildOutputPrefixCore(
        tree.observations, tree.children, processed - 1);
      var piece := Spec.RecursiveOutputFragments(tree)[processed - 1];
      reveal Spec.RecursiveOutputFragments();
      reveal Core.RecursiveChildOutputPrefixCore();
      Core.AppendFragment(fragments, combined, cuts, piece);
      cuts := cuts + [|Core.RecursiveChildOutputPrefixCore(
                        tree.observations, tree.children, processed)|];
      assert Spec.RecursiveOutputFragments(tree)[..processed] == fragments + [piece];
    }
  }

  lemma RecursiveErrorPrefixConcatenates(
    displayPath: BenchWorld.Path, tree: Spec.RecursiveWitness, processed: nat
  ) returns (cuts: seq<nat>)
    requires processed <= |tree.observations|
    ensures Spec.FragmentsConcatenate(
              Spec.RecursiveErrorFragments(displayPath, tree)[..processed],
              Core.RecursiveChildErrorPrefixCore(
                displayPath, tree.observations, tree.children, tree.cycles, processed), cuts)
    decreases processed
  {
    if processed == 0 {
      cuts := [0];
    } else {
      cuts := RecursiveErrorPrefixConcatenates(displayPath, tree, processed - 1);
      var fragments := Spec.RecursiveErrorFragments(displayPath, tree)[..processed - 1];
      var combined := Core.RecursiveChildErrorPrefixCore(
        displayPath, tree.observations, tree.children, tree.cycles, processed - 1);
      var piece := Spec.RecursiveErrorFragments(displayPath, tree)[processed - 1];
      reveal Spec.RecursiveErrorFragments();
      reveal Core.RecursiveChildErrorPrefixCore();
      Core.AppendFragment(fragments, combined, cuts, piece);
      cuts := cuts + [|Core.RecursiveChildErrorPrefixCore(
                        displayPath, tree.observations, tree.children, tree.cycles, processed)|];
      assert Spec.RecursiveErrorFragments(displayPath, tree)[..processed] ==
             fragments + [piece];
    }
  }

  lemma {:isolate_assertions} RecursiveSummaryImpliesSpec(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    displayPath: BenchWorld.Path,
    accessPath: BenchWorld.Path,
    ancestors: set<BenchWorld.HostInodeKey>,
    tree: Spec.RecursiveWitness
  )
    requires Core.RecursiveDirectorySummary(
               cmd, fs, displayPath, accessPath, ancestors, tree)
    ensures Spec.RecursiveDirectoryRelation(
              cmd, fs, displayPath, accessPath, ancestors, tree)
    decreases tree
  {
    hide *;
    reveal Core.RecursiveDirectorySummary(cmd, fs, displayPath, accessPath, ancestors, tree);
    assert Spec.RecursiveNativeDirectoryTrace(cmd, fs, accessPath, tree) &&
           Spec.RecursiveNativeCallsFields(cmd,fs,tree) &&
           cmd.statusContext.BoundStatusObservations? &&
           Spec.OpenDirectoryObservation(cmd, fs, accessPath, tree.openOk, tree.openErr) &&
           (tree.openOk ==> Spec.OpenedDirectoryStatusObservation(
                cmd, fs, accessPath, tree.firstStatus, tree.statusOk,
                tree.openedStatus, tree.statusErr)) &&
           (if !tree.openOk then
              tree.openErr > 0 && !tree.statusOk && !tree.cycle &&
              tree.listingFirstStatus == tree.firstStatus &&
              tree.listingAfterStatus == tree.firstStatus &&
              tree.afterStatus == tree.firstStatus &&
              tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
              tree.output == [] &&
              tree.errors == Spec.OpenDirectoryErrorMessageSpec(displayPath, tree.openErr) &&
              tree.hadError
            else if !tree.statusOk then
              tree.openErr == 0 && tree.statusErr > 0 && !tree.cycle &&
              tree.listingFirstStatus == tree.firstStatus+1 &&
              tree.listingAfterStatus == tree.firstStatus+1 &&
              tree.afterStatus == tree.firstStatus+1 &&
              tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
              tree.output == [] &&
              tree.errors == Spec.DirectoryIdentityErrorMessageSpec(displayPath, tree.statusErr) &&
              tree.hadError
            else
              tree.openErr == 0 && tree.statusErr == 0 &&
              tree.listingFirstStatus == tree.firstStatus + 1 &&
              tree.openedStatus.kind == BenchWorld.DirectoryKind &&
              (if tree.cycle then
                 tree.openedStatus.hostKey in ancestors &&
                 tree.listingAfterStatus == tree.listingFirstStatus &&
                 tree.afterStatus == tree.listingFirstStatus &&
                 tree.observations == [] && tree.children == map[] && tree.cycles == {} &&
                 tree.output == [] && tree.errors == Spec.RecursiveCycleMessageSpec(displayPath) &&
                 tree.hadError
               else
                 tree.openedStatus.hostKey !in ancestors &&
                 Core.DirectoryListingSummary(
                   cmd, displayPath, fs, accessPath, tree.listingFirstStatus,
                   tree.listingAfterStatus,
                   tree.observations, tree.readErr,
                   tree.listingOutput, tree.listingErrors, tree.listingHadError, tree.nativeTrace) &&
                 (exists statusCuts: seq<nat> ::
                    |statusCuts| == |tree.observations| + 1 &&
                    statusCuts[0] == tree.listingAfterStatus &&
                    statusCuts[|tree.observations|] == tree.afterStatus &&
                    (forall i: nat | i < |tree.observations| ::
                       (if i in tree.children then
                          tree.children[i].firstStatus == statusCuts[i] &&
                          tree.children[i].afterStatus == statusCuts[i + 1]
                        else statusCuts[i] == statusCuts[i + 1]))) &&
                 tree.cycles <= tree.children.Keys &&
                 (forall i: nat :: i < |tree.observations| ==>
                                     (i in tree.children <==> Spec.RecursiveEntryEligible(tree.observations[i])) &&
                                     (i in tree.cycles <==> i in tree.children && tree.children[i].cycle)) &&
                 (forall i: nat :: i in tree.children ==>
                                     i < |tree.observations| &&
                                     Core.RecursiveDirectorySummary(
                                       cmd, fs,
                                       Spec.ChildDisplayPath(displayPath, tree.observations[i].displayName),
                                       tree.observations[i].accessPath,
                                       ancestors + {tree.openedStatus.hostKey}, tree.children[i])) &&
                 tree.output == Spec.DirectoryHeaderSpec(displayPath) + tree.listingOutput +
                 Core.RecursiveChildOutputPrefixCore(
                   tree.observations, tree.children, |tree.observations|) &&
                 tree.errors == tree.listingErrors + Core.RecursiveChildErrorPrefixCore(
                   displayPath, tree.observations, tree.children, tree.cycles,
                   |tree.observations|) &&
                 tree.hadError ==
                 (tree.listingHadError ||
                  exists i: nat :: i in tree.children && tree.children[i].hadError)));
    hide Core.RecursiveDirectorySummary();
    if !tree.openOk || !tree.statusOk || tree.cycle {
      assert Spec.RecursiveDirectoryRelation(
          cmd, fs, displayPath, accessPath, ancestors, tree) by {
        reveal Spec.RecursiveDirectoryRelation();
      }
      return;
    }
    DirectorySummaryImpliesSpec(
      cmd, displayPath, fs, accessPath, tree.listingFirstStatus,
      tree.listingAfterStatus,
      tree.observations, tree.readErr,
      tree.listingOutput, tree.listingErrors, tree.listingHadError, tree.nativeTrace);
    forall i: nat | i in tree.children
      ensures Spec.RecursiveDirectoryRelation(
                cmd, fs,
                Spec.ChildDisplayPath(displayPath, tree.observations[i].displayName),
                tree.observations[i].accessPath,
                ancestors + {tree.openedStatus.hostKey}, tree.children[i])
    {
      RecursiveSummaryImpliesSpec(
        cmd, fs,
        Spec.ChildDisplayPath(displayPath, tree.observations[i].displayName),
        tree.observations[i].accessPath,
        ancestors + {tree.openedStatus.hostKey}, tree.children[i]);
    }
    var outputCuts := RecursiveOutputPrefixConcatenates(
      tree, |tree.observations|);
    var errorCuts := RecursiveErrorPrefixConcatenates(
      displayPath, tree, |tree.observations|);
    assert |Spec.RecursiveOutputFragments(tree)| == |tree.observations| by {
      reveal Spec.RecursiveOutputFragments();
    }
    assert |Spec.RecursiveErrorFragments(displayPath, tree)| == |tree.observations| by {
      reveal Spec.RecursiveErrorFragments();
    }
    assert Spec.RecursiveOutputFragments(tree)[..|tree.observations|] ==
           Spec.RecursiveOutputFragments(tree);
    assert Spec.RecursiveErrorFragments(displayPath, tree)[..|tree.observations|] ==
           Spec.RecursiveErrorFragments(displayPath, tree);
    assert exists childOutput: BenchWorld.Bytes, childErrors: BenchWorld.Bytes,
        outputWitness: seq<nat>, errorWitness: seq<nat> ::
        Spec.FragmentsConcatenate(
          Spec.RecursiveOutputFragments(tree), childOutput, outputWitness) &&
        Spec.FragmentsConcatenate(
          Spec.RecursiveErrorFragments(displayPath, tree), childErrors, errorWitness) &&
        tree.output == Spec.DirectoryHeaderSpec(displayPath) + tree.listingOutput + childOutput &&
        tree.errors == tree.listingErrors + childErrors;
    assert Spec.RecursiveDirectoryRelation(
        cmd, fs, displayPath, accessPath, ancestors, tree) by {
      reveal Spec.RecursiveDirectoryRelation();
    }
  }

  lemma {:isolate_assertions} FlatOperandRelationWitness(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    observation: Spec.OperandObservation, entries: seq<Spec.EntryObservation>,
    readErr: int, listingOutput: BenchWorld.Bytes
  )
    requires Spec.OperandNativeFields(cmd,fs,observation)
    requires observation.index < |cmd.operands|
    requires observation.operand == cmd.operands[observation.index]
    requires observation.path == Spec.OperandPathSpec(cmd, cwd, observation.operand)
    requires Spec.OpenDirectoryObservation(cmd, fs, observation.path, true, 0)
    requires Spec.BoundOpenDirectoryTrace(cmd, fs, observation.path, observation.nativeTrace, true, 0)
    requires observation.nativeCalls == observation.statusCalls+observation.nativeTrace.nativeCalls
    requires Spec.ObservedOperandStatusResult(cmd,fs,observation) == Result.Ok(observation.status)
    requires observation.status.kind == BenchWorld.DirectoryKind
    requires !cmd.listDirectories && !cmd.recursive
    requires observation.ok && observation.err == 0 && observation.accessErrors == []
    requires observation.operandClass == Spec.ExpandedDirectory
    requires observation.sectionAvailable && !observation.hasCycle
    requires observation.directoryFailed == Spec.DirectoryOperationFailed(observation.nativeTrace, readErr)
    requires Spec.DirectoryListingRelation(
               cmd, observation.operand, fs, observation.path,
               observation.firstStatus + Spec.ObservedOperandStatusCallCount(cmd,fs,observation),
               observation.afterStatus, entries, readErr, listingOutput,
               observation.sectionErrors, observation.failed, observation.nativeTrace)
    requires observation.body ==
             (if |cmd.operands| > 1 then Spec.DirectoryHeaderSpec(observation.operand) else []) +
             listingOutput
    ensures Spec.OperandObservationRelation(cmd, fs, cwd, observation)
  {
    hide *;
    assert observation.nativeTrace.DirectoryTrace? by {
      reveal Spec.BoundOpenDirectoryTrace();
    }
    reveal Spec.OperandObservationRelation();
  }

  lemma {:vcs_split_on_every_assert} OperandObservationSummaryImpliesSpec(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    observation: Spec.OperandObservation
  )
    requires Core.OperandObservationSummary(cmd, fs, cwd, observation)
    ensures Spec.OperandObservationRelation(cmd, fs, cwd, observation)
  {
    hide *;
    reveal Core.OperandObservationSummary();
    match Spec.ObservedOperandStatusResult(cmd,fs,observation)
    case Err(_) =>
      assert Spec.OperandObservationRelation(cmd, fs, cwd, observation) by {
        reveal Spec.OperandObservationRelation();
      }
    case Ok(status) =>
      if status.kind == BenchWorld.DirectoryKind && !cmd.listDirectories {
        if observation.sectionAvailable {
          if cmd.recursive {
            var tree: Spec.RecursiveWitness :|
              Core.RecursiveDirectorySummary(
                cmd, fs, observation.operand, observation.path,
                {}, tree) &&
              tree.openOk && tree.nativeTrace == observation.nativeTrace &&
              observation.nativeCalls == observation.statusCalls+tree.nativeCalls &&
              tree.firstStatus == observation.firstStatus +
              Spec.ObservedOperandStatusCallCount(cmd,fs,observation) &&
              tree.afterStatus == observation.afterStatus &&
              observation.body == tree.output &&
              observation.sectionErrors == tree.errors &&
              observation.failed == tree.hadError &&
              observation.hasCycle == Spec.RecursiveHasCycle(tree) &&
              observation.directoryFailed == Spec.RecursiveRootFailed(tree);
            RecursiveSummaryImpliesSpec(
              cmd, fs, observation.operand, observation.path,
              {}, tree);
            assert exists candidateTree: Spec.RecursiveWitness ::
                Spec.RecursiveDirectoryRelation(
                  cmd, fs, observation.operand, observation.path,
                  {}, candidateTree) &&
                candidateTree.openOk && candidateTree.nativeTrace == observation.nativeTrace &&
                observation.nativeCalls == observation.statusCalls+candidateTree.nativeCalls &&
                candidateTree.firstStatus == observation.firstStatus +
                Spec.ObservedOperandStatusCallCount(cmd,fs,observation) &&
                candidateTree.afterStatus == observation.afterStatus &&
                observation.body == candidateTree.output &&
                observation.sectionErrors == candidateTree.errors &&
                observation.failed == candidateTree.hadError &&
                observation.hasCycle == Spec.RecursiveHasCycle(candidateTree) &&
                observation.directoryFailed == Spec.RecursiveRootFailed(candidateTree) by {
              assert Spec.RecursiveDirectoryRelation(
                  cmd, fs, observation.operand, observation.path,
            {}, tree);
            }
            assert Spec.OperandObservationRelation(cmd, fs, cwd, observation) by {
              reveal Spec.OperandObservationRelation();
            }
          } else {
            var entries: seq<Spec.EntryObservation>, readErr: int,
                listingOutput: BenchWorld.Bytes :|
              Core.DirectoryListingSummary(
                cmd, observation.operand, fs, observation.path,
                observation.firstStatus + Spec.ObservedOperandStatusCallCount(cmd,fs,observation),
                observation.afterStatus, entries, readErr,
                listingOutput, observation.sectionErrors, observation.failed, observation.nativeTrace) &&
              observation.directoryFailed == Spec.DirectoryOperationFailed(observation.nativeTrace, readErr) &&
              observation.body ==
              (if |cmd.operands| > 1
               then Spec.DirectoryHeaderSpec(observation.operand)
               else []) + listingOutput;
            DirectorySummaryImpliesSpec(
              cmd, observation.operand, fs, observation.path,
              observation.firstStatus + Spec.ObservedOperandStatusCallCount(cmd,fs,observation),
              observation.afterStatus, entries, readErr,
              listingOutput, observation.sectionErrors, observation.failed, observation.nativeTrace);
            assert exists witnessEntries: seq<Spec.EntryObservation>,
                witnessErr: int, witnessOutput: BenchWorld.Bytes
                {:trigger Spec.DirectoryListingRelation(
                  cmd, observation.operand, fs, observation.path,
                  observation.firstStatus + Spec.ObservedOperandStatusCallCount(cmd,fs,observation),
                  observation.afterStatus, witnessEntries, witnessErr,
                  witnessOutput, observation.sectionErrors, observation.failed, observation.nativeTrace)} ::
                Spec.DirectoryListingRelation(
                  cmd, observation.operand, fs, observation.path,
                  observation.firstStatus + Spec.ObservedOperandStatusCallCount(cmd,fs,observation),
                  observation.afterStatus, witnessEntries, witnessErr,
                  witnessOutput, observation.sectionErrors, observation.failed, observation.nativeTrace) &&
                observation.directoryFailed == Spec.DirectoryOperationFailed(observation.nativeTrace, witnessErr) &&
                observation.body ==
                (if |cmd.operands| > 1
                 then Spec.DirectoryHeaderSpec(observation.operand)
                 else []) + witnessOutput by {
              assert Spec.DirectoryListingRelation(
                  cmd, observation.operand, fs, observation.path,
                  observation.firstStatus + Spec.ObservedOperandStatusCallCount(cmd,fs,observation),
                  observation.afterStatus, entries, readErr,
                  listingOutput, observation.sectionErrors, observation.failed, observation.nativeTrace);
            }
            FlatOperandRelationWitness(
              cmd, fs, cwd, observation, entries, readErr, listingOutput);
          }
        } else {
          assert Spec.OperandObservationRelation(cmd, fs, cwd, observation) by {
            reveal Spec.OperandObservationRelation();
          }
        }
      } else {
        assert Spec.OperandObservationRelation(cmd, fs, cwd, observation) by {
          reveal Spec.OperandObservationRelation();
        }
      }
  }

  lemma RunWitnessImpliesRelation(
    cmd: Schema.LsCmd, fs: BenchWorld.FileSystem, cwd: BenchWorld.Path,
    firstStatus: nat, afterStatus: nat,
    output: BenchWorld.Bytes, errors: BenchWorld.Bytes, exit: int,
    observations: seq<Spec.OperandObservation>,
    sorted: seq<Spec.OperandObservation>, groups: seq<Spec.OutputGroup>,
    statusCuts: seq<nat>, afterNative: seq<Native.State>
  )
    requires Spec.RunNativeFields(cmd,fs,firstStatus,afterStatus,observations,afterNative)
    requires |observations| == |cmd.operands|
    requires |statusCuts| == |observations| + 1
    requires statusCuts[0] == firstStatus
    requires statusCuts[|observations|] == afterStatus
    requires forall i: nat | i < |observations| ::
               observations[i].firstStatus == statusCuts[i] &&
               observations[i].afterStatus == statusCuts[i + 1]
    requires forall i: nat | i < |observations| ::
               observations[i].index == i &&
               Spec.OperandObservationRelation(cmd, fs, cwd, observations[i])
    requires Spec.OperandSortingRelation(cmd, observations, sorted)
    requires Spec.OutputGroupsRelation(cmd, sorted, groups)
    requires Spec.SeparatedGroupsRelation(groups, output)
    requires Spec.OperandErrorsRelation(observations, sorted, errors)
    requires exit == Spec.OperandExitSpec(observations)
    ensures Spec.RunRelation(cmd, fs, cwd, firstStatus, afterStatus,
                             output,errors,exit,afterNative)
  {
    assert Spec.OperandStatusIntervals(observations, firstStatus, afterStatus) by {
      reveal Spec.OperandStatusIntervals();
      if |observations| != 0 {
        assert observations[0].firstStatus == statusCuts[0];
        assert observations[|observations| - 1].afterStatus == statusCuts[|observations|];
        forall i: nat | i + 1 < |observations|
          ensures observations[i].afterStatus == observations[i + 1].firstStatus
        {
          assert observations[i].afterStatus == statusCuts[i + 1];
          assert observations[i + 1].firstStatus == statusCuts[i + 1];
        }
      }
    }
    reveal Spec.RunRelation();
  }

  lemma {:vcs_split_on_every_assert} RunSummaryImpliesSpec(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    firstStatus: nat,
    afterStatus: nat,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    exit: int, afterNative: seq<Native.State>
  )
    requires Core.RunSummary(cmd, fs, cwd, firstStatus, afterStatus,
                             output,errors,exit,afterNative)
    ensures Spec.RunRelation(cmd, fs, cwd, firstStatus, afterStatus,
                             output,errors,exit,afterNative)
  {
    hide *;
    reveal Core.RunSummary();
    var observations: seq<Spec.OperandObservation>,
        sorted: seq<Spec.OperandObservation>, groups: seq<Spec.OutputGroup>,
        statusCuts: seq<nat> :|
      Spec.RunNativeFields(cmd,fs,firstStatus,afterStatus,observations,afterNative) &&
      |observations| == |cmd.operands| &&
      |statusCuts| == |observations| + 1 &&
      statusCuts[0] == firstStatus &&
      statusCuts[|observations|] == afterStatus &&
      (forall i: nat | i < |observations| ::
         observations[i].firstStatus == statusCuts[i] &&
         observations[i].afterStatus == statusCuts[i + 1]) &&
      (forall i: nat | i < |observations| ::
         observations[i].index == i &&
         Core.OperandObservationSummary(cmd, fs, cwd, observations[i])) &&
      sorted == Core.SortOperandsCore(cmd, observations) &&
      groups == Core.OutputGroupsCore(cmd, sorted) &&
      output == Core.JoinOutputGroupsCore(groups) &&
      errors == Core.AccessErrorsCore(observations) +
      Core.SectionErrorsCore(sorted) &&
      exit == Spec.OperandExitSpec(observations);
    forall i: nat | i < |observations|
      ensures Spec.OperandObservationRelation(cmd, fs, cwd, observations[i])
    {
      OperandObservationSummaryImpliesSpec(cmd, fs, cwd, observations[i]);
    }
    SortOperandsCoreSatisfiesRelation(cmd, observations);
    OutputGroupsCoreSatisfiesRelation(cmd, sorted);
    JoinOutputGroupsCoreSatisfiesRelation(groups);
    OperandErrorsCoreSatisfiesRelation(observations, sorted);
    RunWitnessImpliesRelation(
      cmd, fs, cwd, firstStatus, afterStatus, output, errors, exit,
      observations,sorted,groups,statusCuts,afterNative);
  }

  twostate lemma PreparedSummaryImpliesPreparedSpec(
    raw: Schema.LsCmdRaw,
    io: BenchIO.IO,
    exit: int
  , plannedStdout: StreamWorld.Bytes, plannedStderr: StreamWorld.Bytes)
    requires Core.PreparedSummary(raw, io, exit, plannedStdout, plannedStderr)
    ensures Spec.PreparedSpec(raw, io, exit, plannedStdout, plannedStderr)
  {
    hide *;
    reveal Core.PreparedSummary(), Spec.PreparedSpec(), Spec.ObservedSpec();
    reveal NativeIO.Inputs(), NativeIO.State();
    var cmd := Schema.WithStatusObservations(
      Spec.EffectiveCommandSpec(raw, old(io.env()), old(io.now())),
      io.statusObservations(), old(io.statusCursor()), io.trustedNativeFailures(),old(io.dirHandles()),old(io.cwd()),[old(NativeIO.Inputs(io))],[old(NativeIO.State(io))]);
    if cmd.mode == Schema.ModeRun {
      var output: BenchWorld.Bytes, errors: BenchWorld.Bytes :|
        Core.RunSummary(cmd, old(io.fs()), old(io.cwd()),
                        old(io.statusCursor()), io.statusCursor(),
                        output,errors,exit,[NativeIO.State(io)]) &&
        plannedStdout == output &&
        plannedStderr == errors;
      RunSummaryImpliesSpec(cmd, old(io.fs()), old(io.cwd()),
                            old(io.statusCursor()), io.statusCursor(),
                            output,errors,exit,[NativeIO.State(io)]);
    }
  }

  twostate lemma CoreSummaryImpliesSpec(raw: Schema.LsCmdRaw, io: BenchIO.IO, exit: int)
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    var output: StreamWorld.Bytes, diagnostics: StreamWorld.Bytes, normalExit: int :|
      Core.PreparedSummary(raw, io, normalExit, output, diagnostics) &&
      Spec.EmissionFields(old(io.stdout()), old(io.stderr()), io.stdout(), io.stderr(),
                          io.trustedStreams(), output, diagnostics, normalExit, exit);
    PreparedSummaryImpliesPreparedSpec(raw, io, normalExit,
                                       output, diagnostics);
  }
}
