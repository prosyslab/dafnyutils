include "../../core/World.dfy"
include "LsSchema.dfy"
include "LsSpec.dfy"
include "LsCore.dfy"

module LsProof {
  import BenchIO
  import BenchWorld
  import IOContract
  import Schema = LsSchema
  import Spec = LsSpec
  import Core = LsCore

  lemma DigitCharBridge(d: nat)
    requires d < 10
    ensures Core.DigitCharCore(d) == Spec.DigitChar(d)
  {
  }

  lemma NatTextBridge(n: nat)
    ensures Core.NatTextCore(n) == Spec.NatTextSpec(n)
    decreases n
  {
    if n >= 10 {
      NatTextBridge(n / 10);
      DigitCharBridge(n % 10);
    } else {
      DigitCharBridge(n);
    }
  }

  lemma IntTextBridge(n: int)
    ensures Core.IntTextCore(n) == Spec.IntTextSpec(n)
  {
    if n < 0 {
      NatTextBridge((-n) as nat);
    } else {
      NatTextBridge(n as nat);
    }
  }

  lemma PermissionCharBridge(mode: bv32, bit: bv32, present: char)
    ensures Core.PermissionCharCore(mode, bit, present) ==
            Spec.PermissionCharSpec(mode, bit, present)
  {
  }

  lemma KindCharBridge(kind: BenchWorld.FileKind)
    ensures Core.KindCharCore(kind) == Spec.KindCharSpec(kind)
  {
    match kind
    case RegularKind =>
    case DirectoryKind =>
    case SymlinkKind =>
    case BlockDeviceKind =>
    case CharacterDeviceKind =>
    case FifoKind =>
    case SocketKind =>
  }

  lemma ExecuteCharBridge(
    mode: bv32,
    executeBit: bv32,
    specialBit: bv32,
    specialExecute: char,
    specialNoExecute: char
  )
    ensures Core.ExecuteCharCore(
              mode, executeBit, specialBit, specialExecute, specialNoExecute) ==
            Spec.ExecuteCharSpec(
              mode, executeBit, specialBit, specialExecute, specialNoExecute)
  {
    PermissionCharBridge(mode, executeBit, 'x');
  }

  lemma SelectedTimeBridge(cmd: Schema.LsCmd, status: BenchWorld.FileStatus)
    ensures Core.SelectedSecondsCore(cmd, status) ==
            Spec.SelectedSecondsSpec(cmd, status)
    ensures Core.SelectedNanosecondsCore(cmd, status) ==
            Spec.SelectedNanosecondsSpec(cmd, status)
  {
    match cmd.timeField
    case ModificationTime =>
    case AccessTime =>
    case ChangeTime =>
  }

  lemma ModeTextBridge(status: BenchWorld.FileStatus)
    ensures Core.ModeTextCore(status) == Spec.ModeTextSpec(status)
  {
    KindCharBridge(status.kind);
    PermissionCharBridge(status.mode, 256 as bv32, 'r');
    PermissionCharBridge(status.mode, 128 as bv32, 'w');
    ExecuteCharBridge(status.mode, 64 as bv32, 2048 as bv32, 's', 'S');
    PermissionCharBridge(status.mode, 32 as bv32, 'r');
    PermissionCharBridge(status.mode, 16 as bv32, 'w');
    ExecuteCharBridge(status.mode, 8 as bv32, 1024 as bv32, 's', 'S');
    PermissionCharBridge(status.mode, 4 as bv32, 'r');
    PermissionCharBridge(status.mode, 2 as bv32, 'w');
    ExecuteCharBridge(status.mode, 1 as bv32, 512 as bv32, 't', 'T');
  }

  lemma RenderEntryBridge(
    cmd: Schema.LsCmd,
    displayName: string,
    status: BenchWorld.FileStatus
  )
    ensures Core.RenderEntryCore(cmd, displayName, status) ==
            Spec.RenderEntrySpec(cmd, displayName, status)
  {
    if cmd.showBlocks {
      NatTextBridge(Spec.DisplayedBlocksSpec(
                      status.storage.allocatedBlocks, cmd.cliBlockSize));
    }
    if cmd.numericLong {
      ModeTextBridge(status);
      NatTextBridge(status.linkCount);
      NatTextBridge(status.ownership.uid);
      NatTextBridge(status.ownership.gid);
      NatTextBridge(Spec.DisplayedFileSizeSpec(
                      status.storage.size, cmd.fileSizeBlockSize));
      SelectedTimeBridge(cmd, status);
      IntTextBridge(Core.SelectedSecondsCore(cmd, status));
      IntTextBridge(Core.SelectedNanosecondsCore(cmd, status));
    }
  }

  lemma AllocatedBlocksSumBridge(observations: seq<Spec.EntryObservation>)
    ensures Core.AllocatedBlocksSumCore(observations) ==
            Spec.AllocatedBlocksSumSpec(observations)
    decreases |observations|
  {
    if |observations| > 0 {
      AllocatedBlocksSumBridge(observations[1..]);
    }
  }

  lemma TotalLineBridge(cmd: Schema.LsCmd, observations: seq<Spec.EntryObservation>)
    ensures Core.TotalLineCore(cmd, observations) == Spec.TotalLineSpec(cmd, observations)
  {
    if cmd.numericLong || cmd.showBlocks {
      AllocatedBlocksSumBridge(observations);
      NatTextBridge(Spec.DisplayedBlocksSpec(
                      Core.AllocatedBlocksSumCore(observations), cmd.cliBlockSize));
    }
  }

  // Core keeps its index recursion, so the bridge carries the suffix
  // generalisation the structural specification needs.
  lemma StringLessFromBridge(left: string, right: string, i: nat)
    requires i <= |left| && i <= |right|
    ensures Core.StringLessFromCore(left, right, i) ==
            Spec.StringLessSpec(left[i..], right[i..])
    decreases |left| - i
  {
    reveal Core.StringLessFromCore();
    reveal Spec.StringLessSpec();
    if i < |left| && i < |right| {
      assert left[i..][0] == left[i];
      assert right[i..][0] == right[i];
      assert left[i..][1..] == left[i + 1..];
      assert right[i..][1..] == right[i + 1..];
      if left[i] == right[i] {
        StringLessFromBridge(left, right, i + 1);
      }
    }
  }

  lemma StringLessBridge(left: string, right: string)
    ensures Core.StringLessFromCore(left, right, 0) ==
            Spec.StringLessSpec(left, right)
  {
    StringLessFromBridge(left, right, 0);
  }

  lemma EntryBeforeBridge(
    cmd: Schema.LsCmd,
    left: Spec.EntryObservation,
    right: Spec.EntryObservation
  )
    ensures Core.EntryBeforeCore(cmd, left, right) ==
            Spec.EntryBeforeSpec(cmd, left, right)
  {
    reveal Core.EntryBeforeCore();
    reveal Spec.EntryBeforeSpec();
    reveal Core.BaseEntryBeforeCore();
    reveal Spec.BaseEntryBeforeSpec();
    reveal Core.StringLessCore();
    reveal Spec.StringLessSpec();
    StringLessBridge(left.displayName, right.displayName);
    StringLessBridge(right.displayName, left.displayName);
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
      EntryBeforeBridge(cmd, entry, sorted[0]);
      if !Core.EntryBeforeCore(cmd, entry, sorted[0]) {
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
      EntryBeforeBridge(cmd, entry, sorted[0]);
      if Core.EntryBeforeCore(cmd, entry, sorted[0]) {
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

  lemma OperandBeforeBridge(
    cmd: Schema.LsCmd,
    left: Spec.OperandObservation,
    right: Spec.OperandObservation
  )
    ensures Core.OperandBeforeCore(cmd, left, right) ==
            Spec.OperandBeforeSpec(cmd, left, right)
  {
    reveal Core.OperandBeforeCore();
    reveal Spec.OperandBeforeSpec();
    if left.operandClass == right.operandClass {
      EntryBeforeBridge(cmd, Spec.OperandAsEntry(left), Spec.OperandAsEntry(right));
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
      if !Core.OperandBeforeCore(cmd, observation, sorted[0]) {
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
      OperandBeforeBridge(cmd, observation, sorted[0]);
      if Core.OperandBeforeCore(cmd, observation, sorted[0]) {
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
    sorted: seq<Spec.OperandObservation>, positions: seq<nat>, processed: nat
  ) returns (cuts: seq<nat>)
    requires processed <= |positions|
    requires forall k: nat :: k < |positions| ==> positions[k] < |sorted|
    ensures Spec.FragmentsConcatenate(
              Core.BodiesFragmentsPrefixCore(sorted, positions, processed),
              Core.BodiesAtPositionsPrefixCore(sorted, positions, processed), cuts)
    decreases processed
  {
    if processed == 0 {
      cuts := [0];
    } else {
      cuts := BodiesAtPositionsConcatenate(sorted, positions, processed - 1);
      var fragments := Core.BodiesFragmentsPrefixCore(
        sorted, positions, processed - 1);
      var combined := Core.BodiesAtPositionsPrefixCore(
        sorted, positions, processed - 1);
      Core.AppendFragment(
        fragments, combined, cuts, sorted[positions[processed - 1]].body);
      cuts := cuts + [|Core.BodiesAtPositionsPrefixCore(
                        sorted, positions, processed)|];
      assert Core.BodiesFragmentsPrefixCore(sorted, positions, processed) ==
             fragments + [sorted[positions[processed - 1]].body];
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
    sorted: seq<Spec.OperandObservation>
  )
    ensures Spec.OutputGroupsRelation(sorted, Core.OutputGroupsCore(sorted))
  {
    var directPositions := Core.DirectPositionsCore(sorted, 0);
    var directoryPositions := Core.DirectoryPositionsCore(sorted, 0);
    DirectPositionsCoreSuffix(sorted, 0);
    DirectoryPositionsCoreSuffix(sorted, 0);
    assert Spec.DirectPositionRelation(sorted, directPositions);
    assert Spec.DirectoryPositionRelation(sorted, directoryPositions);
    var directFragments := Core.BodiesFragmentsPrefixCore(
      sorted, directPositions, |directPositions|);
    var directIndices := Core.OperandIndicesPrefixCore(
      sorted, directPositions, |directPositions|);
    var directBody := Core.BodiesAtPositionsCore(sorted, directPositions);
    var directCuts := BodiesAtPositionsConcatenate(
      sorted, directPositions, |directPositions|);
    DirectoryGroupsCoreShape(
      sorted, directoryPositions, |directoryPositions|);
    assert Spec.FragmentsConcatenate(directFragments, directBody, directCuts);
    assert |directIndices| == |directPositions|;
    assert |directFragments| == |directPositions|;
    var groups := Core.OutputGroupsCore(sorted);
    var offset := if |directPositions| == 0 then 0 else 1;
    assert |groups| == |directoryPositions| + offset;
    if |directPositions| > 0 {
      assert groups[0] == Spec.OutputGroup(directIndices, directBody, false);
    }
    forall k: nat | k < |directoryPositions|
      ensures groups[k + offset] == Spec.OutputGroup(
                                      [sorted[directoryPositions[k]].index],
                                      sorted[directoryPositions[k]].body, true)
    {
      if offset == 0 {
        assert groups == Core.DirectoryGroupsCore(sorted, directoryPositions);
      } else {
        assert groups == [Spec.OutputGroup(directIndices, directBody, false)] +
                         Core.DirectoryGroupsCore(sorted, directoryPositions);
      }
    }
    assert Spec.OutputGroupsWitnessRelation(
        sorted, groups, directPositions, directoryPositions, directIndices,
        directFragments, directCuts, directBody) by {
      reveal Spec.OutputGroupsWitnessRelation();
    }
    assert Spec.OutputGroupsRelation(sorted, groups) by {
      reveal Spec.OutputGroupsRelation();
    }
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
      cuts := cuts + [|Core.JoinOutputGroupsPrefixCore(groups, processed)|];
      assert Core.GroupFragmentsPrefixCore(groups, processed) == fragments + [tail];
    }
  }

  lemma JoinOutputGroupsCoreSatisfiesRelation(groups: seq<Spec.OutputGroup>)
    ensures Spec.SeparatedGroupsRelation(
              groups, Core.JoinOutputGroupsCore(groups))
  {
    var cuts := JoinOutputGroupsConcatenate(groups, |groups|);
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
    reveal Spec.OperandErrorsRelation();
  }

  lemma ObservationPiecesImpliesSpec(
    cmd: Schema.LsCmd,
    observations: seq<Spec.EntryObservation>,
    outputFragments: seq<BenchWorld.Bytes>,
    errorFragments: seq<BenchWorld.Bytes>
  )
    requires Core.ObservationPiecesSummary(
               cmd, observations, outputFragments, errorFragments)
    ensures Spec.ObservationPiecesRelation(
              cmd, observations, outputFragments, errorFragments)
  {
    forall i: nat | i < |observations|
      ensures outputFragments[i] ==
              (if observations[i].ok
               then Spec.RenderEntrySpec(cmd, observations[i].renderName, observations[i].status)
               else [])
    {
      if observations[i].ok {
        RenderEntryBridge(cmd, observations[i].renderName, observations[i].status);
      }
    }
  }

  lemma DirectorySummaryImpliesSpec(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    path: BenchWorld.Path,
    observations: seq<Spec.EntryObservation>,
    readErr: int,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    hadError: bool
  )
    requires Core.DirectoryListingSummary(
               cmd, fs, path, observations, readErr, output, errors, hadError)
    ensures Spec.DirectoryListingRelation(
              cmd, fs, path, observations, readErr, output, errors, hadError)
  {
    var rawObservations: seq<Spec.EntryObservation>,
        outputFragments: seq<BenchWorld.Bytes>, outputCuts: seq<nat>,
        errorFragments: seq<BenchWorld.Bytes>, errorCuts: seq<nat>,
        entryOutput: BenchWorld.Bytes, entryErrors: BenchWorld.Bytes :|
      Spec.DirectoryObservationRelation(cmd, fs, path, readErr == 0, rawObservations) &&
      observations == Core.SortEntriesCore(cmd, rawObservations) &&
      Core.ObservationPiecesSummary(cmd, observations, outputFragments, errorFragments) &&
      Spec.FragmentsConcatenate(outputFragments, entryOutput, outputCuts) &&
      output == Core.TotalLineCore(cmd, rawObservations) + entryOutput &&
      Spec.FragmentsConcatenate(errorFragments, entryErrors, errorCuts) &&
      errors == entryErrors +
      (if readErr == 0 then [] else Spec.ReadDirectoryErrorMessageSpec(path, readErr)) &&
      (readErr != 0 ==> hadError);
    SortEntriesCoreSatisfiesRelation(cmd, rawObservations);
    TotalLineBridge(cmd, rawObservations);
    ObservationPiecesImpliesSpec(cmd, observations, outputFragments, errorFragments);
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

  lemma RecursiveSummaryImpliesSpec(
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
    DirectorySummaryImpliesSpec(
      cmd, fs, accessPath, tree.observations, tree.readErr,
      tree.listingOutput, tree.listingErrors, tree.listingHadError);
    forall i: nat | i in tree.children
      ensures Spec.RecursiveDirectoryRelation(
                cmd, fs,
                Spec.ChildDisplayPath(displayPath, tree.observations[i].displayName),
                tree.observations[i].accessPath,
                ancestors + {tree.observations[i].status.hostKey}, tree.children[i])
    {
      RecursiveSummaryImpliesSpec(
        cmd, fs,
        Spec.ChildDisplayPath(displayPath, tree.observations[i].displayName),
        tree.observations[i].accessPath,
        ancestors + {tree.observations[i].status.hostKey}, tree.children[i]);
    }
    var outputCuts := RecursiveOutputPrefixConcatenates(
      tree, |tree.observations|);
    var errorCuts := RecursiveErrorPrefixConcatenates(
      displayPath, tree, |tree.observations|);
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
        tree.output == displayPath + ":\n" + tree.listingOutput + childOutput &&
        tree.errors == tree.listingErrors + childErrors;
  }

  lemma OperandObservationSummaryImpliesSpec(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    observation: Spec.OperandObservation
  )
    requires Core.OperandObservationSummary(cmd, fs, cwd, observation)
    ensures Spec.OperandObservationRelation(cmd, fs, cwd, observation)
  {
    reveal Core.OperandObservationSummary();
    reveal Spec.OperandObservationRelation();
    match Spec.OperandStatusResultSpec(cmd, fs, observation.path)
    case Err(_) =>
    case Ok(status) =>
      if status.kind == BenchWorld.DirectoryKind && !cmd.listDirectories {
        if observation.sectionAvailable {
          if cmd.recursive {
            var tree: Spec.RecursiveWitness :|
              Core.RecursiveDirectorySummary(
                cmd, fs, observation.operand, observation.path,
                {status.hostKey}, tree) &&
              observation.body == tree.output &&
              observation.sectionErrors == tree.errors &&
              observation.failed == tree.hadError;
            RecursiveSummaryImpliesSpec(
              cmd, fs, observation.operand, observation.path,
              {status.hostKey}, tree);
          } else {
            var entries: seq<Spec.EntryObservation>, readErr: int,
                listingOutput: BenchWorld.Bytes :|
              Core.DirectoryListingSummary(
                cmd, fs, observation.path, entries, readErr,
                listingOutput, observation.sectionErrors, observation.failed) &&
              observation.body ==
              (if |cmd.operands| > 1
               then observation.operand + ":\n"
               else []) + listingOutput;
            DirectorySummaryImpliesSpec(
              cmd, fs, observation.path, entries, readErr,
              listingOutput, observation.sectionErrors, observation.failed);
          }
        }
      } else {
        RenderEntryBridge(
          cmd,
          Spec.RenderNameSpec(
            fs, observation.operand, observation.path,
            Spec.ExplicitCommandLineFollowSpec(cmd), cmd.numericLong, status),
          status);
      }
  }

  lemma {:vcs_split_on_every_assert} RunSummaryImpliesSpec(
    cmd: Schema.LsCmd,
    fs: BenchWorld.FileSystem,
    cwd: BenchWorld.Path,
    output: BenchWorld.Bytes,
    errors: BenchWorld.Bytes,
    exit: int
  )
    requires Core.RunSummary(cmd, fs, cwd, output, errors, exit)
    ensures Spec.RunRelation(cmd, fs, cwd, output, errors, exit)
  {
    var observations: seq<Spec.OperandObservation>,
        sorted: seq<Spec.OperandObservation>, groups: seq<Spec.OutputGroup> :|
      |observations| == |cmd.operands| &&
      (forall i: nat | i < |observations| ::
         observations[i].index == i &&
         Core.OperandObservationSummary(cmd, fs, cwd, observations[i])) &&
      sorted == Core.SortOperandsCore(cmd, observations) &&
      groups == Core.OutputGroupsCore(sorted) &&
      output == Core.JoinOutputGroupsCore(groups) &&
      errors == Core.AccessErrorsCore(observations) +
      Core.SectionErrorsCore(sorted) &&
      exit == (if exists i: nat ::
                    i < |observations| && observations[i].failed then 2 else 0);
    forall i: nat | i < |observations|
      ensures Spec.OperandObservationRelation(cmd, fs, cwd, observations[i])
    {
      OperandObservationSummaryImpliesSpec(cmd, fs, cwd, observations[i]);
    }
    SortOperandsCoreSatisfiesRelation(cmd, observations);
    OutputGroupsCoreSatisfiesRelation(sorted);
    JoinOutputGroupsCoreSatisfiesRelation(groups);
    OperandErrorsCoreSatisfiesRelation(observations, sorted);
  }

  twostate lemma CoreSummaryImpliesSpec(
    raw: Schema.LsCmdRaw,
    io: BenchIO.IO,
    exit: int
  )
    requires Core.CoreSummary(raw, io, exit)
    ensures Spec.Spec(raw, io, exit)
  {
    reveal Core.CoreSummary();
    var cmd := Spec.EffectiveCommandSpec(raw, old(io.env()), old(io.now()));
    if cmd.mode == Schema.ModeRun {
      var output: BenchWorld.Bytes, errors: BenchWorld.Bytes :|
        Core.RunSummary(cmd, old(io.fs()), old(io.cwd()), output, errors, exit) &&
        io.stdout() == old(io.stdout()) + output &&
        io.stderr() == old(io.stderr()) + errors;
      RunSummaryImpliesSpec(cmd, old(io.fs()), old(io.cwd()), output, errors, exit);
    }
  }
}
