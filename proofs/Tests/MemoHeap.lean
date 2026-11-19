import SubtreeProofs.Rust.MemoHeapRefinement

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace MemoHeapTests

open SubtreeProofs.Rust LookupSource LookupSource.Heap verified_ordered_core

private def emptyWord : Cell := .node .word 0 []
private def witness : CommonEmbedding := ⟨.Empty, 77#u32⟩
private def entry : Cell := .node .entry 0 [emptyWord, emptyWord, .node .embedding 0 [emptyWord, .number 77]]
private def memory : Memory := [entry, .node .table 0 [], .number 12]
private def table : Cell := .node .table 1 [.owned 0, .owned 1]
private def native : MemoTable := .Entry ⟨.Empty, .Empty, witness⟩ .Empty

private theorem table_rep : Represents memory table (encodeTable native) :=
  .node (.cons (.owned rfl (.node (.cons (.node .nil) (.cons (.node .nil)
    (.cons (.node (.cons (.node .nil) (.cons (.number 77) .nil))) .nil)))))
    (.cons (.owned rfl (.node .nil)) .nil))

-- Both key borrows alias a field of the owned table. The result borrow also
-- points into that table, and its arbitrary score is preserved.
private theorem key_rep : Represents memory (.shared ⟨0, [0]⟩) (.reference (encodeWord .Empty)) :=
  .shared rfl (.node .nil)
private theorem result_rep : Represents memory (.shared ⟨0, [2]⟩) (.reference (encodeResult witness)) :=
  .shared rfl (.node (.cons (.node .nil) (.cons (.number 77) .nil)))

private def insertion := MemoSource.Heap.run MemoSource.Program.body 4 .insert
  [table, .shared ⟨0, [0]⟩, .shared ⟨0, [0]⟩, .shared ⟨0, [2]⟩] memory

private def viewInsert (value : Option (Cell × Memory × Cost)) : Option (Nat × Nat × Nat × Nat × Nat × Nat) :=
  match value with
  | some (.node .table 1 [.owned newEntry, .owned newTail], after, cost) =>
    match after[newTail]? with
    | some (.node .table 1 [.owned oldEntry, .owned oldTail]) =>
      some (newEntry, newTail, oldEntry, oldTail, after.length, cost.events.allocations)
    | _ => none
  | _ => none

example : viewInsert insertion = some (3, 4, 0, 1, 5, 2) := by decide +kernel

example : ∃ cell after cost, MemoSource.Heap.run MemoSource.Program.body 4 .insert
      [table, .shared ⟨0, [0]⟩, .shared ⟨0, [0]⟩, .shared ⟨0, [2]⟩] memory = some (cell, after, cost) ∧
    Typed after cell (.adt .table) := by
  obtain ⟨cell, after, cost, _, hr, _, ht, _⟩ :=
    MemoSource.Heap.insert_total native .Empty .Empty witness 4 (by decide +kernel) memory table
      ⟨0, [0]⟩ ⟨0, [0]⟩ ⟨0, [2]⟩ table_rep key_rep key_rep result_rep
  exact ⟨cell, after, cost, hr, ht⟩

private theorem table_footprint : Footprint memory table [0, 1] :=
  .node (.cons (.owned rfl (.node (.cons (.node .nil) (.cons (.node .nil)
    (.cons (.node (.cons (.node .nil) (.cons (.number 77) .nil))) .nil)))))
    (.cons (.owned rfl (.node .nil)) .nil))

private def packed := MemoSource.Heap.Layout.packInsert table .Empty .Empty witness memory

-- The complete returned ledger includes old cells, each exactly once.
example : Footprint packed.2 packed.1 [3, 0, 1, 4] :=
  MemoSource.Heap.Layout.packInsert_footprint table .Empty .Empty witness memory table_footprint

example : ¬Owns packed.2 packed.1 memory.length packed.2.length := by
  intro ho
  have hf : Footprint packed.2 packed.1 [3, 0, 1, 4] :=
    MemoSource.Heap.Layout.packInsert_footprint table .Empty .Empty witness memory table_footprint
  have hi := ((ho.exclusive hf).2.2 0).mp (by simp)
  change 3 ≤ 0 ∧ _ at hi
  omega

example : Spatial.Separated packed.2 [packed.1, .owned 2] := by
  apply MemoSource.Heap.Layout.packInsert_frame table .Empty .Empty witness memory [.owned 2]
  exact ⟨[0, 1, 2], .cons table_footprint (.cons (.owned rfl (.number 12)) .nil), by decide +kernel⟩

-- Insertion transfers every duplicate occurrence too; it cannot repair an
-- invalid aliased input owner by allocating a new entry and tail.
example (tc : Cell) (left right : BalancedWord) (result : CommonEmbedding) (before : Memory)
    {old : List Nat} (ht : Footprint before tc old) (hbad : ¬old.Nodup) :
    ¬Spatial.Separated (MemoSource.Heap.Layout.packInsert tc left right result before).2
      [(MemoSource.Heap.Layout.packInsert tc left right result before).1] := by
  obtain ⟨addresses, hp, hperm⟩ := MemoSource.Heap.Layout.packInsert_ledger tc left right result before ht
  intro hs
  have hn := hs.every_footprint (by simpa only [List.append_nil] using FieldsFootprint.cons hp FieldsFootprint.nil)
  exact hbad (List.nodup_append.mp (hperm.nodup_iff.mp hn)).1

private def pairMemory : Memory :=
  [.node .word 0 [], .node .word 0 [], .node .word 1 [.owned 0, .owned 1]]
private def viewWord (value : Option (Cell × Memory × Cost)) : Option (Nat × Nat × Nat × Nat) :=
  match value with
  | some (.node .word 1 [.owned head, .owned tail], after, cost) => some (head, tail, after.length, cost.events.allocations)
  | _ => none

-- Aliased input words are copied into a complete fresh append layout.
example : viewWord (MemoSource.Heap.run MemoSource.Program.body 5 .concatenate
    [.shared ⟨2, []⟩, .shared ⟨2, []⟩] pairMemory) = some (3, 6, 7, 4) := by decide +kernel

example : MemoSource.Heap.run MemoSource.Program.body 4 .insert
    [table, .shared ⟨20, []⟩, .shared ⟨0, [0]⟩, .shared ⟨0, [2]⟩] memory = none := rfl

example (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (memory : Memory) :
    ∃ tc pl pr pc after,
      Represents after tc (encodeTable table) ∧ Represents after (.shared pl) (.reference (encodeWord left)) ∧
      Represents after (.shared pr) (.reference (encodeWord right)) ∧
      Represents after (.shared pc) (.reference (encodeResult result)) ∧ Extends memory after ∧
      ∀ frame, Spatial.Separated memory frame → Spatial.Separated after (tc :: frame) :=
  MemoSource.Heap.insert_inputs_exist table left right result memory

end MemoHeapTests
