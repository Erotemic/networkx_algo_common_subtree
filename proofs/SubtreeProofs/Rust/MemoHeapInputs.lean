module

public import SubtreeProofs.Rust.MemoHeapOwnership

/-! Constructive represented inputs and owned-table frames for every native
memo primitive input. These are external input layouts, not free setup work
inside the source contracts. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Heap

open LookupSource LookupSource.Heap verified_ordered_core

theorem packTable_owns (table : MemoTable) (memory : Memory) :
    Owns (packTable table memory).2 (packTable table memory).1 memory.length (packTable table memory).2.length := by
  induction table generalizing memory with
  | Empty => exact .node (.nil _)
  | Entry entry rest ih =>
    have hh := Layout.packEntry_owns entry memory
    have ht := ih (alloc (packEntry entry memory).2 (packEntry entry memory).1).2
    have he := (packTable_spec rest (alloc (packEntry entry memory).2 (packEntry entry memory).1).2).2
    have hhead := (alloc_owns hh).mono
      (he.trans (Extends.append (packTable rest (alloc (packEntry entry memory).2 (packEntry entry memory).1).2).2
        [(packTable rest (alloc (packEntry entry memory).2 (packEntry entry memory).1).2).1]))
    exact .node (.cons hhead (.cons (alloc_owns ht) (.nil _)))

def sharedWord (word : BalancedWord) (memory : Memory) : Pointer × Memory :=
  let (cell, memory) := packWord word memory
  (⟨memory.length, []⟩, memory ++ [cell])

theorem sharedWord_spec (word : BalancedWord) (memory : Memory) :
    Represents (sharedWord word memory).2 (.shared (sharedWord word memory).1) (.reference (encodeWord word)) ∧
      Extends memory (sharedWord word memory).2 := by
  have hp := packWord_spec word memory
  have hs := shareRoot_spec hp.1
  exact ⟨hs.1, hp.2.trans hs.2⟩

def sharedResult (result : CommonEmbedding) (memory : Memory) : Pointer × Memory :=
  let (cell, memory) := packResult result memory
  (⟨memory.length, []⟩, memory ++ [cell])

theorem sharedResult_spec (result : CommonEmbedding) (memory : Memory) :
    Represents (sharedResult result memory).2 (.shared (sharedResult result memory).1) (.reference (encodeResult result)) ∧
      Extends memory (sharedResult result memory).2 := by
  have hp := packResult_spec result memory
  have hs := shareRoot_spec hp.1
  exact ⟨hs.1, hp.2.trans hs.2⟩

theorem concatenate_inputs_exist (left right : BalancedWord) (memory : Memory) :
    ∃ pl pr after, Represents after (.shared pl) (.reference (encodeWord left)) ∧
      Represents after (.shared pr) (.reference (encodeWord right)) ∧ Extends memory after := by
  have hl := sharedWord_spec left memory
  have hr := sharedWord_spec right (sharedWord left memory).2
  exact ⟨_, _, _, hl.1.mono hr.2, hr.1, hl.2.trans hr.2⟩

/-- Every native table has a duplicate-free owned input layout, with all old
external owner frames preserved while the shared inputs are materialized. -/
theorem insert_inputs_exist (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (memory : Memory) :
    ∃ tc pl pr pc after,
      Represents after tc (encodeTable table) ∧
      Represents after (.shared pl) (.reference (encodeWord left)) ∧
      Represents after (.shared pr) (.reference (encodeWord right)) ∧
      Represents after (.shared pc) (.reference (encodeResult result)) ∧ Extends memory after ∧
      ∀ frame, Spatial.Separated memory frame → Spatial.Separated after (tc :: frame) := by
  have ht := packTable_spec table memory
  have ho := packTable_owns table memory
  have hl := sharedWord_spec left (packTable table memory).2
  have hr := sharedWord_spec right (sharedWord left (packTable table memory).2).2
  have hc := sharedResult_spec result (sharedWord right (sharedWord left (packTable table memory).2).2).2
  have he := hl.2.trans (hr.2.trans hc.2)
  exact ⟨_, _, _, _, _, ht.1.mono he, hl.1.mono (hr.2.trans hc.2), hr.1.mono hc.2, hc.1,
    ht.2.trans he, fun _ hs => (Spatial.fresh_owns ht.2 ho hs).mono he⟩

end SubtreeProofs.Rust.MemoSource.Heap
