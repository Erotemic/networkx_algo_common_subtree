module

public import SubtreeProofs.Rust.MemoHeapInputs

/-! Successful native-input addressed memo primitives, independently typed
readback, exact source costs, fresh concatenation ownership and framed transfer
of insertion's existing owned table. Intermediate trace invariants remain open. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Heap

open LookupSource LookupSource.Heap verified_ordered_core

theorem concatenate_return_owns (left right : BalancedWord) (fuel : Nat)
    (hf : concatenateDepth left right ≤ fuel) (memory : Memory) (pl pr : Pointer)
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : run Program.body fuel .concatenate [.shared pl, .shared pr] memory = some (cell, after, cost)) :
    Owns after cell memory.length after.length := by
  obtain ⟨work, hs⟩ := Layout.concatenate_layout left right fuel hf memory pl pr hLeft hRight
  rw [hr] at hs
  cases hs
  exact packWord_owns (OrderedSolver.appendWord left right) memory

theorem insert_return_frame (table : Cell) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : insertDepth left right result ≤ fuel) (memory : Memory) (pl pr pc : Pointer)
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    (hResult : Represents memory (.shared pc) (.reference (encodeResult result)))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : run Program.body fuel .insert [table, .shared pl, .shared pr, .shared pc] memory = some (cell, after, cost)) :
    ∀ frame, Spatial.Separated memory (table :: frame) → Spatial.Separated after (cell :: frame) := by
  obtain ⟨work, hs⟩ := Layout.insert_layout table left right result fuel hf memory pl pr pc hLeft hRight hResult
  rw [hr] at hs
  cases hs
  exact Layout.packInsert_frame table left right result memory

/-- The last fresh Box contains exactly the input table cell, with the copied
entry in the other output field. Representation alone cannot establish this. -/
theorem insert_return_tail (table : Cell) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : insertDepth left right result ≤ fuel) (memory : Memory) (pl pr pc : Pointer)
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    (hResult : Represents memory (.shared pc) (.reference (encodeResult result)))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : run Program.body fuel .insert [table, .shared pl, .shared pr, .shared pc] memory = some (cell, after, cost)) :
    ∃ entry tail, cell = .node .table 1 [entry, .owned tail] ∧ after[tail]? = some table ∧ memory.length ≤ tail := by
  obtain ⟨work, hs⟩ := Layout.insert_layout table left right result fuel hf memory pl pr pc hLeft hRight hResult
  rw [hr] at hs
  cases hs
  have ht := Layout.packInsert_tail table left right result memory
  exact ⟨_, _, ht.1, ht.2, (Layout.entryLayout_owns left right result memory).bounds⟩

theorem concatenate_total (left right : BalancedWord) (fuel : Nat) (hf : concatenateDepth left right ≤ fuel)
    (memory : Memory) (pl pr : Pointer)
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ cell after cost,
      sourceRun Certificate.original.body fuel .concatenate [.reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeWord (OrderedSolver.appendWord left right), cost) ∧
      run Program.body fuel .concatenate [.shared pl, .shared pr] memory = some (cell, after, cost) ∧
      Represents after cell (encodeWord (OrderedSolver.appendWord left right)) ∧ Typed after cell (.adt .word) ∧
      Owns after cell memory.length after.length ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧ cost.events = concatenateEvents left right ∧
      verified_ordered_core.concatenate left right = .ok (OrderedSolver.appendWord left right) ∧
      ∀ frame, Spatial.Separated memory frame → Spatial.Separated after (cell :: frame) := by
  obtain ⟨cost, hr, hn, he⟩ := concatenate_checked left right fuel hf
  obtain ⟨cell, after, hrun, hv, hext, hlen⟩ := certified_run_spec fuel .concatenate memory _ _ _ cost
    (.cons hLeft (.cons hRight .nil)) hr
  have ho := concatenate_return_owns left right fuel hf memory pl pr hLeft hRight hrun
  exact ⟨cell, after, cost, hr, hrun, hv, hv.typed (word_typed _), ho, hext, hlen, he, hn,
    fun _ hs => Spatial.fresh_owns hext ho hs⟩

theorem insert_total (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : insertDepth left right result ≤ fuel) (memory : Memory) (tc : Cell) (pl pr pc : Pointer)
    (hTable : Represents memory tc (encodeTable table))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    (hResult : Represents memory (.shared pc) (.reference (encodeResult result))) :
    ∃ cell after cost,
      sourceRun Certificate.original.body fuel .insert
          [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)] =
        some (encodeTable (.Entry ⟨left, right, result⟩ table), cost) ∧
      run Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory = some (cell, after, cost) ∧
      Represents after cell (encodeTable (.Entry ⟨left, right, result⟩ table)) ∧ Typed after cell (.adt .table) ∧
      Extends memory after ∧ after.length = memory.length + cost.events.allocations ∧
      cost.events = insertEvents left right result ∧
      verified_ordered_core.memo_insert table left right result = .ok (.Entry ⟨left, right, result⟩ table) ∧
      (∃ entry tail, cell = .node .table 1 [entry, .owned tail] ∧ after[tail]? = some tc ∧ memory.length ≤ tail) ∧
      ∀ frame, Spatial.Separated memory (tc :: frame) → Spatial.Separated after (cell :: frame) := by
  obtain ⟨cost, hr, hn, he⟩ := insert_checked table left right result fuel hf
  obtain ⟨cell, after, hrun, hv, hext, hlen⟩ := certified_run_spec fuel .insert memory _ _ _ cost
    (.cons hTable (.cons hLeft (.cons hRight (.cons hResult .nil)))) hr
  exact ⟨cell, after, cost, hr, hrun, hv, hv.typed (table_typed _), hext, hlen, he, hn,
    insert_return_tail tc left right result fuel hf memory pl pr pc hLeft hRight hResult hrun,
    insert_return_frame tc left right result fuel hf memory pl pr pc hLeft hRight hResult hrun⟩

/-- Every old owner occurrence is transferred once, and every newly allocated
cell occurs once in addition. The permutation retains multiplicities. -/
theorem insert_return_ledger (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : insertDepth left right result ≤ fuel) (memory : Memory) (tc : Cell) (pl pr pc : Pointer)
    (hTable : Represents memory tc (encodeTable table))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    (hResult : Represents memory (.shared pc) (.reference (encodeResult result)))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : run Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory = some (cell, after, cost))
    {old : List Nat} (ht : Footprint memory tc old) :
    ∃ addresses, Footprint after cell addresses ∧
      addresses.Perm (old ++ List.range' memory.length (after.length - memory.length)) ∧
      addresses.length = old.length + cost.events.allocations ∧ (old.Nodup → addresses.Nodup) := by
  obtain ⟨value, mem, work, _, hs, _, _, hext, hlen, _⟩ :=
    insert_total table left right result fuel hf memory tc pl pr pc hTable hLeft hRight hResult
  rw [hr] at hs
  cases hs
  obtain ⟨reference, hshape⟩ := Layout.insert_layout tc left right result fuel hf memory pl pr pc hLeft hRight hResult
  rw [hr] at hshape
  cases hshape
  obtain ⟨addresses, hp, hperm⟩ := Layout.packInsert_ledger tc left right result memory ht
  refine ⟨addresses, hp, hperm, ?_, ?_⟩
  · have hl := hperm.length_eq
    simp only [List.length_append, List.length_range'] at hl
    omega
  · intro hn
    have hsep : Spatial.Separated memory [tc] :=
      ⟨old, by simpa only [List.append_nil] using FieldsFootprint.cons ht FieldsFootprint.nil, hn⟩
    have hout := Layout.packInsert_frame tc left right result memory [] hsep
    apply hout.every_footprint
    simpa only [List.append_nil] using FieldsFootprint.cons hp FieldsFootprint.nil

end SubtreeProofs.Rust.MemoSource.Heap
