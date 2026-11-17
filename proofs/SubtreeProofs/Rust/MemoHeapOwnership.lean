module

public import SubtreeProofs.Rust.MemoHeapInsertion

/-! Fresh copied entry ownership and explicit transfer of an existing table.
These are returned-value/frame theorems, separate from intermediate local
ownership/storage/loan traces. Complete occurrence lists retain duplicate owners. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Spatial

theorem fresh_owns {before after : Memory} {cell : Cell} {frame : List Cell}
    (he : Extends before after) (ho : Owns after cell before.length after.length)
    (hf : Separated before frame) : Separated after (cell :: frame) := by
  obtain ⟨addresses, ha, hn⟩ := hf
  have hx := ho.exclusive ho.footprint
  refine ⟨List.range' before.length (after.length - before.length) ++ addresses,
    .cons ho.footprint (fieldsFootprint_mono he ha), ?_⟩
  apply List.nodup_append.mpr
  refine ⟨hx.2.1, hn, ?_⟩
  intro address hnew other hold heq
  subst other
  have hl := (hx.2.2 address).mp hnew
  have hr := fieldsFootprint_bounds ha address hold
  omega

end SubtreeProofs.Rust.LookupSource.Heap.Spatial

namespace SubtreeProofs.Rust.MemoSource.Heap.Layout

open LookupSource LookupSource.Heap verified_ordered_core

/-- Copying an entry owns precisely the fresh key/witness intervals. -/
theorem packEntry_owns (entry : MemoEntry) (memory : Memory) :
    Owns (packEntry entry memory).2 (packEntry entry memory).1 memory.length (packEntry entry memory).2.length := by
  have hl := packWord_owns entry.left memory
  have hr := packWord_owns entry.right (packWord entry.left memory).2
  have hc := packResult_owns entry.result (packWord entry.right (packWord entry.left memory).2).2
  have heR := (packWord_spec entry.right (packWord entry.left memory).2).2
  have heC := (packResult_spec entry.result (packWord entry.right (packWord entry.left memory).2).2).2
  exact .node (.cons (hl.mono (heR.trans heC)) (.cons (hr.mono heC) (.cons hc (.nil _))))

def entryLayout (left right : BalancedWord) (result : CommonEmbedding) (memory : Memory) : Cell × Memory :=
  alloc (packEntry ⟨left, right, result⟩ memory).2 (packEntry ⟨left, right, result⟩ memory).1

theorem entryLayout_owns (left right : BalancedWord) (result : CommonEmbedding) (memory : Memory) :
    Owns (entryLayout left right result memory).2 (entryLayout left right result memory).1 memory.length
      (entryLayout left right result memory).2.length :=
  alloc_owns (packEntry_owns ⟨left, right, result⟩ memory)

theorem entryLayout_extends (left right : BalancedWord) (result : CommonEmbedding) (memory : Memory) :
    Extends memory (entryLayout left right result memory).2 :=
  (packEntry_spec ⟨left, right, result⟩ memory).2.trans (Extends.append _ [_])

theorem packInsert_tail (table : Cell) (left right : BalancedWord) (result : CommonEmbedding) (memory : Memory) :
    (packInsert table left right result memory).1 =
        .node .table 1 [(entryLayout left right result memory).1,
          .owned (entryLayout left right result memory).2.length] ∧
    (packInsert table left right result memory).2[(entryLayout left right result memory).2.length]? = some table := by
  constructor
  · rfl
  · simp [packInsert, entryLayout, alloc]

theorem packInsert_frame (table : Cell) (left right : BalancedWord) (result : CommonEmbedding) (memory : Memory)
    (frame : List Cell) (hf : Spatial.Separated memory (table :: frame)) :
    Spatial.Separated (packInsert table left right result memory).2
      ((packInsert table left right result memory).1 :: frame) := by
  have hs := Spatial.fresh_owns (entryLayout_extends left right result memory)
    (entryLayout_owns left right result memory) hf
  have ht := hs.perm (List.Perm.swap _ _ _)
  have htail := Spatial.Separated.alloc ht
  have horder := htail.perm (List.Perm.swap _ _ _)
  exact Spatial.Separated.pack (fields := [(entryLayout left right result memory).1,
    (alloc (entryLayout left right result memory).2 table).1]) horder

/-- The occurrence list contains the fresh copied entry, the original table's
complete old occurrence list, then its fresh tail Box. No set erases aliases. -/
theorem packInsert_footprint (table : Cell) (left right : BalancedWord) (result : CommonEmbedding) (memory : Memory)
    {old : List Nat} (ht : Footprint memory table old) :
    Footprint (packInsert table left right result memory).2 (packInsert table left right result memory).1
      (List.range' memory.length ((entryLayout left right result memory).2.length - memory.length) ++
        (old ++ [(entryLayout left right result memory).2.length])) := by
  have he := Extends.append (entryLayout left right result memory).2 [table]
  have hp := Spatial.footprint_mono he (entryLayout_owns left right result memory).footprint
  have htable := Spatial.footprint_mono ((entryLayout_extends left right result memory).trans he) ht
  have htail : Footprint (alloc (entryLayout left right result memory).2 table).2
      (alloc (entryLayout left right result memory).2 table).1 (old ++ [(entryLayout left right result memory).2.length]) :=
    .owned (alloc_fresh _ _).2.1 htable
  cases h : packEntry ⟨left, right, result⟩ memory with
  | mk ec em =>
    simpa [packInsert, entryLayout, alloc, h] using
      Footprint.node (FieldsFootprint.cons hp (FieldsFootprint.cons htail .nil))

theorem packInsert_suffix (table : Cell) (left right : BalancedWord) (result : CommonEmbedding) (memory : Memory) :
    (packInsert table left right result memory).2 = (entryLayout left right result memory).2 ++ [table] := by
  cases h : packEntry ⟨left, right, result⟩ memory with
  | mk ec em => simp [packInsert, entryLayout, alloc, h]

theorem packInsert_ledger (table : Cell) (left right : BalancedWord) (result : CommonEmbedding) (memory : Memory)
    {old : List Nat} (ht : Footprint memory table old) :
    ∃ addresses, Footprint (packInsert table left right result memory).2 (packInsert table left right result memory).1 addresses ∧
      addresses.Perm (old ++ List.range' memory.length ((packInsert table left right result memory).2.length - memory.length)) := by
  have hf := packInsert_footprint table left right result memory ht
  refine ⟨_, hf, ?_⟩
  have hlo := (entryLayout_owns left right result memory).bounds
  have hrange : List.range' memory.length ((entryLayout left right result memory).2.length - memory.length) ++
      [(entryLayout left right result memory).2.length] =
      List.range' memory.length ((packInsert table left right result memory).2.length - memory.length) := by
    rw [packInsert_suffix, List.length_append, List.length_singleton]
    have hlen : (entryLayout left right result memory).2.length + 1 - memory.length =
        ((entryLayout left right result memory).2.length - memory.length) + 1 := by omega
    rw [hlen, List.range'_1_concat, Nat.add_sub_of_le hlo]
  have hp := List.perm_append_comm_assoc
    (List.range' memory.length ((entryLayout left right result memory).2.length - memory.length)) old
    [(entryLayout left right result memory).2.length]
  simpa only [List.append_assoc, hrange] using hp

end SubtreeProofs.Rust.MemoSource.Heap.Layout
