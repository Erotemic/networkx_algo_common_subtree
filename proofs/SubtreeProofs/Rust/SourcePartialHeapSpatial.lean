module

public import SubtreeProofs.Rust.SourcePartialHeapMoves
public import SubtreeProofs.Rust.SourcePartialHeapDrop
public import SubtreeProofs.Rust.LookupSpatialOwnership

/-! Complete duplicate-free partial ownership with an arbitrary caller frame.
A move partitions ownership without changing addresses; logical destruction
retires only selected owners. Shared-loan protection is an additional premise. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open LookupSource.Heap

def Separated (memory : Memory) (cells : List Cell) (parts : List Slot) : Prop :=
  ∃ owners, FieldsRep memory cells parts owners ∧ owners.Nodup

theorem Separated.of_full {memory : Memory} {cells : List Cell} {values : List Value}
    (hr : RepresentsFields memory cells values) (hs : Spatial.Separated memory cells) :
    Separated memory cells (ofFields values) := by
  obtain ⟨owners, hf, hn⟩ := hs
  exact ⟨owners, FieldsRep.of_full hr hf, hn⟩

theorem Separated.mono {before after : Memory} (he : Extends before after)
    {cells : List Cell} {parts : List Slot} (h : Separated before cells parts) : Separated after cells parts := by
  obtain ⟨owners, hr, hn⟩ := h
  exact ⟨owners, hr.mono he, hn⟩

theorem Separated.take {memory : Memory} {cell : Cell} {part after : Slot}
    {frame : List Cell} {masks : List Slot} (h : Separated memory (cell :: frame) (part :: masks))
    (path : List Projection) {value : Value} (ht : part.take path = some (value, after)) :
    ∃ moved, ownedProjection memory cell path = some moved ∧ Represents memory moved value ∧
      Separated memory (moved :: cell :: frame) (Slot.ofValue value :: after :: masks) := by
  obtain ⟨owners, hr, hn⟩ := h
  cases hr with
  | @cons _ _ _ _ first rest hv hf =>
    obtain ⟨moved, a, b, hm, hvalue, hfoot, hafter, hperm⟩ := hv.take path ht
    refine ⟨moved, hm, hvalue, a ++ (b ++ rest), .cons (Rep.of_full hvalue hfoot) (.cons hafter hf), ?_⟩
    simpa only [List.append_assoc] using (hperm.append_right rest).nodup_iff.mp hn

theorem Separated.drop {memory : Memory} {cell : Cell} {part : Slot}
    {frame : List Cell} {masks : List Slot} (h : Separated memory (cell :: frame) (part :: masks)) :
    Separated memory (cell :: frame) (.empty :: masks) := by
  obtain ⟨owners, hr, hn⟩ := h
  cases hr with
  | @cons _ _ _ _ first rest hv hf =>
    exact ⟨rest, .cons (.empty cell) hf, (List.nodup_append.mp hn).2.1⟩

theorem Separated.alloc {memory : Memory} {cell : Cell} {part : Slot} {frame : List Cell} {masks : List Slot}
    (h : Separated memory (cell :: frame) (part :: masks)) :
    Separated (Heap.alloc memory cell).2 ((Heap.alloc memory cell).1 :: frame) (.boxed part :: masks) := by
  obtain ⟨owners, hr, hn⟩ := h
  have hb := hr.bounds
  cases hr with
  | @cons _ _ _ _ first rest hv hf =>
    refine ⟨(first ++ [memory.length]) ++ rest,
      .cons hv.alloc (hf.mono (Extends.append memory [cell])), ?_⟩
    have hp : ((first ++ [memory.length]) ++ rest).Perm (memory.length :: (first ++ rest)) := by
      simpa only [List.append_assoc, List.singleton_append] using
        (List.perm_middle (a := memory.length) (l₁ := first) (l₂ := rest))
    apply hp.nodup_iff.mpr
    apply List.nodup_cons.mpr
    exact ⟨fun hm => Nat.lt_irrefl _ (hb _ hm), hn⟩


/-- The retained caller's owned addresses remain live. Shared pointers own no
addresses, so preserving loans requires the separate guarded-address premise. -/
theorem Separated.destroy_frame {memory : Memory} {cell : Cell} {part : Slot}
    {frame : List Cell} {masks : List Slot} {live : Live}
    (h : ∃ owners, FieldsRep memory (cell :: frame) (part :: masks) owners ∧ owners.Nodup ∧ AliveOn live owners) :
    ∃ discarded retained,
      destroy memory cell part = some (discarded, part.dropWork) ∧
      discarded.length = part.dropWork.boxes ∧ discarded.Nodup ∧
      FieldsRep memory frame masks retained ∧ retained.Nodup ∧
      AliveOn (retire live discarded) retained ∧
      (∀ address ∈ discarded, live address = true ∧ retire live discarded address = false) ∧
      ∀ address ∈ retained, address ∉ discarded := by
  obtain ⟨owners, hr, hn, hl⟩ := h
  cases hr with
  | @cons _ _ _ _ first rest hv hf =>
    have hd := List.nodup_append.mp hn
    have hfirst : AliveOn live first := fun address ha => hl address (List.mem_append_left _ ha)
    have hrest : AliveOn live rest := fun address ha => hl address (List.mem_append_right _ ha)
    have hs : ∀ address ∈ rest, address ∉ first := by
      intro address ha hb
      exact hd.2.2 address hb address ha rfl
    exact ⟨first, rest, hv.destroy, hv.boxes, hd.1, hf, hd.2.1, retire_preserves hs hrest,
      fun address ha => ⟨hfirst address ha, retire_member live ha⟩, hs⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
