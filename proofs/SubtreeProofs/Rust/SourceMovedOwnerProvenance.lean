module

public import SubtreeProofs.Rust.SourceAnchoredOwnerProvenance

/-! Actual owned projections transfer only owner occurrences from their source
local. Both the returned packet and the remaining source retain independently
established owner bounds, including partial Box shells and untouched siblings. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def CellOwnersAbove (bound : Nat) (memory : Memory) (cell : Cell) : Prop :=
  ∀ owners, Footprint memory cell owners → ∀ address ∈ owners, bound ≤ address

theorem CellOwnersAbove.of_footprint {bound : Nat} {memory : Memory} {cell : Cell} {owners : List Nat}
    (represented : Footprint memory cell owners) (above : ∀ address ∈ owners, bound ≤ address) :
    CellOwnersAbove bound memory cell := by
  intro actual actualRep address member
  rw [actualRep.unique represented] at member
  exact above address member

theorem move_owner_provenance {bound : Nat} {world : World} {active : Activation}
    {place : Place} {value : Value} {masks : State}
    (ha : active.Valid world) (run : active.state.move place = some (value, masks)) :
    ∃ moved owners,
      (∃ pointer, Storage.locate world active.roots place = some (moved, pointer)) ∧
      Footprint world.memory moved owners ∧
      (LocalOwnersAbove bound world active (splitPlace place).1 → ∀ address ∈ owners, bound ≤ address) ∧
      (∀ slot, LocalOwnersAbove bound world active slot → LocalOwnersAbove bound world {active with state := masks} slot) := by
  obtain ⟨_, guards, frame⟩ := ha
  obtain ⟨root, moved, owners, remaining, raw, projection, _, footprint, envAfter, partition⟩ := frame.ownerState.move run
  obtain ⟨resources, _, represented⟩ := frame.inspectSlot (splitPlace place).1
  have canonical := represented.source.ownerList
  have sourceAbove (above : LocalOwnersAbove bound world active (splitPlace place).1) :
      ∀ address ∈ ownerState world.memory (rawAt world active.roots) active.state (splitPlace place).1, bound ≤ address := by
    change ∀ address ∈ ownerList world.memory (rawAt world active.roots (splitPlace place).1) (active.state (splitPlace place).1), bound ≤ address
    rw [canonical]
    exact above resources represented
  refine ⟨moved, owners, Storage.locate_owned raw projection, footprint, ?_, ?_⟩
  · intro above address member
    exact sourceAbove above address (partition.symm.subset (List.mem_append_left _ member))
  · intro slot above actual actualRep address member
    have ownerEq := (actualRep.source.ownerList).symm.trans (envAfter slot).ownerList
    by_cases same : slot = (splitPlace place).1
    · subst slot
      rw [ownerEq] at member
      have remainingMember : address ∈ remaining := by
        simpa only [OwnerState.set, ite_true] using member
      exact sourceAbove above address (partition.symm.subset (List.mem_append_right _ remainingMember))
    · have oldMember : address ∈ ownerState world.memory (rawAt world active.roots) active.state slot := by
        rw [ownerEq] at member
        simpa only [OwnerState.set, same, ite_false] using member
      obtain ⟨old, _, oldRep⟩ := frame.inspectSlot slot
      exact above old oldRep address (oldRep.source.ownerList ▸ oldMember)

theorem operand_owner_provenance {bound : Nat} {world : World} {active : Activation} {guarded : List Nat}
    {op : Operand} {packet : ValueCell} {masks : State}
    (ha : active.Valid world)
    (run : operand world active.roots guarded active.state op = some (packet, masks)) :
    (∀ slot, LocalOwnersAbove bound world active slot → LocalOwnersAbove bound world {active with state := masks} slot) ∧
    ((∀ place, op = .move place → LocalOwnersAbove bound world active (splitPlace place).1) → CellOwnersAbove bound world.memory packet.1) := by
  cases op with
  | move place =>
    obtain ⟨pointer, source, located, _⟩ := operand_move_iff.mp run
    obtain ⟨moved, owners, ⟨target, location⟩, footprint, above, remaining⟩ := move_owner_provenance (bound := bound) ha source
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj (located.symm.trans location))
    exact ⟨remaining, fun selected => CellOwnersAbove.of_footprint footprint (above (selected place rfl))⟩
  | copy place =>
    simp only [operand, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨⟨cell, value⟩, pointer⟩, _, copied, copiedRun, run⟩ := run
    cases run
    exact ⟨fun _ above => above, fun _ => CellOwnersAbove.of_footprint (copyCell_owners copiedRun) (by simp)⟩
  | boolean b =>
    cases run
    exact ⟨fun _ above => above, fun _ => CellOwnersAbove.of_footprint (.boolean b) (by simp)⟩
  | number n =>
    simp only [operand] at run
    split at run
    next =>
      cases run
      exact ⟨fun _ above => above, fun _ => CellOwnersAbove.of_footprint (.number n) (by simp)⟩
    next => cases run

end SubtreeProofs.Rust.SourceEval.Addressed
