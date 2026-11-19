module

public import SubtreeProofs.Rust.SourceAnchoredLoanMachine

/-! Complete owner uniqueness separates the precise owned-word anchor from
every other owning local. Fresh word views therefore cannot borrow the owners
of a different selected local; original query-loan obligations stay separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem AnchoredLoanMachine.other_owners_avoid_anchor {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original fresh : List Nat} {source : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    {slot : Nat} {binding : Binding} (root : active.roots slot = some binding) (different : source ≠ slot)
    {item : Resources} (represented : LocalResources world active.frame active.roots active.state slot item) :
    List.Disjoint item.owners anchor.reads := by
  obtain ⟨remaining, _, inventory, _⟩ := active.context_complete h.native.valid slot
  have callerView := h.native.previousCallers.transport h.native.kept
  have frame := Activation.partition_owner_frame h.native.valid h.native.ownerFrame root represented inventory callerView
  have included : source ∈ remainingSlots active.count slot := by
    simp only [remainingSlots, List.mem_filter, List.mem_range]
    exact ⟨h.sourceBound, by simp [different]⟩
  obtain ⟨sourceResources, other, _, owners, _⟩ := inventory.get included
  have same := other.unique h.owning
  subst sourceResources
  have boxes : BoxOwners world item.owners := fun address member => frame.classified address (List.mem_append_left _ member)
  have unique : List.Disjoint item.owners anchor.owners := List.disjoint_left.mpr (by
    intro address first second
    exact List.disjoint_left.mp frame.unique.disjoint first (List.mem_append_left _ (owners second)))
  exact h.owning.closed_reads_avoid_owners (by rw [h.value]; exact ofValue_typed (word_typed word)) (.adt .word) boxes unique

end SubtreeProofs.Rust.SourceEval.Addressed
