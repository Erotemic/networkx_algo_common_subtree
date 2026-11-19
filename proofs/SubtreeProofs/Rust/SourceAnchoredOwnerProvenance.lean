module

public import SubtreeProofs.Rust.SourceHelperOwnerProvenance
public import SubtreeProofs.Rust.SourceAnchoredLoanMachine

/-! Canonical local inventories retain descendant-owner provenance across
preparation and actual anchored-machine advances. The same anchor preserves
its owner identities while its supported shared-view family changes. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem LocalOwnersAbove.of_resource {bound : Nat} {world : World} {active : Activation} {slot : Nat} {resources : Resources}
    (represented : LocalResources world active.frame active.roots active.state slot resources)
    (above : ∀ address ∈ resources.owners, bound ≤ address) : LocalOwnersAbove bound world active slot := by
  intro actual actualRep address member
  rw [actualRep.unique represented] at member
  exact above address member

theorem LocalOwnersAbove.prepare {bound : Nat} {world : World} {active : Activation} {slot : Nat} {ty : Ty}
    (h : LocalOwnersAbove bound world active slot) (code : Code)
    (typed : SlotTyped (active.state slot) ty) (closed : Borrow.Closed ty) :
    LocalOwnersAbove bound world (active.forgetRefs code) slot := by
  have same := LoanEnding.forget_closed code (List.range active.count) typed closed
  intro resources represented address member
  exact h resources (represented.congr_at rfl same.symm) address member

theorem AnchoredLoanMachine.owner_provenance {before world final : World} {active after : Activation}
    {callers : List Activation} {previous : Resources} {external original nextOriginal fresh nextFresh : List Nat}
    {source bound : Nat} {word : BalancedWord} {anchor : Resources}
    (first : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    (last : AnchoredLoanMachine before callers previous external nextOriginal nextFresh source word anchor final after)
    (above : LocalOwnersAbove bound world active source) : LocalOwnersAbove bound final after source :=
  LocalOwnersAbove.of_resource last.owning (above anchor first.owning)

end SubtreeProofs.Rust.SourceEval.Addressed
