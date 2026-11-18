module

public import SubtreeProofs.Rust.SourceAnchoredLoanMachine

/-! Ended fresh views restore the original bounded-loan machine. Reference
families can shrink when removed members have independently closed masks;
physical stack retirement is a separate subsequent source operation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem AnchoredLoanMachine.to_original {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original fresh : List Nat} {source : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    (ended : ∀ slot ∈ fresh, ∃ ty, SlotTyped (active.state slot) ty ∧ Borrow.Closed ty) :
    OriginalLoanMachine before callers previous external original world active := by
  refine ⟨h.native, ?_, fun slot member => h.zero slot (List.mem_append_right fresh member), h.origins⟩
  intro slot outside
  by_cases member : slot ∈ fresh
  · exact ended slot member
  · exact h.closed slot (by simp only [List.mem_append, not_or]; exact ⟨member, outside⟩)

theorem OriginalLoanMachine.narrow {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original remaining : List Nat}
    (h : OriginalLoanMachine before callers previous external original world active)
    (included : ∀ slot ∈ remaining, slot ∈ original)
    (ended : ∀ slot ∈ original, slot ∉ remaining → ∃ ty, SlotTyped (active.state slot) ty ∧ Borrow.Closed ty) :
    OriginalLoanMachine before callers previous external remaining world active := by
  refine ⟨h.native, ?_, fun slot member => h.zero slot (included slot member), fun slot member => h.origins slot (included slot member)⟩
  intro slot outside
  by_cases member : slot ∈ original
  · exact ended slot member outside
  · exact h.closed slot member

end SubtreeProofs.Rust.SourceEval.Addressed
