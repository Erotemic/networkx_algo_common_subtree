module

public import SubtreeProofs.Rust.SourceOwnedLoanAnchors

/-! Forward machines distinguish original bounded query loans from fresh loans
supported by one closed owning word local. Other stack roots remain available
for selected moves, stores and retirement while the word stays borrowed. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem Inventory.loans_below_or_supported {world : World} {active : Activation} {limit : Nat}
    {slots original fresh support : List Nat} {resources : Resources}
    (h : Inventory world active.frame active.roots active.state slots resources)
    (closed : ClosedOutside (fresh ++ original) active.state)
    (old : ∀ slot ∈ original, LoanOrigin world active limit slot)
    (supportedLoans : ∀ slot ∈ fresh, LoanSupport world active (· ∈ support) slot) :
    ∀ address ∈ resources.loans, address < limit ∨ address ∈ support := by
  induction h with
  | nil => simp
  | @cons slot slots head tail represented rest ih =>
    have first : ∀ address ∈ head.loans, address < limit ∨ address ∈ support := by
      intro address member
      by_cases originalSlot : slot ∈ original
      · exact Or.inl ((old slot originalSlot).bound represented address member)
      by_cases freshSlot : slot ∈ fresh
      · exact Or.inr ((supportedLoans slot freshSlot).allows represented address member)
      · obtain ⟨ty, typed, shape⟩ := closed slot (by simp [originalSlot, freshSlot])
        rw [represented.closed_loans typed shape] at member
        cases member
    intro address member
    rcases List.mem_append.mp member with one | more
    · exact first address one
    · exact ih address more

structure AnchoredLoanMachine (before : World) (callers : List Activation) (previous : Resources)
    (external original fresh : List Nat) (source : Nat) (word : BalancedWord) (anchor : Resources)
    (world : World) (active : Activation) : Prop where
  native : LoanSafeMachine before callers previous external world active
  closed : ClosedOutside (fresh ++ original) active.state
  zero : ∀ slot ∈ fresh ++ original, (active.state slot).dropWork.boxes = 0
  origins : ∀ slot ∈ original, LoanOrigin world active before.memory.length slot
  supportedLoans : ∀ slot ∈ fresh, LoanSupport world active (· ∈ anchor.reads) slot
  owning : LocalResources world active.frame active.roots active.state source anchor
  value : active.state source = Slot.ofValue (encodeWord word)
  sourceBound : source < active.count

namespace AnchoredLoanMachine

variable {before world : World} {active : Activation} {callers : List Activation} {previous : Resources}
  {external original fresh : List Nat} {source : Nat} {word : BalancedWord} {anchor : Resources}

theorem of_original (h : OriginalLoanMachine before callers previous external original world active)
    (owning : LocalResources world active.frame active.roots active.state source anchor)
    (value : active.state source = Slot.ofValue (encodeWord word)) (bound : source < active.count) :
    AnchoredLoanMachine before callers previous external original [] source word anchor world active :=
  ⟨h.native, h.closed, h.zero, h.origins, by simp, owning, value, bound⟩

theorem prepare (h : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    (code : Code) : AnchoredLoanMachine before callers previous external original fresh source word anchor world (active.forgetRefs code) := by
  have same : (active.forgetRefs code).state source = active.state source :=
    LoanEnding.forget_closed code _ (by rw [h.value]; exact ofValue_typed (word_typed word)) (.adt .word)
  refine ⟨h.native.prepare code, h.closed.forget code _, ?_, fun slot member => (h.origins slot member).prepare code,
    fun slot member => (h.supportedLoans slot member).prepare code, h.owning.congr_at rfl same, same.trans h.value, h.sourceBound⟩
  intro slot member
  rcases LoanEnding.forget_eq_or_empty code (List.range active.count) active.state slot with unchanged | empty
  · change (LoanEnding.forget code _ active.state slot).dropWork.boxes = 0
    rw [unchanged]; exact h.zero slot member
  · change (LoanEnding.forget code _ active.state slot).dropWork.boxes = 0
    rw [empty]; simp only [Slot.dropWork]

theorem anchor_avoids_root (h : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    {slot : Nat} {binding : Binding} (root : active.roots slot = some binding) (different : source ≠ slot) : binding.address ∉ anchor.reads := by
  apply h.owning.closed_reads_avoid_other_root h.native.valid
    (by rw [h.value]; exact ofValue_typed (word_typed word)) (.adt .word) _ root different
  exact fun address member => h.native.ownerFrame.classified address (List.mem_append_left _
    (h.owning.owners_subset_activation h.sourceBound member))

theorem current_root_unborrowed (h : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    {slot : Nat} {binding : Binding} (root : active.roots slot = some binding) (different : source ≠ slot)
    {slots : List Nat} {resources : Resources}
    (inventory : Inventory world active.frame active.roots active.state slots resources) : binding.address ∉ resources.loans := by
  intro member
  rcases Inventory.loans_below_or_supported inventory h.closed h.origins h.supportedLoans binding.address member with old | supportedLoans
  · have bound := h.native.fresh slot binding root
    omega
  · exact h.anchor_avoids_root root different supportedLoans

theorem rootLoans (h : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    {slot : Nat} {binding : Binding} (root : active.roots slot = some binding) (different : source ≠ slot) :
    Derived.RootLoansAllowed world active callers slot binding := by
  intro remainder suspended inventory callerView forbidden
  rcases List.mem_append.mp forbidden with current | old
  · exact h.current_root_unborrowed root different inventory current
  · have bound := h.native.previousCallers.preserved_read_bound h.native.beforeWellFormed h.native.kept callerView
      binding.address (callerView.loans_subset_reads old)
    have freshRoot := h.native.fresh slot binding root
    omega

theorem move_local (h : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    {slot : Nat} {binding : Binding} (root : active.roots slot = some binding) (different : source ≠ slot)
    {current suspended : Resources} (scanned : Scanned world active current) (callerView : Callers world callers suspended) :
    Allowed world active.roots (current.loans ++ suspended.reads) (.move (.local slot)) := by
  apply allowed_local_from_loans h.native.valid h.native.separate h.native.ownerFrame callerView root
  intro forbidden
  rcases List.mem_append.mp forbidden with current | old
  · exact h.current_root_unborrowed root different scanned.inventory current
  · have bound := h.native.previousCallers.preserved_read_bound h.native.beforeWellFormed h.native.kept callerView
      binding.address (callerView.loans_subset_reads old)
    have freshRoot := h.native.fresh slot binding root
    omega

end AnchoredLoanMachine
end SubtreeProofs.Rust.SourceEval.Addressed
