module

public import SubtreeProofs.Rust.SourceOriginalLoanMachine

/-! Checked owned drops preserve every untouched original loan. Freshness of
selected owned descendants supplies a sufficient semantic drop permission;
query/table aliases elsewhere in the machine remain allowed. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem drop_preserves_other_local {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) {slot other : Nat} (different : other ≠ slot) (bound : other < active.count)
    {r : Resources} (represented : LocalResources world active.frame active.roots active.state other r)
    (run : drop world active callers slot = some (final, after)) : Preserves world final r.reads := by
  simp only [drop, bind, Option.bind_eq_some_iff] at run
  obtain ⟨item, inspected, ⟨remainder, suspended⟩, contextScan, binding, root, run⟩ := run
  simp only [scanContext, bind, Option.bind_eq_some_iff] at contextScan
  obtain ⟨actualRemaining, remainingScan, actualSuspended, callerScan, sameContext⟩ := contextScan
  cases sameContext
  split at run
  next ready =>
    cases run
    obtain ⟨actual, scanned, remaining, _⟩ := active.context_complete ha slot
    have same := Option.some.inj (scanned.symm.trans remainingScan)
    subst actual
    obtain ⟨selected, selectedRep, included, _, _⟩ := remaining.get (slot := other)
      (by simp [remainingSlots, bound, different])
    have same := represented.unique selectedRep
    have kept := world.retire_keeps ready.2.2.2
    apply kept.preserves.weaken
    intro address member
    exact List.mem_append_left _ (included (same ▸ member))
  next => cases run

end SubtreeProofs.Rust.SourceEval.Addressed.Derived

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem OriginalLoanMachine.drop_fresh {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    {slot : Nat} {binding : Binding} (root : active.roots slot = some binding)
    (bounded : ∀ index ∈ exceptions, index < active.count)
    (freshOwners : ∀ item, LocalResources world active.frame active.roots active.state slot item →
      ∀ address ∈ item.owners, before.memory.length ≤ address) :
    ∃ discarded, Derived.drop world active callers slot =
        some (world.retire discarded, {active with state := active.state.set slot .empty}) ∧
      discarded.length = (active.state slot).dropWork.boxes ∧
      OriginalLoanMachine before callers previous external exceptions
        (world.retire discarded) {active with state := active.state.set slot .empty} := by
  have loans : Derived.DropLoansAllowed world active callers slot binding := by
    intro item remainder suspended represented remaining callerView
    apply List.disjoint_left.mpr
    intro address member forbidden
    have fresh : before.memory.length ≤ address := by
      rcases List.mem_cons.mp member with same | owned
      · subst address; exact h.native.fresh slot binding root
      · exact freshOwners item represented address owned
    rcases List.mem_append.mp forbidden with current | old
    · have below := Inventory.loans_below_family remaining h.closed h.origins address current
      omega
    · have below := h.native.previousCallers.preserved_read_bound h.native.beforeWellFormed h.native.kept callerView
        address (callerView.loans_subset_reads old)
      omega
  obtain ⟨discarded, run, _, length⟩ := Derived.drop_complete h.native.valid h.native.callersValid
    h.native.separate h.native.ownerFrame root loans
  have native := h.native.advance (act := .drop slot) run (h.native.safe.clear slot)
    h.native.separate h.native.memoryBound h.native.fresh
  refine ⟨discarded, run, length, native, h.closed.clear slot, ?_, ?_⟩
  · intro index member
    by_cases same : index = slot
    · subst index; simp only [Partial.Locals.set, ite_true, Slot.dropWork]
    · simpa only [Partial.Locals.set, same, ite_false] using h.zero index member
  · intro index member
    by_cases same : index = slot
    · subst index
      exact LoanOrigin.of_closed native.valid before.memory.length slot
        (by simpa only [Partial.Locals.set, ite_true] using SlotTyped.empty .u32) .u32
    · obtain ⟨r, represented, below⟩ := h.origins index member
      have kept := Derived.drop_preserves_other_local h.native.valid same (bounded index member) represented run
      exact ⟨r, (represented.transport kept).congr_at rfl
        (by simp only [Partial.Locals.set, same, ite_false]), below⟩

end SubtreeProofs.Rust.SourceEval.Addressed
