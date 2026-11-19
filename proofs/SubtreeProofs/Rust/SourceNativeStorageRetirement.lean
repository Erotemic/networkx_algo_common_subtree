module

public import SubtreeProofs.Rust.SourceLoanSafeMachine

/-! Retire fresh native-reference storage after its logical view has ended.
Its retained raw pointer cell cannot belong to any current native loan; older
caller reads lie below the fresh callee roots. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem LoanSafeMachine.storageDead_reference {before world : World} {active : Activation}
    {callers : List Activation} {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} {pointer : Pointer} (hb : active.roots slot = some binding)
    (memory : world.memory[binding.address]? = some (.shared pointer))
    (zero : (active.state slot).dropWork.boxes = 0) :
    let final := world.retire [binding.address]
    let after : Activation := {active with roots := active.roots.set slot none, state := active.state.set slot .empty}
    Derived.storageDead world active callers slot = some (final, after) ∧
      LoanSafeMachine before callers previous external final after := by
  dsimp only
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := slot) h.safe memory (Or.inr ⟨pointer, rfl⟩)
    h.previousCallers h.beforeWellFormed h.kept (h.fresh slot binding hb)
  have run := Derived.storageDead_complete h.valid h.callersValid h.wellFormed h.separate h.ownerFrame hb zero loans
  refine ⟨run, h.advance (act := .storageDead slot) run (h.safe.clear slot) (h.separate.erase slot) h.memoryBound ?_⟩
  intro index target ht
  by_cases same : index = slot
  · subst index; simp only [Roots.set, ite_true, reduceCtorEq] at ht
  · exact h.fresh index target (by simpa only [Roots.set, same, ite_false] using ht)

theorem LoanSafeMachine.shared_root {before world : World} {active : Activation}
    {callers : List Activation} {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    {slot : Nat} {binding : Binding} {value : Value} (hb : active.roots slot = some binding)
    (initialized : active.state slot = .shared value) :
    ∃ pointer, world.memory[binding.address]? = some (.shared pointer) := by
  obtain ⟨_, frame⟩ := h.valid.2
  obtain ⟨cell, used, memory, _, graph, _⟩ := frame.get hb
  rw [initialized] at graph
  cases graph
  exact ⟨_, memory⟩

end SubtreeProofs.Rust.SourceEval.Addressed
